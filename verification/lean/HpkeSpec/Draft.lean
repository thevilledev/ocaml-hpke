import HpkeSpec.Bytes
import HpkeSpec.Registry
import HpkeSpec.Encoding

/-!
# `Draft_hpke_04`: the successor draft and its one-stage KDFs

Mirrors of `Draft_hpke_04` in `lib/hpke.ml`, the module for
draft-ietf-hpke-hpke-04 with the SHAKE KDFs of draft-ietf-hpke-pq-05
Section 5, and the specifications they implement:

* `Draft_hpke_04.Kdf`: its KDF registry, against the KDF tables of both drafts,
  and its HKDFs against RFC 9180's;
* `length_prefixed`, against `lengthPrefixed` (draft Section 5.1), with its
  65535-byte bound (Section 7.2.1);
* the input of `one_stage_schedule`, against `CombineSecrets_OneStage`, and
  its split into `key`, `base_nonce` and `exporter_secret`;
* the one-stage branch of `Rfc9180.export`, against `Context.Export_OneStage`;
* the dispatch of `setup_sender` and `setup_receiver`, as a table of results.

Proved: every one-stage input the library hands the KDF is the draft's; the
one-stage key schedule binds the PSK, the shared secret, the mode, the PSK
identifier and `info` unambiguously; the lengths it asks for never make
`I2OSP` raise; and an input over 65535 bytes is `Invalid_length`, never an
exception. The KDFs themselves are opaque.
-/

namespace Hpke
namespace Draft

/-! ## The KDF registry -/

/-- `Draft_hpke_04.Kdf.id`. -/
inductive KdfId where
  | hkdfSha256 | hkdfSha384 | hkdfSha512 | shake128 | shake256
  deriving DecidableEq, Repr, Inhabited

/-- `One_stage_kdf.id`. -/
inductive OneStage where
  | shake128 | shake256
  deriving DecidableEq, Repr, Inhabited

/-- `schedule_kdf`: how a context's KDF runs. -/
inductive Schedule where
  | twoStage (kdf : Hpke.KdfId)
  | oneStage (kdf : OneStage)
  deriving DecidableEq, Repr

namespace KdfId

def all : List KdfId := [hkdfSha256, hkdfSha384, hkdfSha512, shake128, shake256]

theorem mem_all (k : KdfId) : k ∈ all := by cases k <;> simp [all]

/-- Mirror of `Kdf.to_int`. -/
def toInt : KdfId → Int
  | hkdfSha256 => 0x0001 | hkdfSha384 => 0x0002 | hkdfSha512 => 0x0003
  | shake128 => 0x0010 | shake256 => 0x0011

/-- Mirror of `Kdf.of_int`. -/
def ofInt : Int → Except Err KdfId
  | 0x0001 => .ok hkdfSha256 | 0x0002 => .ok hkdfSha384 | 0x0003 => .ok hkdfSha512
  | 0x0010 => .ok shake128 | 0x0011 => .ok shake256
  | id => .error (.unsupportedAlgorithm id)

/-- Mirror of `Kdf.schedule`. -/
def schedule : KdfId → Schedule
  | hkdfSha256 => .twoStage .hkdfSha256
  | hkdfSha384 => .twoStage .hkdfSha384
  | hkdfSha512 => .twoStage .hkdfSha512
  | shake128 => .oneStage .shake128
  | shake256 => .oneStage .shake256

/-- Mirror of `One_stage_kdf.hash_size`. -/
def oneStageHashSize : OneStage → Nat
  | .shake128 => 32
  | .shake256 => 64

/-- Mirror of `Kdf.hash_size`. -/
def hashSize (k : KdfId) : Nat :=
  match k.schedule with
  | .twoStage kdf => kdf.hashSize
  | .oneStage kdf => oneStageHashSize kdf

/-- Mirror of `Kdf.two_stage`. -/
def twoStage (k : KdfId) : Option Hpke.KdfId :=
  match k.schedule with
  | .twoStage kdf => some kdf
  | .oneStage _ => none

end KdfId

/-- The KDF tables of draft-ietf-hpke-hpke-04 (Section 7.2) and
draft-ietf-hpke-pq-05 (Section 5): identifier, `Nh`, and whether the KDF is
two-stage. -/
def kdfTable : KdfId → Int × Nat × Bool
  | .hkdfSha256 => (0x0001, 32, true)
  | .hkdfSha384 => (0x0002, 48, true)
  | .hkdfSha512 => (0x0003, 64, true)
  | .shake128 => (0x0010, 32, false)
  | .shake256 => (0x0011, 64, false)

theorem kdf_matches_table (k : KdfId) :
    kdfTable k = (k.toInt, k.hashSize, k.twoStage.isSome) := by
  cases k <;> rfl

theorem KdfId.ofInt_toInt (k : KdfId) : KdfId.ofInt k.toInt = .ok k := by
  cases k <;> rfl

theorem KdfId.toInt_ofInt {n : Int} {k : KdfId} (h : KdfId.ofInt n = .ok k) :
    k.toInt = n := by
  unfold KdfId.ofInt at h
  split at h <;> first | (cases h; rfl) | cases h

theorem KdfId.ofInt_error {n : Int} (h : ∀ k : KdfId, k.toInt ≠ n) :
    KdfId.ofInt n = .error (.unsupportedAlgorithm n) := by
  unfold KdfId.ofInt
  split <;> first | rfl | (exfalso; first
    | exact h .hkdfSha256 rfl | exact h .hkdfSha384 rfl | exact h .hkdfSha512 rfl
    | exact h .shake128 rfl | exact h .shake256 rfl)

/-- The two-stage KDFs of the draft are RFC 9180's: the same identifier and
`Nh`, so a suite with one of them has the `suite_id` of the RFC 9180 suite. -/
theorem twoStage_is_rfc9180 (k : KdfId) (f : Hpke.KdfId) (h : k.twoStage = some f) :
    k.toInt = f.toInt ∧ k.hashSize = f.hashSize := by
  cases k <;> simp [KdfId.twoStage, KdfId.schedule] at h <;> subst h <;> decide

/-- Every identifier fits `I2OSP(·, 2)` and differs from every other. -/
theorem KdfId.toInt_range (k : KdfId) : 0 ≤ k.toInt ∧ k.toInt < 0x10000 := by
  cases k <;> decide

/-! ## `lengthPrefixed` -/

/-- Mirror of `Draft_hpke_04.length_prefixed`: the bound, then
`Util.i2osp2 (String.length value) ^ value`. `Util.i2osp2` raising, which the
bound rules out, would be caught as `Invalid_length` by the setup functions. -/
def lengthPrefixedMirror (value : Bytes) : Except Err Bytes :=
  if value.length > 0xffff then .error (.invalidLength "longer than 65535 bytes")
  else
    match i2osp2 value.length with
    | some l => .ok (l ++ value)
    | none => .error (.invalidLength "I2OSP(2)")

theorem lengthPrefixedMirror_ok {value : Bytes} (h : value.length ≤ 0xffff) :
    lengthPrefixedMirror value = .ok (lengthPrefixed value) := by
  unfold lengthPrefixedMirror
  rw [ite_eq_right (by omega), i2osp2_nat (by omega)]
  rfl

theorem lengthPrefixedMirror_error {value : Bytes} (h : 0xffff < value.length) :
    ∃ r, lengthPrefixedMirror value = .error (.invalidLength r) := by
  unfold lengthPrefixedMirror
  exact ⟨_, ite_eq_left h⟩

@[simp] theorem length_lengthPrefixed (x : Bytes) : (lengthPrefixed x).length = 2 + x.length := by
  simp [lengthPrefixed]

/-- `lengthPrefixed` is prefix-free: a string that starts with one determines
it, which is what lets a concatenation of them be parsed back. -/
theorem lengthPrefixed_append_injective {a b x y : Bytes} (ha : a.length < 0x10000)
    (hb : b.length < 0x10000) (h : lengthPrefixed a ++ x = lengthPrefixed b ++ y) :
    a = b ∧ x = y := by
  unfold lengthPrefixed at h
  simp only [List.append_assoc] at h
  have h2 := List.append_inj h (by simp)
  have hl : a.length = b.length := i2osp_injective (by simpa using ha) (by simpa using hb) h2.1
  exact List.append_inj h2.2 hl

/-! ## `CombineSecrets_OneStage` -/

/-- The PSK of the mode: none in Base mode, `(psk, psk_id)` in PSK mode. -/
abbrev PskInput := Option (Bytes × Bytes)

/-- The mode byte, PSK and identifier `one_stage_schedule` derives from its
`~psk` (draft Section 5: `mode_base = 0x00`, `mode_psk = 0x01`). -/
def modeParams : PskInput → Bytes × Bytes × Bytes
  | none => ([0], [], [])
  | some (psk, pskId) => ([1], psk, pskId)

/-- Mirror of `one_stage_schedule` up to the KDF call: the `labeled_ikm` it
hands `One_stage_kdf.derive` for `L = Nk + Nn + Nh`, or its error. The four
`length_prefixed` calls run in the OCaml order. -/
def oneStageInput (suiteId : Bytes) (psk : PskInput) (sharedSecret info : Bytes)
    (L : Nat) : Except Err Bytes := do
  let (mode, pskSecret, pskId) := modeParams psk
  let prefixedPsk ← lengthPrefixedMirror pskSecret
  let prefixedSecret ← lengthPrefixedMirror sharedSecret
  let prefixedPskId ← lengthPrefixedMirror pskId
  let prefixedInfo ← lengthPrefixedMirror info
  match labeledDeriveInput suiteId (ascii "secret") (mode ++ prefixedPskId ++ prefixedInfo)
      (prefixedPsk ++ prefixedSecret) L with
  | some input => pure input
  | none => throw (.invalidLength "I2OSP(2)")

/-- draft-ietf-hpke-hpke-04 Section 5.1:
```
def CombineSecrets_OneStage(mode, shared_secret, info, psk, psk_id):
  secrets = concat(
    lengthPrefixed(psk),
    lengthPrefixed(shared_secret)
  )
  context = concat(
    mode,
    lengthPrefixed(psk_id),
    lengthPrefixed(info)
  )

  secret = LabeledDerive(secrets, "secret", context, Nk + Nn + Nh)
```
up to the KDF call: the `labeled_ikm` of that `LabeledDerive`. -/
def combineSecretsInput (suiteId : Bytes) (mode : UInt8) (sharedSecret info psk pskId : Bytes)
    (L : Nat) : Bytes :=
  let secrets := lengthPrefixed psk ++ lengthPrefixed sharedSecret
  let context := [mode] ++ lengthPrefixed pskId ++ lengthPrefixed info
  labeledDeriveSpec suiteId secrets (ascii "secret") context L

/-- The mode byte and PSK of a `PskInput`, as the draft names them. -/
def modeByte (psk : PskInput) : UInt8 := match psk with | none => 0 | some _ => 1
def pskOf (psk : PskInput) : Bytes := match psk with | none => [] | some (s, _) => s
def pskIdOf (psk : PskInput) : Bytes := match psk with | none => [] | some (_, i) => i

/-- Every input of 65535 bytes or fewer, and every length the library asks for,
gives `CombineSecrets_OneStage`'s input exactly. -/
theorem oneStageInput_eq_spec (suiteId : Bytes) (psk : PskInput) (sharedSecret info : Bytes)
    (L : Nat) (hL : L < 0x10000) (hp : (pskOf psk).length ≤ 0xffff)
    (hs : sharedSecret.length ≤ 0xffff) (hi : (pskIdOf psk).length ≤ 0xffff)
    (hn : info.length ≤ 0xffff) :
    oneStageInput suiteId psk sharedSecret info L
      = .ok (combineSecretsInput suiteId (modeByte psk) sharedSecret info (pskOf psk)
          (pskIdOf psk) L) := by
  have hlabel : (ascii "secret").length < 0x10000 := by decide +kernel
  rcases psk with _ | ⟨s, i⟩ <;>
  simp only [pskOf, pskIdOf] at hp hi <;>
  simp [oneStageInput, modeParams, lengthPrefixedMirror_ok hp, lengthPrefixedMirror_ok hs,
    lengthPrefixedMirror_ok hi, lengthPrefixedMirror_ok hn,
    labeledDeriveInput_eq_spec _ _ _ _ hlabel (Int.natCast_nonneg L) (by omega),
    combineSecretsInput, modeByte, pskOf, pskIdOf, bind, Except.bind, pure, Except.pure]

/-- An input over 65535 bytes is `Invalid_length`, never an exception. -/
theorem oneStageInput_too_long (suiteId : Bytes) (psk : PskInput) (sharedSecret info : Bytes)
    (L : Nat) (h : 0xffff < (pskOf psk).length ∨ 0xffff < sharedSecret.length ∨
      0xffff < (pskIdOf psk).length ∨ 0xffff < info.length) :
    ∃ r, oneStageInput suiteId psk sharedSecret info L = .error (.invalidLength r) := by
  have hnil := lengthPrefixedMirror_ok (show ([] : Bytes).length ≤ 0xffff by decide)
  unfold oneStageInput
  rcases psk with _ | ⟨p, i⟩ <;> simp only [pskOf, pskIdOf, modeParams] at h ⊢
  · simp only [hnil, bind, Except.bind]
    by_cases h2 : 0xffff < sharedSecret.length
    · obtain ⟨r, hr⟩ := lengthPrefixedMirror_error h2
      exact ⟨r, by simp [hr]⟩
    · have h4 : 0xffff < info.length := by simp at h; omega
      obtain ⟨r, hr⟩ := lengthPrefixedMirror_error h4
      exact ⟨r, by simp [lengthPrefixedMirror_ok (show sharedSecret.length ≤ 0xffff by omega),
        hr]⟩
  · simp only [bind, Except.bind]
    by_cases h1 : 0xffff < p.length
    · obtain ⟨r, hr⟩ := lengthPrefixedMirror_error h1
      exact ⟨r, by simp [hr]⟩
    rw [lengthPrefixedMirror_ok (show p.length ≤ 0xffff by omega)]
    by_cases h2 : 0xffff < sharedSecret.length
    · obtain ⟨r, hr⟩ := lengthPrefixedMirror_error h2
      exact ⟨r, by simp [hr]⟩
    rw [lengthPrefixedMirror_ok (show sharedSecret.length ≤ 0xffff by omega)]
    by_cases h3 : 0xffff < i.length
    · obtain ⟨r, hr⟩ := lengthPrefixedMirror_error h3
      exact ⟨r, by simp [hr]⟩
    rw [lengthPrefixedMirror_ok (show i.length ≤ 0xffff by omega)]
    have h4 : 0xffff < info.length := by omega
    obtain ⟨r, hr⟩ := lengthPrefixedMirror_error h4
    exact ⟨r, by simp [hr]⟩

/-- **Binding.** Under one `suite_id` and length, the input of the one-stage
key schedule determines the mode, the PSK, the shared secret, the PSK
identifier and `info`: no two different sets of inputs reach the KDF as the
same string. -/
theorem combineSecretsInput_injective {s : Bytes} {L : Nat}
    {m₁ m₂ : UInt8} {x₁ x₂ i₁ i₂ p₁ p₂ d₁ d₂ : Bytes}
    (hx₁ : x₁.length < 0x10000) (hx₂ : x₂.length < 0x10000)
    (hi₁ : i₁.length < 0x10000) (hi₂ : i₂.length < 0x10000)
    (hp₁ : p₁.length < 0x10000) (hp₂ : p₂.length < 0x10000)
    (hd₁ : d₁.length < 0x10000) (hd₂ : d₂.length < 0x10000)
    (h : combineSecretsInput s m₁ x₁ i₁ p₁ d₁ L = combineSecretsInput s m₂ x₂ i₂ p₂ d₂ L) :
    m₁ = m₂ ∧ x₁ = x₂ ∧ i₁ = i₂ ∧ p₁ = p₂ ∧ d₁ = d₂ := by
  unfold combineSecretsInput labeledDeriveSpec at h
  simp only [List.append_assoc] at h
  obtain ⟨hp, h1⟩ := lengthPrefixed_append_injective hp₁ hp₂ h
  obtain ⟨hx, h2⟩ := lengthPrefixed_append_injective hx₁ hx₂ h1
  have h3 := List.append_cancel_left (List.append_cancel_left (List.append_cancel_left
    (List.append_cancel_left h2)))
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h3
  obtain ⟨hm, h4⟩ := h3
  obtain ⟨hd, h5⟩ := lengthPrefixed_append_injective hd₁ hd₂ h4
  have h6 : lengthPrefixed i₁ ++ [] = lengthPrefixed i₂ ++ [] := by simpa using h5
  obtain ⟨hi, _⟩ := lengthPrefixed_append_injective hi₁ hi₂ h6
  exact ⟨hm, hx, hi, hp, hd⟩

/-- In particular the Base and PSK modes never share a key schedule input. -/
theorem combineSecretsInput_mode_separation {s : Bytes} {L : Nat} {x₁ x₂ i₁ i₂ p₂ d₂ : Bytes}
    (hx₁ : x₁.length < 0x10000) (hx₂ : x₂.length < 0x10000)
    (hi₁ : i₁.length < 0x10000) (hi₂ : i₂.length < 0x10000)
    (hp₂ : p₂.length < 0x10000) (hd₂ : d₂.length < 0x10000) :
    combineSecretsInput s 0 x₁ i₁ [] [] L ≠ combineSecretsInput s 1 x₂ i₂ p₂ d₂ L := by
  intro h
  have := (combineSecretsInput_injective hx₁ hx₂ hi₁ hi₂ (by decide) hp₂ (by decide) hd₂ h).1
  exact absurd this (by decide)

/-! ## The split of `secret` and the lengths asked for -/

/-- `key_nonce_sizes`: `Nk` and `Nn`, zero for export-only (draft Section 7.3). -/
def keyNonceSizes : Option AeadId → Nat × Nat
  | some a => (a.keySize, a.nonceSize)
  | none => (0, 0)

/-- Mirror of the split in `one_stage_context`: `String.sub secret 0 Nk`,
`String.sub secret Nk Nn` and `String.sub secret (Nk + Nn) Nh`. -/
def split (nk nn nh : Nat) (secret : Bytes) : Bytes × Bytes × Bytes :=
  (secret.take nk, (secret.drop nk).take nn, (secret.drop (nk + nn)).take nh)

/-- The draft's `key = secret[:Nk]`, `base_nonce = secret[Nk:(Nk + Nn)]`,
`exporter_secret = secret[(Nk + Nn):]`: on a secret of `Nk + Nn + Nh` bytes
the split has those lengths and concatenates back to it. -/
theorem split_spec (nk nn nh : Nat) (secret : Bytes) (h : secret.length = nk + nn + nh) :
    let (k, n, e) := split nk nn nh secret
    k.length = nk ∧ n.length = nn ∧ e.length = nh ∧ k ++ n ++ e = secret ∧
      e = secret.drop (nk + nn) := by
  simp only [split]
  refine ⟨by simp; omega, by simp; omega, by simp; omega, ?_, ?_⟩
  · rw [List.take_of_length_le (l := secret.drop (nk + nn)) (by simp; omega),
      List.append_assoc, ← List.drop_drop]
    rw [List.take_append_drop, List.take_append_drop]
  · rw [List.take_of_length_le (by simp; omega)]

/-- The length a one-stage key schedule asks for, `Nk + Nn + Nh`, is at most
108, so `I2OSP(L, 2)` never raises. -/
theorem schedule_length_small (aead : Option AeadId) (k : OneStage) :
    (keyNonceSizes aead).1 + (keyNonceSizes aead).2 + KdfId.oneStageHashSize k ≤ 108 := by
  rcases aead with _ | a <;> cases k <;> (try cases a) <;> decide

/-! ## `Context.Export_OneStage` -/

/-- Mirror of the one-stage branch of `Rfc9180.export`, up to the KDF call:
the length check, then the input `Labeled_kdf.derive` hands the KDF. An
`Invalid_argument` would be `Internal_error`. -/
def exportInput (suiteId exporterSecret exporterContext : Bytes) (L : Int) : Except Err Bytes :=
  if L < 0 ∨ L > 0xffff then .error .exportLengthOutOfRange
  else
    match labeledDeriveInput suiteId (ascii "sec") exporterContext exporterSecret L with
    | some input => .ok input
    | none => .error (.internalError "I2OSP(2)")

/-- draft Section 5.3:
`Context.Export_OneStage(exporter_context, L) =
  LabeledDerive(self.exporter_secret, "sec", exporter_context, L)`. The
export is `Export_length_out_of_range` exactly outside `[0, 65535]`, and
never `Internal_error`. -/
theorem exportInput_spec (suiteId exporterSecret exporterContext : Bytes) (L : Int) :
    exportInput suiteId exporterSecret exporterContext L =
      if L < 0 ∨ L > 0xffff then .error .exportLengthOutOfRange
      else .ok (labeledDeriveSpec suiteId exporterSecret (ascii "sec") exporterContext L.toNat) := by
  unfold exportInput
  by_cases h : L < 0 ∨ L > 0xffff
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    have hlabel : (ascii "sec").length < 0x10000 := by decide +kernel
    rw [labeledDeriveInput_eq_spec _ _ _ _ hlabel (by omega) (by omega)]

/-! ## The setup functions -/

/-- The error class of a setup result, `none` for success. -/
def resultClass {α : Type} : Except Err α → Option ErrClass
  | .ok _ => none
  | .error e => some e.cls

/-- Mirror of `one_stage_sender` and `one_stage_receiver`: the key check, the
KEM operation (`kemResult`, `encap` or `decap`, which gives the shared secret),
then the key schedule, whose input is `oneStageInput`. -/
def oneStageSetup {α : Type} (suiteKem keyKem : KemId) (kemResult : Except Err (Bytes × α))
    (suiteId : Bytes) (psk : PskInput) (info : Bytes) (L : Nat) : Except Err (Bytes × α) := do
  if suiteKem ≠ keyKem then throw .keyMismatch
  let (sharedSecret, rest) ← kemResult
  let input ← oneStageInput suiteId psk sharedSecret info L
  pure (input, rest)

/-- Mirror of `setup_sender` and `setup_receiver`: an HKDF suite runs the RFC
9180 setup of its mode (`rfc`), a SHAKE suite `one_stage_setup`. -/
def setup {α β : Type} (kdf : KdfId) (rfc : Hpke.KdfId → Except Err β)
    (oneStage : OneStage → Except Err α) : Except Err (β ⊕ α) :=
  match kdf.schedule with
  | .twoStage f => (rfc f).map .inl
  | .oneStage k => (oneStage k).map .inr

/-- The documented contract of `Draft_hpke_04`'s setup functions:
`Key_mismatch` unless the suite and the key share one KEM; for a one-stage
KDF, `Invalid_length` if an input exceeds 65535 bytes; otherwise success, for
valid keys and a valid encapsulation. `long` says whether some input exceeds
65535 bytes. -/
def expectedClass (suiteKem keyKem : KemId) (kdf : KdfId) (long : Bool) : Option ErrClass :=
  if suiteKem ≠ keyKem then some .keyMismatch
  else if long ∧ kdf.twoStage.isNone then some .invalidLength
  else none

/-- `one_stage_setup` returns the class `expectedClass` predicts, for a KEM
operation that succeeds with a shared secret of at most 65535 bytes (every
KEM's is 64 or fewer). -/
theorem oneStageSetup_class {α : Type} (suiteKem keyKem : KemId) (sharedSecret : Bytes) (a : α)
    (hs : sharedSecret.length ≤ 0xffff) (suiteId : Bytes) (psk : PskInput) (info : Bytes)
    (L : Nat) (hL : L < 0x10000) (k : OneStage) (kdf : KdfId) (hk : kdf.schedule = .oneStage k) :
    resultClass (oneStageSetup suiteKem keyKem (.ok (sharedSecret, a)) suiteId psk info L)
      = expectedClass suiteKem keyKem kdf
          (decide (0xffff < (pskOf psk).length ∨ 0xffff < (pskIdOf psk).length ∨
            0xffff < info.length)) := by
  have hkn : kdf.twoStage.isNone = true := by simp [KdfId.twoStage, hk]
  unfold oneStageSetup expectedClass
  by_cases hm : suiteKem ≠ keyKem
  · simp [hm, resultClass, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, Err.cls]
  · simp only [hm, ite_false, bind, Except.bind]
    by_cases hl : 0xffff < (pskOf psk).length ∨ 0xffff < (pskIdOf psk).length ∨
        0xffff < info.length
    · obtain ⟨r, hr⟩ := oneStageInput_too_long suiteId psk sharedSecret info L (by omega)
      simp [hr, hl, hkn, resultClass, Err.cls]
    · rw [oneStageInput_eq_spec suiteId psk sharedSecret info L hL (by omega) hs (by omega)
        (by omega)]
      simp [hl, resultClass, pure, Except.pure]

end Draft
end Hpke
