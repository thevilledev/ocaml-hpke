import HpkeSpec.Bytes
import HpkeSpec.Registry

/-!
# Key schedule and setup contracts

The `Rfc9180` module of `lib/hpke.ml` from the key schedule to the setup
functions (lines 1015-1189), and the `Private.setup_*_with_ephemeral` entry
points (lines 1230-1249).

* `keySchedule` mirrors `Rfc9180.key_schedule` with `LabeledExtract` and
  `LabeledExpand` abstract (`LabeledKdf`); `Rfc.KeySchedule` transcribes
  RFC 9180 Section 5.1. Every typed mode passes `VerifyPSKInputs` and yields
  the RFC's `key`, `base_nonce` and `exporter_secret`, with sequence number 0.
* `setupSenderInner` and `setupReceiverInner` mirror `setup_*_inner` with
  `encap` and `decap` as parameters, as the OCaml passes `~encap`. They are
  generic in a monad `m`: the OCaml `encap` has effects (it draws randomness),
  and a theorem of the form `setupSenderInner ... = pure (.error e)` for every
  monad and every `encap` says that `encap` is never run, so no randomness is
  drawn.
* `expectedClass` is a computable table of the error class every setup
  returns for valid keys, proved to agree with the mirrors; `table` enumerates
  it for conformance tests.

Keys are abstracted to records carrying their `KemId` (`PubKey`, `PrivKey`):
the setup layer inspects nothing else. This file is independent of
`HpkeSpec.Kem`, which proves what `encap` and `decap` compute. What the table
theorems assume of them is explicit (`EncapSucceeds`, `DecapSucceeds`: valid
keys of one KEM and a valid encapsulation succeed); `HpkeSpec.Kem` also shows
that after these checks `decap` never fails with `Key_mismatch` or
`Unsupported_mode` (`decap_dh_not_caller_error`, `decap_mlkem_not_caller_error`).
-/

namespace Hpke
namespace Setup

/-! ## Abstract labeled KDF -/

/-- `Labeled_kdf.extract ~kdf ~suite_id` and `Labeled_kdf.expand ~kdf ~suite_id`
(lines 647-653): RFC 9180's `LabeledExtract(salt, label, ikm)` and
`LabeledExpand(prk, label, info, L)` for the suite's KDF and `suite_id`, as
opaque deterministic functions. -/
structure LabeledKdf where
  extract : KdfId → (suiteId salt label ikm : Bytes) → Bytes
  expand : KdfId → (suiteId prk label info : Bytes) → (length : Nat) → Bytes

/-! ## Suites (lines 605-643) -/

/-- `Suite.t`: the GADT's two constructors. -/
inductive Suite where
  | encryption (kem : KemId) (kdf : KdfId) (aead : AeadId)
  | exportOnly (kem : KemId) (kdf : KdfId)
  deriving DecidableEq, Repr

namespace Suite

/-- `Suite.kem` (lines 621-623). -/
def kem : Suite → KemId
  | encryption kem _ _ => kem
  | exportOnly kem _ => kem

/-- `Suite.kdf` (lines 625-627). -/
def kdf : Suite → KdfId
  | encryption _ kdf _ => kdf
  | exportOnly _ kdf => kdf

/-- `Suite.aead_id` (lines 631-633). -/
def aeadId : Suite → Int
  | encryption _ _ aead => aead.toInt
  | exportOnly _ _ => 0xffff

end Suite

/-- Mirror of `Labeled_kdf.suite_id` (lines 639-643). `Util.i2osp2` raises
outside `[0, 0xffff]`; every identifier is in range (`ids_in_range`). -/
def suiteId (suite : Suite) : Bytes :=
  ascii "HPKE" ++ i2osp suite.kem.toInt.toNat 2 ++ i2osp suite.kdf.toInt.toNat 2
    ++ i2osp suite.aeadId.toNat 2

/-! ## PSKs and modes (lines 592-603, 1019-1027) -/

/-- `Psk.t` with the invariant `Psk.create` establishes. `Psk.t` is abstract in
`hpke.mli` and `create` is its only constructor, so every OCaml value satisfies
it; here it is carried as proof fields. -/
structure Psk where
  secret : Bytes
  id : Bytes
  secret_length : 32 ≤ secret.length
  id_nonempty : id ≠ []

/-- Mirror of `Psk.create` (lines 595-600). -/
def Psk.create (secret id : Bytes) : Except Err Psk :=
  if h : secret.length < 32 then
    .error (.invalidPsk "the secret must contain at least 32 bytes")
  else if h' : id.length = 0 then
    .error (.invalidPsk "the identifier must not be empty")
  else
    .ok ⟨secret, id, by omega, fun hc => h' (by simp [hc])⟩

theorem Psk.create_ok_iff (secret id : Bytes) :
    (∃ p, Psk.create secret id = .ok p) ↔ 32 ≤ secret.length ∧ id ≠ [] := by
  unfold Psk.create
  constructor
  · rintro ⟨p, hp⟩
    split at hp
    · cases hp
    · split at hp
      · cases hp
      · rename_i h h'
        exact ⟨by omega, fun hc => h' (by simp [hc])⟩
  · rintro ⟨h1, h2⟩
    have h1' : ¬ secret.length < 32 := by omega
    have h2' : ¬ id.length = 0 := fun hc => h2 (List.eq_nil_of_length_eq_zero hc)
    simp [h1', h2']

theorem Psk.create_fields {secret id : Bytes} {p : Psk} (h : Psk.create secret id = .ok p) :
    p.secret = secret ∧ p.id = id := by
  unfold Psk.create at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; exact ⟨rfl, rfl⟩

/-- Every `Psk` is what `Psk.create` returns for its own fields. -/
theorem Psk.create_self (p : Psk) : Psk.create p.secret p.id = .ok p := by
  obtain ⟨q, hq⟩ := (Psk.create_ok_iff p.secret p.id).mpr ⟨p.secret_length, p.id_nonempty⟩
  obtain ⟨h1, h2⟩ := Psk.create_fields hq
  have : q = p := by cases q; cases p; simp_all
  rw [hq, this]

theorem Psk.secret_ne_nil (p : Psk) : p.secret ≠ [] := by
  intro h
  have := p.secret_length
  rw [h] at this
  simp at this

/-- `'key mode` (lines 1019-1023): a mode that needs a PSK or a sender key
carries it. `κ` is the half of the sender's static key a role holds. -/
inductive Mode (κ : Type) where
  | base
  | psk (psk : Psk)
  | auth (key : κ)
  | authPsk (key : κ) (psk : Psk)

/-- `sender_key` (lines 1025-1027). -/
def senderKey {κ : Type} : Mode κ → Option κ
  | .base | .psk _ => none
  | .auth key | .authPsk key _ => some key

namespace Mode

variable {κ κ' : Type}

/-- Replace the sender key, e.g. by its public half on the receiver side. -/
def map (f : κ → κ') : Mode κ → Mode κ'
  | base => base
  | psk p => psk p
  | auth key => auth (f key)
  | authPsk key p => authPsk (f key) p

/-- The mode with its key forgotten: what the key schedule sees. -/
def erase (m : Mode κ) : Mode Unit := m.map fun _ => ()

/-- The numeric mode, `0` to `3`, as in the table of `expectedClass`. -/
def num : Mode κ → Nat
  | base => 0
  | psk _ => 1
  | auth _ => 2
  | authPsk _ _ => 3

theorem erase_map (f : κ → κ') (m : Mode κ) : (m.map f).erase = m.erase := by
  cases m <;> rfl

theorem senderKey_map (f : κ → κ') (m : Mode κ) : senderKey (m.map f) = (senderKey m).map f := by
  cases m <;> rfl

theorem num_map (f : κ → κ') (m : Mode κ) : (m.map f).num = m.num := by
  cases m <;> rfl

theorem two_le_num_iff (m : Mode κ) : 2 ≤ m.num ↔ (senderKey m).isSome := by
  cases m <;> simp [num, senderKey]

theorem num_lt (m : Mode κ) : m.num < 4 := by
  cases m <;> simp [num]

end Mode

/-! ## The key schedule (lines 873-892, 1029-1089) -/

/-- `encryption_state` (lines 873-882). The OCaml keeps the AEAD key expanded,
`{Aead.id = aead; expanded = Aead.expand aead key}`, a function of `(aead, key)`;
the raw `key` stands for it. `busy` is the `Atomic.t`'s value. -/
structure EncryptionState where
  aead : AeadId
  key : Bytes
  baseNonce : Bytes
  exporterSecret : Bytes
  kdf : KdfId
  suiteId : Bytes
  sequence : Bytes
  busy : Bool
  deriving DecidableEq, Repr

/-- `export_state` (lines 884-888). -/
structure ExportState where
  exporterSecret : Bytes
  kdf : KdfId
  suiteId : Bytes
  deriving DecidableEq, Repr

/-- `_ context` (lines 890-892). -/
inductive Context where
  | encryption (state : EncryptionState)
  | exportOnly (state : ExportState)
  deriving DecidableEq, Repr

/-- The `match mode with` of `key_schedule` (lines 1038-1044): mode byte, PSK
and PSK identifier. -/
def modeParams {κ : Type} : Mode κ → Bytes × Bytes × Bytes
  | .base => ([0], [], [])
  | .psk psk => ([1], psk.secret, psk.id)
  | .auth _ => ([2], [], [])
  | .authPsk _ psk => ([3], psk.secret, psk.id)

/-- Mirror of `Rfc9180.key_schedule` (lines 1029-1089). -/
def keySchedule {κ : Type} (L : LabeledKdf) (suite : Suite) (mode : Mode κ)
    (sharedSecret info : Bytes) : Context :=
  let kdf := suite.kdf
  let sid := suiteId suite
  let params := modeParams mode
  let modeByte := params.1
  let psk := params.2.1
  let pskId := params.2.2
  let pskIdHash := L.extract kdf sid [] (ascii "psk_id_hash") pskId
  let infoHash := L.extract kdf sid [] (ascii "info_hash") info
  let keyScheduleContext := modeByte ++ pskIdHash ++ infoHash
  let secret := L.extract kdf sid sharedSecret (ascii "secret") psk
  let exporterSecret := L.expand kdf sid secret (ascii "exp") keyScheduleContext kdf.hashSize
  match suite with
  | .exportOnly _ _ => .exportOnly { exporterSecret, kdf, suiteId := sid }
  | .encryption _ _ aead =>
    let key := L.expand kdf sid secret (ascii "key") keyScheduleContext aead.keySize
    let baseNonce :=
      L.expand kdf sid secret (ascii "base_nonce") keyScheduleContext aead.nonceSize
    .encryption
      { aead, key, baseNonce, exporterSecret, kdf, suiteId := sid,
        sequence := replicateByte 12 0, busy := false }

/-! ## RFC 9180 Section 5.1, transcribed -/

namespace Rfc

/-- RFC 9180 Table 1. -/
def mode_base : UInt8 := 0x00
def mode_psk : UInt8 := 0x01
def mode_auth : UInt8 := 0x02
def mode_auth_psk : UInt8 := 0x03

def default_psk : Bytes := ascii ""
def default_psk_id : Bytes := ascii ""

/-- ```
def VerifyPSKInputs(mode, psk, psk_id):
  got_psk = (psk != default_psk)
  got_psk_id = (psk_id != default_psk_id)
  if got_psk != got_psk_id:
    raise Exception("Inconsistent PSK inputs")

  if got_psk and (mode in [mode_base, mode_auth]):
    raise Exception("PSK input provided when not needed")
  if (not got_psk) and (mode in [mode_psk, mode_auth_psk]):
    raise Exception("Missing required PSK input")
``` -/
def VerifyPSKInputs (mode : UInt8) (psk psk_id : Bytes) : Except String Unit := do
  let got_psk := psk != default_psk
  let got_psk_id := psk_id != default_psk_id
  if got_psk != got_psk_id then
    throw "Inconsistent PSK inputs"
  if got_psk && [mode_base, mode_auth].contains mode then
    throw "PSK input provided when not needed"
  if !got_psk && [mode_psk, mode_auth_psk].contains mode then
    throw "Missing required PSK input"

/-- The AEAD column of `suite_id`: the AEAD's identifier (Table 5), or the
export-only `0xFFFF`. -/
def aead_id : Option AeadId → Int
  | some aead => (aeadTable aead).1
  | none => exportOnlyAeadId

/-- `suite_id = concat("HPKE", I2OSP(kem_id, 2), I2OSP(kdf_id, 2),
I2OSP(aead_id, 2))`, from the registry tables. -/
def suite_id (kem : KemId) (kdf : KdfId) (aead : Option AeadId) : Bytes :=
  ascii "HPKE" ++ i2osp (kemTable kem).id.toNat 2 ++ i2osp (kdfTable kdf).1.toNat 2
    ++ i2osp (aead_id aead).toNat 2

/-- `Nk` and `Nn` of Table 5; not applicable (here `0`) to export-only
suites, whose `key` and `base_nonce` Section 5.3 lets an implementation skip. -/
def Nk : Option AeadId → Nat
  | some aead => (aeadTable aead).2.1
  | none => 0

def Nn : Option AeadId → Nat
  | some aead => (aeadTable aead).2.2.1
  | none => 0

/-- `Nh` of Table 3. -/
def Nh (kdf : KdfId) : Nat := (kdfTable kdf).2

/-- `Context<ROLE>(key, base_nonce, seq, exporter_secret)`. -/
structure Context where
  key : Bytes
  base_nonce : Bytes
  seq : Nat
  exporter_secret : Bytes
  deriving DecidableEq, Repr

/-- ```
def KeySchedule<ROLE>(mode, shared_secret, info, psk, psk_id):
  VerifyPSKInputs(mode, psk, psk_id)

  psk_id_hash = LabeledExtract("", "psk_id_hash", psk_id)
  info_hash = LabeledExtract("", "info_hash", info)
  key_schedule_context = concat(mode, psk_id_hash, info_hash)

  secret = LabeledExtract(shared_secret, "secret", psk)

  key = LabeledExpand(secret, "key", key_schedule_context, Nk)
  base_nonce = LabeledExpand(secret, "base_nonce",
                             key_schedule_context, Nn)
  exporter_secret = LabeledExpand(secret, "exp",
                                  key_schedule_context, Nh)

  return Context<ROLE>(key, base_nonce, 0, exporter_secret)
```
for the suite `(kem, kdf, aead)`, `aead = none` being export-only. -/
def KeySchedule (L : LabeledKdf) (kem : KemId) (kdf : KdfId) (aead : Option AeadId)
    (mode : UInt8) (shared_secret info psk psk_id : Bytes) : Except String Context := do
  VerifyPSKInputs mode psk psk_id
  let LabeledExtract := L.extract kdf (suite_id kem kdf aead)
  let LabeledExpand := L.expand kdf (suite_id kem kdf aead)
  let psk_id_hash := LabeledExtract (ascii "") (ascii "psk_id_hash") psk_id
  let info_hash := LabeledExtract (ascii "") (ascii "info_hash") info
  let key_schedule_context := [mode] ++ psk_id_hash ++ info_hash
  let secret := LabeledExtract shared_secret (ascii "secret") psk
  let key := LabeledExpand secret (ascii "key") key_schedule_context (Nk aead)
  let base_nonce := LabeledExpand secret (ascii "base_nonce") key_schedule_context (Nn aead)
  let exporter_secret := LabeledExpand secret (ascii "exp") key_schedule_context (Nh kdf)
  return { key, base_nonce, seq := 0, exporter_secret }

end Rfc

/-- The RFC mode value (Table 1) each typed mode denotes. -/
def Mode.rfcMode {κ : Type} : Mode κ → UInt8
  | .base => Rfc.mode_base
  | .psk _ => Rfc.mode_psk
  | .auth _ => Rfc.mode_auth
  | .authPsk _ _ => Rfc.mode_auth_psk

/-! ## The key schedule equals the RFC's -/

theorem ascii_empty : ascii "" = [] := by simp [ascii]

theorem modeParams_modeByte {κ : Type} (m : Mode κ) : (modeParams m).1 = [m.rfcMode] := by
  cases m <;> rfl

theorem rfcMode_num {κ : Type} (m : Mode κ) : m.rfcMode = UInt8.ofNat m.num := by
  cases m <;> rfl

@[simp] private theorem cons_bne_nil (x : UInt8) (xs : Bytes) : (x :: xs != ([] : Bytes)) = true :=
  rfl

@[simp] private theorem nil_bne_nil : (([] : Bytes) != []) = false := rfl

private theorem ne_nil_cons {l : Bytes} (h : l ≠ []) : ∃ x xs, l = x :: xs := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => exact ⟨x, xs, rfl⟩

/-- Every typed mode passes `VerifyPSKInputs` on the mode value, PSK and PSK
identifier the mirror derives from it. -/
theorem verifyPSKInputs_modeParams {κ : Type} (m : Mode κ) :
    Rfc.VerifyPSKInputs m.rfcMode (modeParams m).2.1 (modeParams m).2.2 = .ok () := by
  cases m with
  | base =>
    simp [Rfc.VerifyPSKInputs, modeParams, Mode.rfcMode, Rfc.default_psk, Rfc.default_psk_id,
      ascii_empty]
    rfl
  | auth _ =>
    simp [Rfc.VerifyPSKInputs, modeParams, Mode.rfcMode, Rfc.default_psk, Rfc.default_psk_id,
      ascii_empty]
    rfl
  | psk p =>
    obtain ⟨x, xs, hx⟩ := ne_nil_cons p.secret_ne_nil
    obtain ⟨y, ys, hy⟩ := ne_nil_cons p.id_nonempty
    simp [Rfc.VerifyPSKInputs, modeParams, Mode.rfcMode, hx, hy, Rfc.default_psk,
      Rfc.default_psk_id, ascii_empty, Rfc.mode_psk, Rfc.mode_base, Rfc.mode_auth,
      Rfc.mode_auth_psk]
    rfl
  | authPsk _ p =>
    obtain ⟨x, xs, hx⟩ := ne_nil_cons p.secret_ne_nil
    obtain ⟨y, ys, hy⟩ := ne_nil_cons p.id_nonempty
    simp [Rfc.VerifyPSKInputs, modeParams, Mode.rfcMode, hx, hy, Rfc.default_psk,
      Rfc.default_psk_id, ascii_empty, Rfc.mode_psk, Rfc.mode_base, Rfc.mode_auth,
      Rfc.mode_auth_psk]
    rfl

/-- Conversely, the typed modes are exactly the inputs `VerifyPSKInputs`
accepts: for each RFC mode, either no PSK and no identifier (Base, Auth) or
both (PSK, AuthPSK). (`Psk.create` further demands 32 bytes of secret, the
"at least 32 bytes of entropy" of RFC 9180 Section 5.1.2.) -/
theorem verifyPSKInputs_ok_iff (mode : UInt8) (hmode : mode.toNat < 4) (psk psk_id : Bytes) :
    Rfc.VerifyPSKInputs mode psk psk_id = .ok () ↔
      ((mode = Rfc.mode_base ∨ mode = Rfc.mode_auth) ∧ psk = [] ∧ psk_id = []) ∨
      ((mode = Rfc.mode_psk ∨ mode = Rfc.mode_auth_psk) ∧ psk ≠ [] ∧ psk_id ≠ []) := by
  have hm : mode = 0 ∨ mode = 1 ∨ mode = 2 ∨ mode = 3 := by
    have : mode.toNat = 0 ∨ mode.toNat = 1 ∨ mode.toNat = 2 ∨ mode.toNat = 3 := by omega
    rcases this with h | h | h | h
    · exact .inl (UInt8.toNat_inj.mp h)
    · exact .inr (.inl (UInt8.toNat_inj.mp h))
    · exact .inr (.inr (.inl (UInt8.toNat_inj.mp h)))
    · exact .inr (.inr (.inr (UInt8.toNat_inj.mp h)))
  rcases hm with rfl | rfl | rfl | rfl <;>
  cases psk <;> cases psk_id <;>
  simp [Rfc.VerifyPSKInputs, Rfc.default_psk, Rfc.default_psk_id, ascii_empty,
    Rfc.mode_psk, Rfc.mode_base, Rfc.mode_auth, Rfc.mode_auth_psk, throw, throwThe,
    MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]

theorem keyScheduleContext_eq {κ : Type} (m : Mode κ) (a b : Bytes) :
    (modeParams m).1 ++ a ++ b = [m.rfcMode] ++ a ++ b := by
  rw [modeParams_modeByte]

theorem suiteId_encryption (kem : KemId) (kdf : KdfId) (aead : AeadId) :
    suiteId (.encryption kem kdf aead) = Rfc.suite_id kem kdf (some aead) := by
  cases kem <;> cases kdf <;> cases aead <;> rfl

theorem suiteId_exportOnly (kem : KemId) (kdf : KdfId) :
    suiteId (.exportOnly kem kdf) = Rfc.suite_id kem kdf none := by
  cases kem <;> cases kdf <;> rfl

theorem hashSize_eq_Nh (kdf : KdfId) : kdf.hashSize = Rfc.Nh kdf := by cases kdf <;> rfl

/-- The initial sequence number: twelve zero bytes, `I2OSP(0, Nn)`. -/
theorem initial_sequence (aead : AeadId) :
    replicateByte 12 0 = i2osp 0 aead.nonceSize ∧ os2ip (replicateByte 12 0) = 0 ∧
      (replicateByte 12 0).length = aead.nonceSize := by
  refine ⟨?_, by decide, by simp [replicateByte, AeadId.nonceSize]⟩
  simp only [AeadId.nonceSize]
  decide

/-- For an encryption suite, `key_schedule` derives the RFC's `key`,
`base_nonce` and `exporter_secret` from the mode value, PSK and PSK identifier
of the typed mode (which `VerifyPSKInputs` accepts), with sequence number 0,
kept as twelve zero bytes. -/
theorem keySchedule_encryption_eq_rfc {κ : Type} (L : LabeledKdf) (kem : KemId) (kdf : KdfId)
    (aead : AeadId) (mode : Mode κ) (sharedSecret info : Bytes) :
    ∃ st, keySchedule L (.encryption kem kdf aead) mode sharedSecret info = .encryption st ∧
      st.aead = aead ∧ st.kdf = kdf ∧ st.suiteId = Rfc.suite_id kem kdf (some aead) ∧
      st.sequence = replicateByte 12 0 ∧ st.busy = false ∧
      Rfc.KeySchedule L kem kdf (some aead) mode.rfcMode sharedSecret info
          (modeParams mode).2.1 (modeParams mode).2.2
        = .ok ⟨st.key, st.baseNonce, os2ip st.sequence, st.exporterSecret⟩ := by
  refine ⟨_, rfl, rfl, rfl, suiteId_encryption kem kdf aead, rfl, rfl, ?_⟩
  have hv := verifyPSKInputs_modeParams mode
  have hz : os2ip (replicateByte 12 0) = 0 := by decide
  simp only [Rfc.KeySchedule, hv, bind, Except.bind, pure, Except.pure]
  simp only [Suite.kdf, suiteId_encryption, hz, ascii_empty, modeParams_modeByte,
    hashSize_eq_Nh]
  cases aead <;> rfl

/-- For an export-only suite only `exporter_secret` is derived, and it is the
RFC's (with `aead_id = 0xFFFF` in `suite_id`). -/
theorem keySchedule_exportOnly_eq_rfc {κ : Type} (L : LabeledKdf) (kem : KemId) (kdf : KdfId)
    (mode : Mode κ) (sharedSecret info : Bytes) :
    ∃ st, keySchedule L (.exportOnly kem kdf) mode sharedSecret info = .exportOnly st ∧
      st.kdf = kdf ∧ st.suiteId = Rfc.suite_id kem kdf none ∧
      (Rfc.KeySchedule L kem kdf none mode.rfcMode sharedSecret info
          (modeParams mode).2.1 (modeParams mode).2.2).map (·.exporter_secret)
        = .ok st.exporterSecret := by
  refine ⟨_, rfl, rfl, suiteId_exportOnly kem kdf, ?_⟩
  have hv := verifyPSKInputs_modeParams mode
  simp only [Rfc.KeySchedule, hv, bind, Except.bind, pure, Except.pure, Except.map]
  simp only [Suite.kdf, suiteId_exportOnly, ascii_empty, modeParams_modeByte, hashSize_eq_Nh]

/-! ## Sender and receiver agree -/

theorem modeParams_erase {κ : Type} (m : Mode κ) : modeParams m.erase = modeParams m := by
  cases m <;> rfl

/-- The key schedule sees only the mode's kind and PSK: modes that agree up to
their keys give the same context. -/
theorem keySchedule_congr {κ₁ κ₂ : Type} (L : LabeledKdf) (suite : Suite)
    (m₁ : Mode κ₁) (m₂ : Mode κ₂) (h : m₁.erase = m₂.erase) (sharedSecret info : Bytes) :
    keySchedule L suite m₁ sharedSecret info = keySchedule L suite m₂ sharedSecret info := by
  have : modeParams m₁ = modeParams m₂ := by
    rw [← modeParams_erase m₁, h, modeParams_erase]
  simp only [keySchedule, this]

/-- In particular the receiver, who holds the public half of the sender key,
derives the sender's context from the same shared secret and info. -/
theorem keySchedule_map {κ κ' : Type} (L : LabeledKdf) (suite : Suite) (f : κ → κ')
    (m : Mode κ) (sharedSecret info : Bytes) :
    keySchedule L suite (m.map f) sharedSecret info = keySchedule L suite m sharedSecret info :=
  keySchedule_congr L suite _ _ (Mode.erase_map f m) sharedSecret info

/-! ## Keys and checks (lines 1091-1108) -/

/-- A public key as the setup layer sees it: its KEM (and its bytes). -/
structure PubKey where
  kem : KemId
  bytes : Bytes
  deriving DecidableEq, Repr

/-- A private key as the setup layer sees it. Its public half has the same KEM,
as every `Private_key.t` built by `Private_key.of_bytes` does. Whether the
secret is a Diffie-Hellman or an ML-KEM one is decided by `kem` (the
constructor `secret_and_public` picks, lines 523-558). -/
structure PrivKey where
  kem : KemId
  bytes : Bytes
  publicBytes : Bytes
  deriving DecidableEq, Repr

/-- `Private_key.public_key`. -/
def PrivKey.publicKey (key : PrivKey) : PubKey := ⟨key.kem, key.publicBytes⟩

@[simp] theorem PrivKey.publicKey_kem (key : PrivKey) : key.publicKey.kem = key.kem := rfl

/-- `check_public_key` (lines 1091-1093). -/
def checkPublicKey (suite : Suite) (key : PubKey) : Except Err Unit :=
  if suite.kem = key.kem then .ok () else .error .keyMismatch

/-- `check_private_key` (lines 1095-1097). -/
def checkPrivateKey (suite : Suite) (key : PrivKey) : Except Err Unit :=
  if suite.kem = key.kem then .ok () else .error .keyMismatch

/-- `check_sender_key` (lines 1099-1100). -/
def checkSenderKey {κ : Type} (check : Suite → κ → Except Err Unit) (suite : Suite)
    (mode : Mode κ) : Except Err Unit :=
  match senderKey mode with
  | none => .ok ()
  | some key => check suite key

/-- `check_mode` (lines 1104-1108). -/
def checkMode {κ : Type} (suite : Suite) (mode : Mode κ) : Except Err Unit :=
  match senderKey mode with
  | some _ => if !suite.kem.supportsAuth then .error .unsupportedMode else .ok ()
  | none => .ok ()

/-! ## Setup (lines 1110-1141) -/

/-- `'capability sender_setup` (lines 1008-1011). -/
structure SenderSetup where
  encapsulatedKey : Bytes
  context : Context
  deriving DecidableEq, Repr

/-- Lines 1114-1118 after `encap` returns: the key schedule on its secret. -/
def senderResult {κ : Type} (L : LabeledKdf) (suite : Suite) (mode : Mode κ) (info : Bytes) :
    Except Err (Bytes × Bytes) → Except Err SenderSetup
  | .error e => .error e
  | .ok (sharedSecret, encapsulatedKey) =>
    .ok { encapsulatedKey, context := keySchedule L suite mode sharedSecret info }

/-- Mirror of `setup_sender_inner` (lines 1110-1118), generic in the monad in
which `encap` runs. -/
def setupSenderInner {m : Type → Type} [Monad m] (L : LabeledKdf)
    (encap : Option PrivKey → PubKey → m (Except Err (Bytes × Bytes)))
    (suite : Suite) (recipient : PubKey) (mode : Mode PrivKey) (info : Bytes) :
    m (Except Err SenderSetup) :=
  match checkMode suite mode with
  | .error e => pure (.error e)
  | .ok () =>
    match checkPublicKey suite recipient with
    | .error e => pure (.error e)
    | .ok () =>
      match checkSenderKey checkPrivateKey suite mode with
      | .error e => pure (.error e)
      | .ok () => do
        let result ← encap (senderKey mode) recipient
        pure (senderResult L suite mode info result)

/-- Mirror of `setup_sender_encap` (lines 1120-1122). Its
`Invalid_argument → Invalid_length` handler is modelled by `encap` returning
`.error (.invalidLength _)`: nothing else in `setup_sender_inner` can raise
(`key_schedule`'s lengths and identifiers are in range). -/
def setupSenderEncap {m : Type → Type} [Monad m] (L : LabeledKdf)
    (encap : Option PrivKey → PubKey → m (Except Err (Bytes × Bytes))) :=
  setupSenderInner L encap

/-- `setup_sender ~rng` (line 1124): `encap ~rng` is the parameter. -/
def setupSender {m : Type → Type} [Monad m] (L : LabeledKdf)
    (encapRng : Option PrivKey → PubKey → m (Except Err (Bytes × Bytes))) :=
  setupSenderEncap L encapRng

/-- Lines 1133-1137 after `decap` returns. -/
def receiverResult {κ : Type} (L : LabeledKdf) (suite : Suite) (mode : Mode κ) (info : Bytes) :
    Except Err Bytes → Except Err Context
  | .error e => .error e
  | .ok sharedSecret => .ok (keySchedule L suite mode sharedSecret info)

/-- Mirror of `setup_receiver_inner` (lines 1129-1137), with `decap` a
parameter. -/
def setupReceiverInner {m : Type → Type} [Monad m] (L : LabeledKdf)
    (decap : PrivKey → Option PubKey → Bytes → m (Except Err Bytes))
    (suite : Suite) (recipient : PrivKey) (encapsulatedKey : Bytes) (mode : Mode PubKey)
    (info : Bytes) : m (Except Err Context) :=
  match checkMode suite mode with
  | .error e => pure (.error e)
  | .ok () =>
    match checkPrivateKey suite recipient with
    | .error e => pure (.error e)
    | .ok () =>
      match checkSenderKey checkPublicKey suite mode with
      | .error e => pure (.error e)
      | .ok () => do
        let result ← decap recipient (senderKey mode) encapsulatedKey
        pure (receiverResult L suite mode info result)

/-- Mirror of `setup_receiver` (lines 1139-1141); the handler is modelled as
for `setupSenderEncap`. -/
def setupReceiver {m : Type → Type} [Monad m] (L : LabeledKdf)
    (decap : PrivKey → Option PubKey → Bytes → m (Except Err Bytes)) :=
  setupReceiverInner L decap

/-- Mirror of `normalized_open` (lines 1180-1188). `openCiphertext` is
`Receiver.open_ context ~aad ~ciphertext`. -/
def normalizedOpen (openCiphertext : Context → Except Err Bytes)
    (setup : Except Err Context) : Except Err Bytes :=
  match setup with
  | .error .keyMismatch => .error .keyMismatch
  | .error .unsupportedMode => .error .unsupportedMode
  | .error _ => .error .openError
  | .ok context =>
    match openCiphertext context with
    | .ok plaintext => .ok plaintext
    | .error _ => .error .openError

/-! ### `Private.setup_*_with_ephemeral` (lines 1126-1127, 1230-1249) -/

/-- Mirror of `dh` (lines 744-769) on KEM-tagged keys; `exchange` is the
library exchange of a Diffie-Hellman secret with public-key octets. -/
def dh (exchange : PrivKey → PubKey → Except String Bytes) (sk : PrivKey) (pk : PubKey) :
    Except Err Bytes :=
  if sk.kem ≠ pk.kem then .error .keyMismatch
  else if sk.kem.isDh then
    match exchange sk pk with
    | .ok v => .ok v
    | .error reason => .error (.invalidPublicKey reason)
  else .error (.invalidPrivateKey "ML-KEM keys cannot perform a Diffie-Hellman exchange")

/-- Mirror of `encap_with` (lines 780-798); `extractAndExpand kem dh context`
is `extract_and_expand`. -/
def encapWith (exchange : PrivKey → PubKey → Except String Bytes)
    (extractAndExpand : KemId → Bytes → Bytes → Bytes)
    (ephemeral : PrivKey) (sender : Option PrivKey) (recipient : PubKey) :
    Except Err (Bytes × Bytes) := do
  let kem := recipient.kem
  let ephemeralDh ← dh exchange ephemeral recipient
  let (staticDh, senderPublic) ←
    match sender with
    | none => pure ([], [])
    | some sender => do
      let staticDh ← dh exchange sender recipient
      pure (staticDh, sender.publicKey.bytes)
  let encapsulatedKey := ephemeral.publicKey.bytes
  let kemContext := encapsulatedKey ++ recipient.bytes ++ senderPublic
  pure (extractAndExpand kem (ephemeralDh ++ staticDh) kemContext, encapsulatedKey)

/-- `setup_sender_with_ephemeral ~ephemeral` (lines 1126-1127), behind every
`Private.setup_*_sender_with_ephemeral`. -/
def setupSenderWithEphemeral (L : LabeledKdf)
    (exchange : PrivKey → PubKey → Except String Bytes)
    (extractAndExpand : KemId → Bytes → Bytes → Bytes) (ephemeral : PrivKey)
    (suite : Suite) (recipient : PubKey) (mode : Mode PrivKey) (info : Bytes) :
    Except Err SenderSetup :=
  setupSenderEncap (m := Id) L (encapWith exchange extractAndExpand ephemeral) suite recipient
    mode info

/-! ## (i)-(iii): the order of the checks and when `encap`/`decap` run -/

section Contracts

variable {m : Type → Type} [Monad m] (L : LabeledKdf)

theorem checkMode_error {κ : Type} (suite : Suite) (mode : Mode κ)
    (hs : (senderKey mode).isSome) (ha : suite.kem.supportsAuth = false) :
    checkMode suite mode = .error .unsupportedMode := by
  cases h : senderKey mode with
  | none => simp [h] at hs
  | some _ => simp [checkMode, h, ha]

theorem checkMode_ok {κ : Type} (suite : Suite) (mode : Mode κ)
    (h : (senderKey mode).isSome → suite.kem.supportsAuth = true) :
    checkMode suite mode = .ok () := by
  cases hk : senderKey mode with
  | none => simp [checkMode, hk]
  | some _ => simp [checkMode, hk, h (by simp [hk])]

/-- (i) An Auth or AuthPSK mode on a KEM without auth support is
`Unsupported_mode`, whatever the keys: none is examined and `encap` never runs
(the result is `pure`, in every monad, so no randomness is drawn). -/
theorem setupSender_unsupportedMode
    (encap : Option PrivKey → PubKey → m (Except Err (Bytes × Bytes)))
    (suite : Suite) (recipient : PubKey) (mode : Mode PrivKey) (info : Bytes)
    (hs : (senderKey mode).isSome) (ha : suite.kem.supportsAuth = false) :
    setupSenderInner L encap suite recipient mode info = pure (.error .unsupportedMode) := by
  simp only [setupSenderInner, checkMode_error suite mode hs ha]

theorem setupReceiver_unsupportedMode
    (decap : PrivKey → Option PubKey → Bytes → m (Except Err Bytes))
    (suite : Suite) (recipient : PrivKey) (enc : Bytes) (mode : Mode PubKey) (info : Bytes)
    (hs : (senderKey mode).isSome) (ha : suite.kem.supportsAuth = false) :
    setupReceiverInner L decap suite recipient enc mode info = pure (.error .unsupportedMode) := by
  simp only [setupReceiverInner, checkMode_error suite mode hs ha]

/-- (ii) Otherwise `Key_mismatch` unless the suite, the recipient key and the
sender key (if the mode has one) share one KEM; `encap` does not run. -/
theorem setupSender_keyMismatch
    (encap : Option PrivKey → PubKey → m (Except Err (Bytes × Bytes)))
    (suite : Suite) (recipient : PubKey) (mode : Mode PrivKey) (info : Bytes)
    (hmode : (senderKey mode).isSome → suite.kem.supportsAuth = true)
    (h : recipient.kem ≠ suite.kem ∨ ∃ k, senderKey mode = some k ∧ k.kem ≠ suite.kem) :
    setupSenderInner L encap suite recipient mode info = pure (.error .keyMismatch) := by
  simp only [setupSenderInner, checkMode_ok suite mode hmode]
  by_cases hr : recipient.kem = suite.kem
  · have hc : checkPublicKey suite recipient = .ok () := by simp [checkPublicKey, hr]
    obtain ⟨k, hk, hne⟩ := h.resolve_left (· hr)
    have hs : checkSenderKey checkPrivateKey suite mode = .error .keyMismatch := by
      simp [checkSenderKey, hk, checkPrivateKey, Ne.symm hne]
    simp only [hc, hs]
  · have hc : checkPublicKey suite recipient = .error .keyMismatch := by
      simp [checkPublicKey, Ne.symm hr]
    simp only [hc]

theorem setupReceiver_keyMismatch
    (decap : PrivKey → Option PubKey → Bytes → m (Except Err Bytes))
    (suite : Suite) (recipient : PrivKey) (enc : Bytes) (mode : Mode PubKey) (info : Bytes)
    (hmode : (senderKey mode).isSome → suite.kem.supportsAuth = true)
    (h : recipient.kem ≠ suite.kem ∨ ∃ k, senderKey mode = some k ∧ k.kem ≠ suite.kem) :
    setupReceiverInner L decap suite recipient enc mode info = pure (.error .keyMismatch) := by
  simp only [setupReceiverInner, checkMode_ok suite mode hmode]
  by_cases hr : recipient.kem = suite.kem
  · have hc : checkPrivateKey suite recipient = .ok () := by simp [checkPrivateKey, hr]
    obtain ⟨k, hk, hne⟩ := h.resolve_left (· hr)
    have hs : checkSenderKey checkPublicKey suite mode = .error .keyMismatch := by
      simp [checkSenderKey, hk, checkPublicKey, Ne.symm hne]
    simp only [hc, hs]
  · have hc : checkPrivateKey suite recipient = .error .keyMismatch := by
      simp [checkPrivateKey, Ne.symm hr]
    simp only [hc]

/-- (iii) When (i) and (ii) pass, the setup runs `encap` exactly once, with
`sender = sender_key mode`, and then the key schedule on its result. -/
theorem setupSender_runs_encap
    (encap : Option PrivKey → PubKey → m (Except Err (Bytes × Bytes)))
    (suite : Suite) (recipient : PubKey) (mode : Mode PrivKey) (info : Bytes)
    (hmode : (senderKey mode).isSome → suite.kem.supportsAuth = true)
    (hr : recipient.kem = suite.kem) (hs : ∀ k, senderKey mode = some k → k.kem = suite.kem) :
    setupSenderInner L encap suite recipient mode info
      = (encap (senderKey mode) recipient >>= fun r => pure (senderResult L suite mode info r)) := by
  have hc : checkPublicKey suite recipient = .ok () := by simp [checkPublicKey, hr]
  have hsk : checkSenderKey checkPrivateKey suite mode = .ok () := by
    cases hk : senderKey mode with
    | none => simp [checkSenderKey, hk]
    | some k => simp [checkSenderKey, hk, checkPrivateKey, hs k hk]
  simp only [setupSenderInner, checkMode_ok suite mode hmode, hc, hsk]

theorem setupReceiver_runs_decap
    (decap : PrivKey → Option PubKey → Bytes → m (Except Err Bytes))
    (suite : Suite) (recipient : PrivKey) (enc : Bytes) (mode : Mode PubKey) (info : Bytes)
    (hmode : (senderKey mode).isSome → suite.kem.supportsAuth = true)
    (hr : recipient.kem = suite.kem) (hs : ∀ k, senderKey mode = some k → k.kem = suite.kem) :
    setupReceiverInner L decap suite recipient enc mode info
      = (decap recipient (senderKey mode) enc >>= fun r => pure (receiverResult L suite mode info r)) := by
  have hc : checkPrivateKey suite recipient = .ok () := by simp [checkPrivateKey, hr]
  have hsk : checkSenderKey checkPublicKey suite mode = .ok () := by
    cases hk : senderKey mode with
    | none => simp [checkSenderKey, hk]
    | some k => simp [checkSenderKey, hk, checkPublicKey, hs k hk]
  simp only [setupReceiverInner, checkMode_ok suite mode hmode, hc, hsk]

/-- Conversely, `encap` runs only when (i) and (ii) pass: in every other case
the result is `pure` of an error. -/
theorem setupSender_pure_unless_checks
    (encap : Option PrivKey → PubKey → m (Except Err (Bytes × Bytes)))
    (suite : Suite) (recipient : PubKey) (mode : Mode PrivKey) (info : Bytes)
    (h : ¬ ((senderKey mode).isSome → suite.kem.supportsAuth = true) ∨
      ¬ (recipient.kem = suite.kem ∧ ∀ k, senderKey mode = some k → k.kem = suite.kem)) :
    ∃ e, setupSenderInner L encap suite recipient mode info = pure (.error e) := by
  by_cases hm : (senderKey mode).isSome → suite.kem.supportsAuth = true
  · have h' := h.resolve_left (· hm)
    refine ⟨_, setupSender_keyMismatch L encap suite recipient mode info hm ?_⟩
    by_cases hr : recipient.kem = suite.kem
    · refine .inr ?_
      apply Classical.byContradiction
      intro hn
      exact h' ⟨hr, fun k hk => Classical.byContradiction fun hk' => hn ⟨k, hk, hk'⟩⟩
    · exact .inl hr
  · have hs : (senderKey mode).isSome := Classical.byContradiction fun hn => hm (by simp_all)
    have ha : suite.kem.supportsAuth = false := by
      cases h' : suite.kem.supportsAuth
      · rfl
      · exact absurd (fun _ => h') hm
    exact ⟨_, setupSender_unsupportedMode L encap suite recipient mode info hs ha⟩

end Contracts

/-! ## Sender and receiver setups agree -/

/-- Same suite, mode (the receiver holding the public half of the sender
key), shared secret and info: the two setups produce the same context. -/
theorem setup_contexts_agree (L : LabeledKdf)
    (encap : Option PrivKey → PubKey → Except Err (Bytes × Bytes))
    (decap : PrivKey → Option PubKey → Bytes → Except Err Bytes)
    (suite : Suite) (recipient : PrivKey) (mode : Mode PrivKey) (info ss enc : Bytes)
    (hmode : (senderKey mode).isSome → suite.kem.supportsAuth = true)
    (hr : recipient.kem = suite.kem) (hs : ∀ k, senderKey mode = some k → k.kem = suite.kem)
    (hE : encap (senderKey mode) recipient.publicKey = .ok (ss, enc))
    (hD : decap recipient (senderKey (mode.map PrivKey.publicKey)) enc = .ok ss) :
    ∃ ctx,
      setupSenderInner (m := Id) L encap suite recipient.publicKey mode info = .ok ⟨enc, ctx⟩ ∧
      setupReceiverInner (m := Id) L decap suite recipient enc (mode.map PrivKey.publicKey) info
        = .ok ctx := by
  refine ⟨keySchedule L suite mode ss info, ?_, ?_⟩
  · rw [setupSender_runs_encap (m := Id) L encap suite recipient.publicKey mode info hmode hr hs]
    show senderResult L suite mode info (encap (senderKey mode) recipient.publicKey) = _
    rw [hE]; rfl
  · have hmode' : (senderKey (mode.map PrivKey.publicKey)).isSome →
        suite.kem.supportsAuth = true := by
      rw [Mode.senderKey_map]; simpa using hmode
    have hs' : ∀ k, senderKey (mode.map PrivKey.publicKey) = some k → k.kem = suite.kem := by
      intro k hk
      rw [Mode.senderKey_map] at hk
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
      exact hs k' hk'
    rw [setupReceiver_runs_decap (m := Id) L decap suite recipient enc _ info hmode' hr hs']
    show receiverResult L suite _ info (decap recipient _ enc) = _
    rw [hD]
    simp [receiverResult, keySchedule_map]

/-! ## (iv) `normalized_open` -/

theorem normalizedOpen_passthrough (openCiphertext : Context → Except Err Bytes) (e : Err)
    (h : e = .keyMismatch ∨ e = .unsupportedMode) :
    normalizedOpen openCiphertext (.error e) = .error e := by
  rcases h with rfl | rfl <;> rfl

theorem normalizedOpen_other (openCiphertext : Context → Except Err Bytes) (e : Err)
    (h1 : e ≠ .keyMismatch) (h2 : e ≠ .unsupportedMode) :
    normalizedOpen openCiphertext (.error e) = .error .openError := by
  cases e <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2

theorem normalizedOpen_ok (openCiphertext : Context → Except Err Bytes) (context : Context) :
    normalizedOpen openCiphertext (.ok context)
      = match openCiphertext context with
        | .ok plaintext => .ok plaintext
        | .error _ => .error .openError := rfl

/-- Every error of an `open_*` is `Key_mismatch`, `Unsupported_mode` (both only
from setup) or `Open_error`. -/
theorem normalizedOpen_error (openCiphertext : Context → Except Err Bytes)
    (setup : Except Err Context) (e : Err) (h : normalizedOpen openCiphertext setup = .error e) :
    (e = .keyMismatch ∧ setup = .error .keyMismatch) ∨
    (e = .unsupportedMode ∧ setup = .error .unsupportedMode) ∨ e = .openError := by
  unfold normalizedOpen at h
  split at h
  · cases h; exact .inl ⟨rfl, rfl⟩
  · cases h; exact .inr (.inl ⟨rfl, rfl⟩)
  · cases h; exact .inr (.inr rfl)
  · split at h
    · cases h
    · cases h; exact .inr (.inr rfl)

/-! ## (v) Caller-chosen ephemeral keys -/

theorem encapWith_keyMismatch (exchange : PrivKey → PubKey → Except String Bytes)
    (eae : KemId → Bytes → Bytes → Bytes) (ephemeral : PrivKey) (sender : Option PrivKey)
    (recipient : PubKey) (h : ephemeral.kem ≠ recipient.kem) :
    encapWith exchange eae ephemeral sender recipient = .error .keyMismatch := by
  simp [encapWith, dh, h, bind, Except.bind]

theorem encapWith_mlkem (exchange : PrivKey → PubKey → Except String Bytes)
    (eae : KemId → Bytes → Bytes → Bytes) (ephemeral : PrivKey) (sender : Option PrivKey)
    (recipient : PubKey) (h : ephemeral.kem = recipient.kem) (hml : ephemeral.kem.isDh = false) :
    encapWith exchange eae ephemeral sender recipient
      = .error (.invalidPrivateKey "ML-KEM keys cannot perform a Diffie-Hellman exchange") := by
  simp [encapWith, dh, h, bind, Except.bind]
  simp [← h, hml]

/-- (v) Once the setup checks pass, an ephemeral key of another KEM than the
recipient's is `Key_mismatch` (from `dh`). -/
theorem withEphemeral_keyMismatch (L : LabeledKdf)
    (exchange : PrivKey → PubKey → Except String Bytes) (eae : KemId → Bytes → Bytes → Bytes)
    (ephemeral : PrivKey) (suite : Suite) (recipient : PubKey) (mode : Mode PrivKey)
    (info : Bytes) (hmode : (senderKey mode).isSome → suite.kem.supportsAuth = true)
    (hr : recipient.kem = suite.kem) (hs : ∀ k, senderKey mode = some k → k.kem = suite.kem)
    (h : ephemeral.kem ≠ recipient.kem) :
    setupSenderWithEphemeral L exchange eae ephemeral suite recipient mode info
      = .error .keyMismatch := by
  unfold setupSenderWithEphemeral setupSenderEncap
  rw [setupSender_runs_encap (m := Id) L _ suite recipient mode info hmode hr hs]
  show senderResult L suite mode info (encapWith exchange eae ephemeral _ recipient) = _
  rw [encapWith_keyMismatch exchange eae ephemeral _ recipient h]
  rfl

/-- (v) ... and an ML-KEM ephemeral key of the recipient's KEM is
`Invalid_private_key`. -/
theorem withEphemeral_mlkem (L : LabeledKdf)
    (exchange : PrivKey → PubKey → Except String Bytes) (eae : KemId → Bytes → Bytes → Bytes)
    (ephemeral : PrivKey) (suite : Suite) (recipient : PubKey) (mode : Mode PrivKey)
    (info : Bytes) (hmode : (senderKey mode).isSome → suite.kem.supportsAuth = true)
    (hr : recipient.kem = suite.kem) (hs : ∀ k, senderKey mode = some k → k.kem = suite.kem)
    (h : ephemeral.kem = recipient.kem) (hml : ephemeral.kem.isDh = false) :
    setupSenderWithEphemeral L exchange eae ephemeral suite recipient mode info
      = .error (.invalidPrivateKey "ML-KEM keys cannot perform a Diffie-Hellman exchange") := by
  unfold setupSenderWithEphemeral setupSenderEncap
  rw [setupSender_runs_encap (m := Id) L _ suite recipient mode info hmode hr hs]
  show senderResult L suite mode info (encapWith exchange eae ephemeral _ recipient) = _
  rw [encapWith_mlkem exchange eae ephemeral _ recipient h hml]
  rfl

/-! ## The error-class table -/

/-- The error class of a result, `none` for success. -/
def resultClass {α : Type} : Except Err α → Option ErrClass
  | .ok _ => none
  | .error e => some e.cls

/-- The documented contract of every `setup_*` (hpke.mli, `setup_auth_sender`):
`Unsupported_mode` if the mode has a sender key and the suite's KEM has no Auth
mode; otherwise `Key_mismatch` unless the suite, the recipient key and the
sender key (if any) share one KEM; otherwise success, for valid keys and a
valid encapsulation. `mode` is `0` Base, `1` PSK, `2` Auth, `3` AuthPSK. -/
def expectedClass (suiteKem recipientKem : KemId) (senderKem : Option KemId) (mode : Nat) :
    Option ErrClass :=
  if 2 ≤ mode ∧ suiteKem.supportsAuth = false then some .unsupportedMode
  else if recipientKem ≠ suiteKem then some .keyMismatch
  else
    match senderKem with
    | some k => if k ≠ suiteKem then some .keyMismatch else none
    | none => none

/-- **Assumption** for the table: `encap` succeeds on valid keys of one KEM
(with a sender key only for a KEM with auth support). -/
def EncapSucceeds (encap : Option PrivKey → PubKey → Except Err (Bytes × Bytes)) : Prop :=
  ∀ sender recipient, (∀ k, sender = some k → k.kem = recipient.kem) →
    (sender.isSome → recipient.kem.supportsAuth = true) →
    ∃ v, encap sender recipient = .ok v

/-- **Assumption** for the table: `decap` succeeds on valid keys of one KEM and
the valid encapsulation `enc`. -/
def DecapSucceeds (decap : PrivKey → Option PubKey → Bytes → Except Err Bytes) (enc : Bytes) :
    Prop :=
  ∀ recipient sender, (∀ k, sender = some k → k.kem = recipient.kem) →
    (sender.isSome → recipient.kem.supportsAuth = true) →
    ∃ ss, decap recipient sender enc = .ok ss

/-- `setup_sender` returns the class `expectedClass` predicts. -/
theorem setupSender_class (L : LabeledKdf)
    (encap : Option PrivKey → PubKey → Except Err (Bytes × Bytes)) (hE : EncapSucceeds encap)
    (suite : Suite) (recipient : PubKey) (mode : Mode PrivKey) (info : Bytes) :
    resultClass (setupSenderInner (m := Id) L encap suite recipient mode info)
      = expectedClass suite.kem recipient.kem ((senderKey mode).map PrivKey.kem) mode.num := by
  by_cases hA : (senderKey mode).isSome ∧ suite.kem.supportsAuth = false
  · rw [setupSender_unsupportedMode (m := Id) L encap suite recipient mode info hA.1 hA.2]
    have : 2 ≤ mode.num := (Mode.two_le_num_iff mode).mpr hA.1
    simp [expectedClass, this, hA.2, resultClass, pure, Err.cls]
  · have hmode : (senderKey mode).isSome → suite.kem.supportsAuth = true := by
      intro hs
      cases h : suite.kem.supportsAuth
      · exact absurd ⟨hs, h⟩ hA
      · rfl
    have hE1 : ¬ (2 ≤ mode.num ∧ suite.kem.supportsAuth = false) := by
      rw [Mode.two_le_num_iff]; exact hA
    by_cases hK : recipient.kem = suite.kem ∧ ∀ k, senderKey mode = some k → k.kem = suite.kem
    · rw [setupSender_runs_encap (m := Id) L encap suite recipient mode info hmode hK.1 hK.2]
      obtain ⟨v, hv⟩ := hE (senderKey mode) recipient
        (fun k hk => (hK.2 k hk).trans hK.1.symm) (fun hs => hK.1 ▸ hmode hs)
      show resultClass (senderResult L suite mode info (encap (senderKey mode) recipient)) = _
      rw [hv]
      cases hk : senderKey mode with
      | none => simp [expectedClass, hE1, hK.1, resultClass, senderResult]
      | some k => simp [expectedClass, hE1, hK.1, hK.2 k hk, resultClass, senderResult]
    · have hK' : recipient.kem ≠ suite.kem ∨ ∃ k, senderKey mode = some k ∧ k.kem ≠ suite.kem := by
        by_cases hr : recipient.kem = suite.kem
        · refine .inr (Classical.byContradiction fun hn => hK ⟨hr, fun k hk => ?_⟩)
          exact Classical.byContradiction fun hk' => hn ⟨k, hk, hk'⟩
        · exact .inl hr
      rw [setupSender_keyMismatch (m := Id) L encap suite recipient mode info hmode hK']
      rcases hK' with hr | ⟨k, hk, hne⟩
      · simp [expectedClass, hE1, hr, resultClass, pure, Err.cls]
      · by_cases hr : recipient.kem = suite.kem
        · simp [expectedClass, hE1, hr, hk, hne, resultClass, pure, Err.cls]
        · simp [expectedClass, hE1, hr, resultClass, pure, Err.cls]

/-- `setup_receiver` returns the class `expectedClass` predicts, for a valid
encapsulation. -/
theorem setupReceiver_class (L : LabeledKdf)
    (decap : PrivKey → Option PubKey → Bytes → Except Err Bytes) (enc : Bytes)
    (hD : DecapSucceeds decap enc)
    (suite : Suite) (recipient : PrivKey) (mode : Mode PubKey) (info : Bytes) :
    resultClass (setupReceiverInner (m := Id) L decap suite recipient enc mode info)
      = expectedClass suite.kem recipient.kem ((senderKey mode).map PubKey.kem) mode.num := by
  by_cases hA : (senderKey mode).isSome ∧ suite.kem.supportsAuth = false
  · rw [setupReceiver_unsupportedMode (m := Id) L decap suite recipient enc mode info hA.1 hA.2]
    have : 2 ≤ mode.num := (Mode.two_le_num_iff mode).mpr hA.1
    simp [expectedClass, this, hA.2, resultClass, pure, Err.cls]
  · have hmode : (senderKey mode).isSome → suite.kem.supportsAuth = true := by
      intro hs
      cases h : suite.kem.supportsAuth
      · exact absurd ⟨hs, h⟩ hA
      · rfl
    have hE1 : ¬ (2 ≤ mode.num ∧ suite.kem.supportsAuth = false) := by
      rw [Mode.two_le_num_iff]; exact hA
    by_cases hK : recipient.kem = suite.kem ∧ ∀ k, senderKey mode = some k → k.kem = suite.kem
    · rw [setupReceiver_runs_decap (m := Id) L decap suite recipient enc mode info hmode hK.1 hK.2]
      obtain ⟨v, hv⟩ := hD recipient (senderKey mode)
        (fun k hk => (hK.2 k hk).trans hK.1.symm) (fun hs => hK.1 ▸ hmode hs)
      show resultClass (receiverResult L suite mode info (decap recipient (senderKey mode) enc)) = _
      rw [hv]
      cases hk : senderKey mode with
      | none => simp [expectedClass, hE1, hK.1, resultClass, receiverResult]
      | some k => simp [expectedClass, hE1, hK.1, hK.2 k hk, resultClass, receiverResult]
    · have hK' : recipient.kem ≠ suite.kem ∨ ∃ k, senderKey mode = some k ∧ k.kem ≠ suite.kem := by
        by_cases hr : recipient.kem = suite.kem
        · refine .inr (Classical.byContradiction fun hn => hK ⟨hr, fun k hk => ?_⟩)
          exact Classical.byContradiction fun hk' => hn ⟨k, hk, hk'⟩
        · exact .inl hr
      rw [setupReceiver_keyMismatch (m := Id) L decap suite recipient enc mode info hmode hK']
      rcases hK' with hr | ⟨k, hk, hne⟩
      · simp [expectedClass, hE1, hr, resultClass, pure, Err.cls]
      · by_cases hr : recipient.kem = suite.kem
        · simp [expectedClass, hE1, hr, hk, hne, resultClass, pure, Err.cls]
        · simp [expectedClass, hE1, hr, resultClass, pure, Err.cls]

/-- Every row of the conformance table: suite KEM, recipient KEM, sender KEM
(only in the Auth modes, which alone carry a sender key), mode. -/
def rows : List (KemId × KemId × Option KemId × Nat) :=
  KemId.all.flatMap fun s => KemId.all.flatMap fun r => [0, 1, 2, 3].flatMap fun md =>
    (if 2 ≤ md then KemId.all.map some else [none]).map fun sk => (s, r, sk, md)

/-- The conformance table: each row with its expected error class (`none` is
success). -/
def table : List (KemId × KemId × Option KemId × Nat × Option ErrClass) :=
  rows.map fun (s, r, sk, md) => (s, r, sk, md, expectedClass s r sk md)

theorem mem_rows (s r : KemId) (sk : Option KemId) (md : Nat) :
    (s, r, sk, md) ∈ rows ↔ md < 4 ∧ (2 ≤ md ↔ sk.isSome) := by
  have hs := KemId.mem_all s
  have hr := KemId.mem_all r
  constructor
  · intro h
    simp only [rows, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, _, _, _, md', hmd', sk', hsk', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmd'
    rcases hmd' with rfl | rfl | rfl | rfl <;>
      simp_all <;> (obtain ⟨k, _, rfl⟩ := hsk'; rfl)
  · rintro ⟨h4, h2⟩
    simp only [rows, List.mem_flatMap, List.mem_map]
    refine ⟨s, hs, r, hr, md, by simp; omega, sk, ?_, rfl⟩
    by_cases hmd : 2 ≤ md
    · obtain ⟨k, rfl⟩ := Option.isSome_iff_exists.mp (h2.mp hmd)
      simp [hmd, KemId.mem_all]
    · cases sk with
      | none => simp [hmd]
      | some k => exact absurd (h2.mpr rfl) hmd

theorem mem_table (row : KemId × KemId × Option KemId × Nat × Option ErrClass) :
    row ∈ table ↔ (row.1, row.2.1, row.2.2.1, row.2.2.2.1) ∈ rows ∧
      row.2.2.2.2 = expectedClass row.1 row.2.1 row.2.2.1 row.2.2.2.1 := by
  obtain ⟨s, r, sk, md, c⟩ := row
  simp only [table, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨s', r', sk', md'⟩, h, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨(s, r, sk, md), h, rfl, rfl, rfl, rfl, rfl⟩

/-- Completeness: every sender setup appears in the table, with its class. -/
theorem setupSender_in_table (L : LabeledKdf)
    (encap : Option PrivKey → PubKey → Except Err (Bytes × Bytes)) (hE : EncapSucceeds encap)
    (suite : Suite) (recipient : PubKey) (mode : Mode PrivKey) (info : Bytes) :
    (suite.kem, recipient.kem, (senderKey mode).map PrivKey.kem, mode.num,
      resultClass (setupSenderInner (m := Id) L encap suite recipient mode info)) ∈ table := by
  rw [mem_table, setupSender_class L encap hE]
  refine ⟨(mem_rows _ _ _ _).mpr ⟨Mode.num_lt mode, ?_⟩, rfl⟩
  rw [Mode.two_le_num_iff]; simp

theorem setupReceiver_in_table (L : LabeledKdf)
    (decap : PrivKey → Option PubKey → Bytes → Except Err Bytes) (enc : Bytes)
    (hD : DecapSucceeds decap enc)
    (suite : Suite) (recipient : PrivKey) (mode : Mode PubKey) (info : Bytes) :
    (suite.kem, recipient.kem, (senderKey mode).map PubKey.kem, mode.num,
      resultClass (setupReceiverInner (m := Id) L decap suite recipient enc mode info)) ∈ table := by
  rw [mem_table, setupReceiver_class L decap enc hD]
  refine ⟨(mem_rows _ _ _ _).mpr ⟨Mode.num_lt mode, ?_⟩, rfl⟩
  rw [Mode.two_le_num_iff]; simp

/-- Soundness: a row's class is the class of every setup it describes. -/
theorem table_sound (L : LabeledKdf)
    (encap : Option PrivKey → PubKey → Except Err (Bytes × Bytes)) (hE : EncapSucceeds encap)
    (s r : KemId) (sk : Option KemId) (md : Nat) (c : Option ErrClass)
    (hrow : (s, r, sk, md, c) ∈ table)
    (suite : Suite) (recipient : PubKey) (mode : Mode PrivKey) (info : Bytes)
    (hs : suite.kem = s) (hr : recipient.kem = r)
    (hsk : (senderKey mode).map PrivKey.kem = sk) (hmd : mode.num = md) :
    resultClass (setupSenderInner (m := Id) L encap suite recipient mode info) = c := by
  rw [setupSender_class L encap hE, hs, hr, hsk, hmd]
  exact ((mem_table _).mp hrow).2.symm

/-- The `Private.setup_*_with_ephemeral` functions on an ML-KEM suite never
succeed. They return `Invalid_private_key` only when the checks pass and the
ephemeral key is an ML-KEM key of the suite's KEM; an Auth or AuthPSK mode is
`Unsupported_mode`, and a recipient or ephemeral key of another KEM is
`Key_mismatch`. (hpke.mli says "with an ML-KEM suite they return
[Invalid_private_key]", which is exact only in the first case.) -/
theorem withEphemeral_mlkem_suite (L : LabeledKdf)
    (exchange : PrivKey → PubKey → Except String Bytes) (eae : KemId → Bytes → Bytes → Bytes)
    (ephemeral : PrivKey) (suite : Suite) (recipient : PubKey) (mode : Mode PrivKey)
    (info : Bytes) (hml : suite.kem.isDh = false) :
    resultClass (setupSenderWithEphemeral L exchange eae ephemeral suite recipient mode info)
      = match expectedClass suite.kem recipient.kem ((senderKey mode).map PrivKey.kem) mode.num with
        | some c => some c
        | none => if ephemeral.kem = suite.kem then some .invalidPrivateKey
                  else some .keyMismatch := by
  have ha : suite.kem.supportsAuth = false := by rw [supportsAuth_iff_isDh]; exact hml
  unfold setupSenderWithEphemeral setupSenderEncap
  cases hk : senderKey mode with
  | some k =>
    rw [setupSender_unsupportedMode (m := Id) L _ suite recipient mode info (by simp [hk]) ha]
    have : 2 ≤ mode.num := (Mode.two_le_num_iff mode).mpr (by simp [hk])
    simp [expectedClass, this, ha, resultClass, pure, Err.cls]
  | none =>
    have hn : ¬ 2 ≤ mode.num := by rw [Mode.two_le_num_iff, hk]; simp
    have hmode : (senderKey mode).isSome → suite.kem.supportsAuth = true := by simp [hk]
    by_cases hr : recipient.kem = suite.kem
    · rw [setupSender_runs_encap (m := Id) L _ suite recipient mode info hmode hr
        (by simp [hk])]
      show resultClass (senderResult L suite mode info
        (encapWith exchange eae ephemeral (senderKey mode) recipient)) = _
      by_cases he : ephemeral.kem = recipient.kem
      · rw [encapWith_mlkem exchange eae ephemeral _ recipient he (by rw [he, hr]; exact hml)]
        simp [expectedClass, hn, hr, resultClass, senderResult, Err.cls, he]
      · rw [encapWith_keyMismatch exchange eae ephemeral _ recipient he]
        simp [expectedClass, hn, resultClass, senderResult, Err.cls, ← hr, he]
    · rw [setupSender_keyMismatch (m := Id) L _ suite recipient mode info hmode (.inl hr)]
      simp [expectedClass, hn, hr, resultClass, pure, Err.cls]

/-! ### Printing the table -/

/-- The OCaml constructor of a `Kem.id`. -/
def kemName : KemId → String
  | .p256 => "P256" | .p384 => "P384" | .p521 => "P521" | .x25519 => "X25519"
  | .x448 => "X448" | .mlkem512 => "Mlkem512" | .mlkem768 => "Mlkem768"
  | .mlkem1024 => "Mlkem1024"

/-- The OCaml constructor of a mode. -/
def modeName : Nat → String
  | 0 => "Base" | 1 => "Psk_mode" | 2 => "Auth" | _ => "Auth_psk"

/-- The OCaml constructor of the expected result. -/
def className : Option ErrClass → String
  | none => "Ok"
  | some .keyMismatch => "Key_mismatch"
  | some .unsupportedMode => "Unsupported_mode"
  | some c => reprStr c

/-- One line per row: `suite_kem recipient_kem sender_kem|- mode result`. -/
def tableLines : List String :=
  table.map fun (s, r, sk, md, c) =>
    s!"{kemName s} {kemName r} {(sk.map kemName).getD "-"} {modeName md} {className c}"

theorem table_length : table.length = 1152 := by decide +kernel

/-- How many rows expect each result. -/
def classCounts : List (String × Nat) :=
  ["Ok", "Key_mismatch", "Unsupported_mode"].map fun n =>
    (n, (table.filter fun (_, _, _, _, c) => className c = n).length)

theorem classCounts_eq :
    classCounts = [("Ok", 26), ("Key_mismatch", 742), ("Unsupported_mode", 384)] := by
  decide +kernel

/-- An ML-KEM suite refuses both authenticated modes even with matching keys. -/
theorem table_mlkem_auth :
    ("Mlkem768 Mlkem768 Mlkem768 Auth Unsupported_mode" ∈ tableLines) ∧
    ("Mlkem768 Mlkem768 Mlkem768 Auth_psk Unsupported_mode" ∈ tableLines) ∧
    ("X25519 X25519 X25519 Auth_psk Ok" ∈ tableLines) := by
  decide +kernel

end Setup
end Hpke
