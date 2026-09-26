import HpkeSpec.Bytes
import HpkeSpec.Registry

/-!
The byte encodings of `lib/hpke.ml`: `Util.i2osp2` and `Util.byte`, the suite
identifiers, the inputs the labeled KDF functions hand to the underlying KDF,
and the key-schedule context.

As in `Registry.lean`, *mirrors* transcribe the OCaml functions and *specs*
transcribe RFC 9180, draft-ietf-hpke-hpke-04 and draft-ietf-hpke-pq-05. An
OCaml `int` that may be negative is an `Int`. A function that can raise
`Invalid_argument` returns `Option`, with `none` for the exception.

The theorems prove that each mirror computes its spec, that the identifiers and
contexts are injective, that the `invalid_arg "I2OSP(2)"` of `i2osp2` is
unreachable from the library, and that the input limits of RFC 9180
Section 7.2.1, which the library does not check, exceed every OCaml string.
Concatenation with `^`, which raises `Invalid_argument "Bytes.create"` beyond
`Sys.max_string_length`, is modelled as total `++`; the last section bounds
where that matters.
-/

namespace Hpke

/-! ## `Util.i2osp2` and `Util.byte` -/

/-- `Char.chr`, which raises `Invalid_argument` outside `[0, 255]`. -/
def charChr (n : Int) : Option UInt8 :=
  if n < 0 ∨ n > 255 then none else some (UInt8.ofNat n.toNat)

/-- Mirror of `Util.i2osp2` (`lib/hpke.ml` lines 289-293). `none` is
`invalid_arg "I2OSP(2)"`. On the branch that returns, `value` is non-negative,
so `lsr` and `land` act on `value.toNat`. -/
def i2osp2 (value : Int) : Option Bytes :=
  if value < 0 ∨ value > 0xffff then none
  else do
    let hi ← charChr (((value.toNat >>> 8) &&& 0xff : Nat) : Int)
    let lo ← charChr ((value.toNat &&& 0xff : Nat) : Int)
    pure [hi, lo]

/-- Mirror of `Util.byte` (line 295): `String.make 1 (Char.chr value)`. -/
def byte (value : Int) : Option Bytes := (charChr value).map fun c => [c]

private theorem land_ff (n : Nat) : n &&& 0xff = n % 256 := by
  have := Nat.and_two_pow_sub_one_eq_mod n 8
  simpa using this

private theorem lsr_8 (n : Nat) : n >>> 8 = n / 256 := by
  simp [Nat.shiftRight_eq_div_pow]

private theorem charChr_of_lt {n : Nat} (h : n < 256) :
    charChr n = some (UInt8.ofNat n) := by
  unfold charChr
  rw [ite_eq_right (by omega)]
  simp

theorem i2osp_two (n : Nat) :
    i2osp n 2 = [UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)] := rfl

theorem i2osp_one (n : Nat) : i2osp n 1 = [UInt8.ofNat (n % 256)] := rfl

/-- On `[0, 0xffff]`, `i2osp2` is `I2OSP(·, 2)`. -/
theorem i2osp2_of_range {v : Int} (h0 : 0 ≤ v) (h1 : v < 0x10000) :
    i2osp2 v = some (i2osp v.toNat 2) := by
  have hn : v.toNat < 65536 := by omega
  unfold i2osp2
  rw [ite_eq_right (by omega), land_ff, land_ff, lsr_8,
    charChr_of_lt (by omega), charChr_of_lt (by omega), i2osp_two]
  rfl

theorem i2osp2_nat {n : Nat} (h : n < 0x10000) : i2osp2 n = some (i2osp n 2) := by
  rw [i2osp2_of_range (by omega) (by omega), Int.toNat_natCast]

/-- `i2osp2` raises exactly outside `[0, 0xffff]`, the domain of `I2OSP(·, 2)`. -/
theorem i2osp2_eq_none_iff (v : Int) : i2osp2 v = none ↔ v < 0 ∨ 0xffff < v := by
  by_cases h : v < 0 ∨ 0xffff < v
  · simp only [h, iff_true]
    unfold i2osp2
    rw [ite_eq_left (by omega)]
  · simp only [h, iff_false]
    rw [i2osp2_of_range (by omega) (by omega)]
    simp

/-- On `[0, 255]`, `Util.byte` is `I2OSP(·, 1)`. -/
theorem byte_of_range {v : Int} (h0 : 0 ≤ v) (h1 : v < 256) :
    byte v = some (i2osp v.toNat 1) := by
  have hn : v.toNat < 256 := by omega
  unfold byte charChr
  rw [ite_eq_right (by omega), i2osp_one, Nat.mod_eq_of_lt hn]
  rfl

theorem byte_eq_none_iff (v : Int) : byte v = none ↔ v < 0 ∨ 255 < v := by
  unfold byte charChr
  by_cases h : v < 0 ∨ v > 255
  · rw [ite_eq_left h]; simp only [Option.map_none, true_iff]; omega
  · rw [ite_eq_right h]; simp only [Option.map_some, reduceCtorEq, false_iff]; omega

/-! ## Suite identifiers -/

/-- `Labeled_kdf.version_label` (line 637). -/
def versionLabel : Bytes := ascii "HPKE-v1"

theorem ascii_HPKE : ascii "HPKE" = [0x48, 0x50, 0x4b, 0x45] := by decide +kernel
theorem ascii_KEM : ascii "KEM" = [0x4b, 0x45, 0x4d] := by decide +kernel
theorem ascii_HPKE_v1 : ascii "HPKE-v1" = [0x48, 0x50, 0x4b, 0x45, 0x2d, 0x76, 0x31] := by
  decide +kernel

@[simp] theorem length_versionLabel : versionLabel.length = 7 := by
  simp [versionLabel, ascii_HPKE_v1]

/-- `Suite.aead_id` (lines 631-633): the AEAD's identifier, or `0xffff` for an
export-only suite (`none`). -/
def suiteAeadId : Option AeadId → Int
  | some a => a.toInt
  | none => 0xffff

theorem suiteAeadId_none : suiteAeadId none = exportOnlyAeadId := rfl

theorem suiteAeadId_range (a : Option AeadId) :
    0 ≤ suiteAeadId a ∧ suiteAeadId a < 0x10000 := by
  rcases a with _ | a
  · decide
  · cases a <;> decide

theorem suiteAeadId_injective {a b : Option AeadId}
    (h : suiteAeadId a = suiteAeadId b) : a = b := by
  rcases a with _ | a <;> rcases b with _ | b
  · rfl
  · cases b <;> simp_all [suiteAeadId, AeadId.toInt]
  · cases a <;> simp_all [suiteAeadId, AeadId.toInt]
  · cases a <;> cases b <;> simp_all [suiteAeadId, AeadId.toInt]

/-- Mirror of `Labeled_kdf.suite_id` (lines 639-643). A suite is its KEM, KDF
and AEAD, `none` for `Suite.Export_only`. -/
def suiteIdMirror (kem : KemId) (kdf : KdfId) (aead : Option AeadId) : Option Bytes := do
  let k ← i2osp2 kem.toInt
  let f ← i2osp2 kdf.toInt
  let a ← i2osp2 (suiteAeadId aead)
  pure (ascii "HPKE" ++ (k ++ (f ++ a)))

/-- RFC 9180 Section 5.1:
`suite_id = concat("HPKE", I2OSP(kem_id, 2), I2OSP(kdf_id, 2), I2OSP(aead_id, 2))`. -/
def suiteIdSpec (kemId kdfId aeadId : Nat) : Bytes :=
  ascii "HPKE" ++ i2osp kemId 2 ++ i2osp kdfId 2 ++ i2osp aeadId 2

/-- The HPKE `suite_id` of a suite, with `aead_id = 0xFFFF` when export-only
(RFC 9180 Table 5). -/
def suiteId (kem : KemId) (kdf : KdfId) (aead : Option AeadId) : Bytes :=
  suiteIdSpec kem.toInt.toNat kdf.toInt.toNat (suiteAeadId aead).toNat

/-- Mirror of `Labeled_kdf.kem_suite_id` (line 645). -/
def kemSuiteIdMirror (kem : KemId) : Option Bytes := do
  let k ← i2osp2 kem.toInt
  pure (ascii "KEM" ++ k)

/-- RFC 9180 Section 4.1 (and draft-ietf-hpke-pq-05 Section 3):
`suite_id = concat("KEM", I2OSP(kem_id, 2))`. -/
def kemSuiteIdSpec (kemId : Nat) : Bytes := ascii "KEM" ++ i2osp kemId 2

def kemSuiteId (kem : KemId) : Bytes := kemSuiteIdSpec kem.toInt.toNat

/-- `Labeled_kdf.suite_id` never raises and computes RFC 9180's `suite_id`. -/
theorem suiteIdMirror_eq (kem : KemId) (kdf : KdfId) (aead : Option AeadId) :
    suiteIdMirror kem kdf aead = some (suiteId kem kdf aead) := by
  have hk := ids_in_range.1 kem
  have hf := ids_in_range.2.1 kdf
  have ha := suiteAeadId_range aead
  simp [suiteIdMirror, suiteId, suiteIdSpec, i2osp2_of_range hk.1 hk.2,
    i2osp2_of_range hf.1 hf.2, i2osp2_of_range ha.1 ha.2]

/-- `Labeled_kdf.kem_suite_id` never raises and computes RFC 9180's KEM
`suite_id`. -/
theorem kemSuiteIdMirror_eq (kem : KemId) :
    kemSuiteIdMirror kem = some (kemSuiteId kem) := by
  have hk := ids_in_range.1 kem
  simp [kemSuiteIdMirror, kemSuiteId, kemSuiteIdSpec, i2osp2_of_range hk.1 hk.2]

theorem suiteId_exportOnly (kem : KemId) (kdf : KdfId) :
    suiteId kem kdf none = suiteIdSpec kem.toInt.toNat kdf.toInt.toNat 0xFFFF := rfl

@[simp] theorem length_suiteIdSpec (k f a : Nat) : (suiteIdSpec k f a).length = 10 := by
  simp [suiteIdSpec, ascii_HPKE]

@[simp] theorem length_suiteId (kem : KemId) (kdf : KdfId) (aead : Option AeadId) :
    (suiteId kem kdf aead).length = 10 := length_suiteIdSpec _ _ _

@[simp] theorem length_kemSuiteIdSpec (k : Nat) : (kemSuiteIdSpec k).length = 5 := by
  simp [kemSuiteIdSpec, ascii_KEM]

@[simp] theorem length_kemSuiteId (kem : KemId) : (kemSuiteId kem).length = 5 :=
  length_kemSuiteIdSpec _

private theorem i2osp_two_injective {x y : Nat} (hx : x < 0x10000) (hy : y < 0x10000)
    (h : i2osp x 2 = i2osp y 2) : x = y :=
  i2osp_injective (by simpa using hx) (by simpa using hy) h

/-- RFC 9180's `suite_id` is injective on identifiers that fit two bytes. -/
theorem suiteIdSpec_injective {k₁ f₁ a₁ k₂ f₂ a₂ : Nat}
    (hk₁ : k₁ < 0x10000) (hf₁ : f₁ < 0x10000) (ha₁ : a₁ < 0x10000)
    (hk₂ : k₂ < 0x10000) (hf₂ : f₂ < 0x10000) (ha₂ : a₂ < 0x10000)
    (h : suiteIdSpec k₁ f₁ a₁ = suiteIdSpec k₂ f₂ a₂) :
    k₁ = k₂ ∧ f₁ = f₂ ∧ a₁ = a₂ := by
  unfold suiteIdSpec at h
  obtain ⟨h, ha⟩ := List.append_inj' h (by simp)
  obtain ⟨h, hf⟩ := List.append_inj' h (by simp)
  obtain ⟨_, hk⟩ := List.append_inj' h (by simp)
  exact ⟨i2osp_two_injective hk₁ hk₂ hk, i2osp_two_injective hf₁ hf₂ hf,
    i2osp_two_injective ha₁ ha₂ ha⟩

private theorem toNat_inj {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x.toNat = y.toNat) :
    x = y := by omega

/-- `suite_id` determines the KEM, the KDF, and the AEAD or export-only
operation. -/
theorem suiteId_injective {kem₁ kem₂ : KemId} {kdf₁ kdf₂ : KdfId}
    {aead₁ aead₂ : Option AeadId}
    (h : suiteId kem₁ kdf₁ aead₁ = suiteId kem₂ kdf₂ aead₂) :
    kem₁ = kem₂ ∧ kdf₁ = kdf₂ ∧ aead₁ = aead₂ := by
  have hk₁ := ids_in_range.1 kem₁
  have hk₂ := ids_in_range.1 kem₂
  have hf₁ := ids_in_range.2.1 kdf₁
  have hf₂ := ids_in_range.2.1 kdf₂
  have ha₁ := suiteAeadId_range aead₁
  have ha₂ := suiteAeadId_range aead₂
  obtain ⟨hk, hf, ha⟩ := suiteIdSpec_injective (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) h
  exact ⟨KemId.toInt_injective (toNat_inj hk₁.1 hk₂.1 hk),
    KdfId.toInt_injective (toNat_inj hf₁.1 hf₂.1 hf),
    suiteAeadId_injective (toNat_inj ha₁.1 ha₂.1 ha)⟩

/-- An export-only suite never shares a `suite_id` with an encryption suite. -/
theorem suiteId_exportOnly_ne (kem kem' : KemId) (kdf kdf' : KdfId) (aead : AeadId) :
    suiteId kem kdf none ≠ suiteId kem' kdf' (some aead) := by
  intro h
  exact nomatch (suiteId_injective h).2.2

theorem kemSuiteIdSpec_injective {k₁ k₂ : Nat} (hk₁ : k₁ < 0x10000) (hk₂ : k₂ < 0x10000)
    (h : kemSuiteIdSpec k₁ = kemSuiteIdSpec k₂) : k₁ = k₂ :=
  i2osp_two_injective hk₁ hk₂ (List.append_cancel_left h)

theorem kemSuiteId_injective {kem₁ kem₂ : KemId}
    (h : kemSuiteId kem₁ = kemSuiteId kem₂) : kem₁ = kem₂ := by
  have hk₁ := ids_in_range.1 kem₁
  have hk₂ := ids_in_range.1 kem₂
  exact KemId.toInt_injective
    (toNat_inj hk₁.1 hk₂.1 (kemSuiteIdSpec_injective (by omega) (by omega) h))

/-- No string that starts with an HPKE `suite_id` starts with a KEM `suite_id`:
they differ in their first byte, `'H'` against `'K'`. -/
theorem suiteId_append_ne_kemSuiteId_append (kem : KemId) (kdf : KdfId)
    (aead : Option AeadId) (kem' : KemId) (s t : Bytes) :
    suiteId kem kdf aead ++ s ≠ kemSuiteId kem' ++ t := by
  simp [suiteId, suiteIdSpec, kemSuiteId, kemSuiteIdSpec, ascii_HPKE, ascii_KEM]

/-- The suite of RFC 9180 Appendix A.1: DHKEM(X25519, HKDF-SHA256),
HKDF-SHA256, AES-128-GCM. -/
example : suiteId .x25519 .hkdfSha256 (some .aes128Gcm) =
    [0x48, 0x50, 0x4b, 0x45, 0x00, 0x20, 0x00, 0x01, 0x00, 0x01] := by decide +kernel

/-- The ML-KEM `suite_id` values of draft-ietf-hpke-pq-05 Section 3. -/
example : kemSuiteId .mlkem512 = [0x4b, 0x45, 0x4d, 0x00, 0x40] ∧
    kemSuiteId .mlkem768 = [0x4b, 0x45, 0x4d, 0x00, 0x41] ∧
    kemSuiteId .mlkem1024 = [0x4b, 0x45, 0x4d, 0x00, 0x42] := by decide +kernel

/-- The hybrid `suite_id` values of draft-ietf-hpke-pq-05 Section 4. -/
example : kemSuiteId .mlkem768P256 = [0x4b, 0x45, 0x4d, 0x00, 0x50] ∧
    kemSuiteId .mlkem768X25519 = [0x4b, 0x45, 0x4d, 0x64, 0x7a] ∧
    kemSuiteId .mlkem1024P384 = [0x4b, 0x45, 0x4d, 0x00, 0x51] := by decide +kernel

/-! ## Labeled KDF inputs -/

/-- Mirror of the input keying material `Labeled_kdf.extract` (lines 647-648)
hands to `Kdf.extract`: `version_label ^ suite_id ^ label ^ ikm`. -/
def labeledIkm (suiteId label ikm : Bytes) : Bytes :=
  versionLabel ++ (suiteId ++ (label ++ ikm))

/-- Mirror of the `info` `Labeled_kdf.expand` (lines 650-653) hands to
`Kdf.expand_unchecked`: `i2osp2 length ^ version_label ^ suite_id ^ label ^ info`. -/
def labeledInfo (suiteId label info : Bytes) (length : Int) : Option Bytes := do
  let l ← i2osp2 length
  pure (l ++ (versionLabel ++ (suiteId ++ (label ++ info))))

/-- Mirror of the SHAKE256 input of `Labeled_kdf.kem_derive_shake256`
(lines 675-679) over a given `suite_id`: `ikm ^ version_label ^ suite_id ^
i2osp2 (String.length label) ^ label ^ i2osp2 length ^ context`. -/
def labeledDeriveInput (suiteId label context ikm : Bytes) (length : Int) :
    Option Bytes := do
  let ll ← i2osp2 label.length
  let l ← i2osp2 length
  pure (ikm ++ (versionLabel ++ (suiteId ++ (ll ++ (label ++ (l ++ context))))))

/-- Mirror of the SHAKE256 input of `Labeled_kdf.kem_derive_shake256`
(lines 675-679), which takes its `suite_id` from `kem_suite_id`. -/
def kemDeriveShake256Input (kem : KemId) (label context ikm : Bytes) (length : Int) :
    Option Bytes := do
  let s ← kemSuiteIdMirror kem
  labeledDeriveInput s label context ikm length

/-- RFC 9180 Section 4, `LabeledExtract`:
`labeled_ikm = concat("HPKE-v1", suite_id, label, ikm)`. -/
def labeledIkmSpec (suiteId label ikm : Bytes) : Bytes :=
  ascii "HPKE-v1" ++ suiteId ++ label ++ ikm

/-- RFC 9180 Section 4, `LabeledExpand`:
`labeled_info = concat(I2OSP(L, 2), "HPKE-v1", suite_id, label, info)`. -/
def labeledInfoSpec (suiteId label info : Bytes) (L : Nat) : Bytes :=
  i2osp L 2 ++ ascii "HPKE-v1" ++ suiteId ++ label ++ info

/-- draft-ietf-hpke-hpke-04 Section 3: `lengthPrefixed(x) = concat(I2OSP(len(x), 2), x)`,
an error for `x` longer than 65535 bytes. -/
def lengthPrefixed (x : Bytes) : Bytes := i2osp x.length 2 ++ x

/-- draft-ietf-hpke-hpke-04 Section 4.4, `LabeledDerive(ikm, label, context, L)`:
`labeled_ikm = concat(ikm, "HPKE-v1", suite_id, lengthPrefixed(label), I2OSP(L, 2), context)`. -/
def labeledDeriveSpec (suiteId ikm label context : Bytes) (L : Nat) : Bytes :=
  ikm ++ ascii "HPKE-v1" ++ suiteId ++ lengthPrefixed label ++ i2osp L 2 ++ context

/-- `Labeled_kdf.extract` hands the KDF RFC 9180's `labeled_ikm`. -/
theorem labeledIkm_eq_spec (suiteId label ikm : Bytes) :
    labeledIkm suiteId label ikm = labeledIkmSpec suiteId label ikm := by
  simp [labeledIkm, labeledIkmSpec, versionLabel]

/-- `Labeled_kdf.expand` hands the KDF RFC 9180's `labeled_info` whenever
`0 ≤ L < 65536`. -/
theorem labeledInfo_eq_spec (suiteId label info : Bytes) {L : Int}
    (h0 : 0 ≤ L) (h1 : L < 0x10000) :
    labeledInfo suiteId label info L = some (labeledInfoSpec suiteId label info L.toNat) := by
  simp [labeledInfo, labeledInfoSpec, versionLabel, i2osp2_of_range h0 h1]

/-- `Labeled_kdf.expand` raises exactly where `I2OSP(L, 2)` is undefined. -/
theorem labeledInfo_eq_none_iff (suiteId label info : Bytes) (L : Int) :
    labeledInfo suiteId label info L = none ↔ L < 0 ∨ 0xffff < L := by
  rw [← i2osp2_eq_none_iff]
  unfold labeledInfo
  cases i2osp2 L <;> simp

/-- `kem_derive_shake256` hands SHAKE256 the `labeled_ikm` of `LabeledDerive`
whenever the label and `L` are shorter than 65536. -/
theorem labeledDeriveInput_eq_spec (suiteId label context ikm : Bytes) {L : Int}
    (hl : label.length < 0x10000) (h0 : 0 ≤ L) (h1 : L < 0x10000) :
    labeledDeriveInput suiteId label context ikm L =
      some (labeledDeriveSpec suiteId ikm label context L.toNat) := by
  simp [labeledDeriveInput, labeledDeriveSpec, lengthPrefixed, versionLabel,
    i2osp2_nat hl, i2osp2_of_range h0 h1]

/-- `kem_derive_shake256` raises exactly where `LabeledDerive` is undefined. -/
theorem labeledDeriveInput_eq_none_iff (suiteId label context ikm : Bytes) (L : Int) :
    labeledDeriveInput suiteId label context ikm L = none ↔
      0xffff < label.length ∨ L < 0 ∨ 0xffff < L := by
  have hl := i2osp2_eq_none_iff label.length
  have hL := i2osp2_eq_none_iff L
  unfold labeledDeriveInput
  cases h₁ : i2osp2 label.length <;> cases h₂ : i2osp2 L <;> simp_all <;> omega

theorem kemDeriveShake256Input_eq_spec (kem : KemId) (label context ikm : Bytes) {L : Int}
    (hl : label.length < 0x10000) (h0 : 0 ≤ L) (h1 : L < 0x10000) :
    kemDeriveShake256Input kem label context ikm L =
      some (labeledDeriveSpec (kemSuiteId kem) ikm label context L.toNat) := by
  simp only [kemDeriveShake256Input, kemSuiteIdMirror_eq, Option.bind_eq_bind,
    Option.bind_some]
  exact labeledDeriveInput_eq_spec _ _ _ _ hl h0 h1

@[simp] theorem length_labeledIkmSpec (s l x : Bytes) :
    (labeledIkmSpec s l x).length = 7 + s.length + l.length + x.length := by
  simp [labeledIkmSpec, ascii_HPKE_v1]; omega

@[simp] theorem length_labeledInfoSpec (s l x : Bytes) (L : Nat) :
    (labeledInfoSpec s l x L).length = 9 + s.length + l.length + x.length := by
  simp [labeledInfoSpec, ascii_HPKE_v1]; omega

@[simp] theorem length_labeledDeriveSpec (s x l c : Bytes) (L : Nat) :
    (labeledDeriveSpec s x l c L).length = 11 + x.length + s.length + l.length + c.length := by
  simp [labeledDeriveSpec, lengthPrefixed, ascii_HPKE_v1]; omega

/-- Under one `suite_id`, `labeled_ikm` determines the label and the input among
labels of one length. -/
theorem labeledIkmSpec_injective {s l₁ l₂ x₁ x₂ : Bytes} (hl : l₁.length = l₂.length)
    (h : labeledIkmSpec s l₁ x₁ = labeledIkmSpec s l₂ x₂) : l₁ = l₂ ∧ x₁ = x₂ := by
  simp only [labeledIkmSpec, List.append_assoc] at h
  exact List.append_inj (List.append_cancel_left (List.append_cancel_left h)) hl

/-- The KEM's extractions and the key schedule's never hash the same input. -/
theorem labeledIkmSpec_hpke_ne_kem (kem : KemId) (kdf : KdfId) (aead : Option AeadId)
    (kem' : KemId) (l x l' x' : Bytes) :
    labeledIkmSpec (suiteId kem kdf aead) l x ≠ labeledIkmSpec (kemSuiteId kem') l' x' := by
  intro h
  simp only [labeledIkmSpec, List.append_assoc] at h
  exact suiteId_append_ne_kemSuiteId_append kem kdf aead kem' _ _
    (List.append_cancel_left h)

/-- The KEM's expansions and the key schedule's never share an `info`, for any
lengths. -/
theorem labeledInfoSpec_hpke_ne_kem (kem : KemId) (kdf : KdfId) (aead : Option AeadId)
    (kem' : KemId) (l x l' x' : Bytes) (L L' : Nat) :
    labeledInfoSpec (suiteId kem kdf aead) l x L ≠
      labeledInfoSpec (kemSuiteId kem') l' x' L' := by
  intro h
  simp only [labeledInfoSpec, List.append_assoc] at h
  have h := (List.append_inj h (by simp)).2
  exact suiteId_append_ne_kemSuiteId_append kem kdf aead kem' _ _
    (List.append_cancel_left h)

/-! ## The key-schedule context -/

/-- The constructor of `Rfc9180.mode` (lines 1019-1023), without its payload. -/
inductive ModeTag where
  | base | psk | auth | authPsk
  deriving DecidableEq, Repr

/-- The argument `Rfc9180.key_schedule` passes to `Util.byte` (lines 1040-1043). -/
def ModeTag.toInt : ModeTag → Int
  | base => 0 | psk => 1 | auth => 2 | authPsk => 3

/-- RFC 9180 Table 1: `mode_base`, `mode_psk`, `mode_auth`, `mode_auth_psk`. -/
def ModeTag.spec : ModeTag → UInt8
  | base => 0x00 | psk => 0x01 | auth => 0x02 | authPsk => 0x03

theorem ModeTag.spec_injective {m₁ m₂ : ModeTag} (h : m₁.spec = m₂.spec) : m₁ = m₂ := by
  cases m₁ <;> cases m₂ <;> first | rfl | exact absurd h (by decide)

/-- Mirror of `key_schedule_context` in `Rfc9180.key_schedule` (lines 1038-1051):
`mode_byte ^ psk_id_hash ^ info_hash`. -/
def keyScheduleContext (mode : ModeTag) (pskIdHash infoHash : Bytes) : Option Bytes := do
  let m ← byte mode.toInt
  pure (m ++ (pskIdHash ++ infoHash))

/-- RFC 9180 Section 5.1:
`key_schedule_context = concat(mode, psk_id_hash, info_hash)`. -/
def keyScheduleContextSpec (mode : UInt8) (pskIdHash infoHash : Bytes) : Bytes :=
  [mode] ++ pskIdHash ++ infoHash

/-- The mode byte never raises, and the context is RFC 9180's. -/
theorem keyScheduleContext_eq (mode : ModeTag) (pskIdHash infoHash : Bytes) :
    keyScheduleContext mode pskIdHash infoHash =
      some (keyScheduleContextSpec mode.spec pskIdHash infoHash) := by
  cases mode <;> rfl

/-- The context determines its three fields once the `psk_id_hash` lengths agree. -/
theorem keyScheduleContextSpec_injective {m₁ m₂ : UInt8} {p₁ p₂ i₁ i₂ : Bytes}
    (hp : p₁.length = p₂.length)
    (h : keyScheduleContextSpec m₁ p₁ i₁ = keyScheduleContextSpec m₂ p₂ i₂) :
    m₁ = m₂ ∧ p₁ = p₂ ∧ i₁ = i₂ := by
  simp only [keyScheduleContextSpec, List.cons_append, List.cons.injEq] at h
  exact ⟨h.1, List.append_inj h.2 hp⟩

/-- `key_schedule_context` is injective in the mode, `psk_id_hash` and
`info_hash` when both hashes are `Nh` bytes, as `LabeledExtract` outputs are. -/
theorem keyScheduleContext_injective (nh : Nat) {m₁ m₂ : ModeTag}
    {p₁ p₂ i₁ i₂ : Bytes} (hp₁ : p₁.length = nh) (hp₂ : p₂.length = nh)
    (h : keyScheduleContext m₁ p₁ i₁ = keyScheduleContext m₂ p₂ i₂) :
    m₁ = m₂ ∧ p₁ = p₂ ∧ i₁ = i₂ := by
  rw [keyScheduleContext_eq, keyScheduleContext_eq, Option.some.injEq] at h
  obtain ⟨hm, hp, hi⟩ := keyScheduleContextSpec_injective (hp₁.trans hp₂.symm) h
  exact ⟨ModeTag.spec_injective hm, hp, hi⟩

/-- Mode separation: contexts of different modes never collide, whatever the
hashes and their lengths. -/
theorem keyScheduleContext_mode_separation {m₁ m₂ : ModeTag} (hm : m₁ ≠ m₂)
    (p₁ p₂ i₁ i₂ : Bytes) :
    keyScheduleContext m₁ p₁ i₁ ≠ keyScheduleContext m₂ p₂ i₂ := by
  rw [keyScheduleContext_eq, keyScheduleContext_eq]
  intro h
  simp only [Option.some.injEq, keyScheduleContextSpec, List.cons_append,
    List.cons.injEq] at h
  exact hm (ModeTag.spec_injective h.1)

theorem length_keyScheduleContextSpec (m : UInt8) (p i : Bytes) :
    (keyScheduleContextSpec m p i).length = 1 + p.length + i.length := by
  simp [keyScheduleContextSpec]; omega

/-! ## `invalid_arg "I2OSP(2)"` is unreachable -/

/-- Every fixed label of `lib/hpke.ml`: lines 1046, 1049, 1053, 1063, 1075,
1056, 912, 685, 688, 692, 772, 773, 702. -/
def libraryLabels : List Bytes :=
  [ascii "psk_id_hash", ascii "info_hash", ascii "secret", ascii "key",
    ascii "base_nonce", ascii "exp", ascii "sec", ascii "dkp_prk",
    ascii "candidate", ascii "sk", ascii "eae_prk", ascii "shared_secret",
    ascii "DeriveKeyPair"]

theorem libraryLabels_lengths :
    libraryLabels.map List.length = [11, 9, 6, 3, 10, 3, 3, 7, 9, 2, 7, 13, 13] := by
  decide +kernel

theorem libraryLabels_short : ∀ l ∈ libraryLabels, l.length ≤ 13 := by
  decide +kernel

/-- Every call in `lib/hpke.ml` that hands a length to `Util.i2osp2`: the
`Labeled_kdf.expand` calls, direct or through `kem_expand`, and the one
`kem_derive_shake256` call. -/
inductive LengthCall where
  /-- `candidate`, lines 688-689. -/
  | candidate (kem : KemId)
  /-- `secret`, lines 692-693. -/
  | sk (kem : KemId)
  /-- the ML-KEM or hybrid seed, lines 702-703. -/
  | deriveKeyPair (kem : KemId)
  /-- `extract_and_expand`, lines 773-774. -/
  | sharedSecret (kem : KemId)
  /-- `exporter_secret`, lines 1056-1057. -/
  | exp (kdf : KdfId)
  /-- `key`, lines 1063-1065. -/
  | key (aead : AeadId)
  /-- `base_nonce`, lines 1075-1077. -/
  | baseNonce (aead : AeadId)
  /-- `Rfc9180.export`, lines 911-913, with the caller's length. -/
  | sec (kdf : KdfId) (length : Int)

namespace LengthCall

def label : LengthCall → Bytes
  | candidate _ => ascii "candidate"
  | sk _ => ascii "sk"
  | deriveKeyPair _ => ascii "DeriveKeyPair"
  | sharedSecret _ => ascii "shared_secret"
  | exp _ => ascii "exp"
  | key _ => ascii "key"
  | baseNonce _ => ascii "base_nonce"
  | sec _ _ => ascii "sec"

/-- The output length passed. -/
def length : LengthCall → Int
  | candidate kem | sk kem | deriveKeyPair kem => kem.privateKeySize
  | sharedSecret kem => kem.secretSize
  | exp kdf => kdf.hashSize
  | key aead => aead.keySize
  | baseNonce aead => aead.nonceSize
  | sec _ length => length

/-- The HKDF that expands, or `none` for SHAKE256. For an ML-KEM `kem`,
`kem_kdf` would raise; only `deriveKeyPair` is called with one. -/
def kdf : LengthCall → Option KdfId
  | candidate kem | sk kem | sharedSecret kem => kemKdf kem
  | deriveKeyPair _ => none
  | exp kdf | sec kdf _ => some kdf
  | key _ | baseNonce _ => none

/-- What holds when the call is made: only `export` checks its length first
(line 906). -/
def Guard : LengthCall → Prop
  | sec kdf length => ¬(length < 0 ∨ length > 255 * (kdf.hashSize : Int))
  | _ => True

theorem label_mem (c : LengthCall) : c.label ∈ libraryLabels := by
  cases c <;> simp [label, libraryLabels]

end LengthCall

theorem KdfId.hashSize_le (kdf : KdfId) : kdf.hashSize ≤ 64 := by
  cases kdf <;> decide

/-- `255 * Nh ≤ 16320`, the largest export length. -/
theorem KdfId.hkdfMax_le (kdf : KdfId) : 255 * kdf.hashSize ≤ 16320 := by
  cases kdf <;> decide

/-- Every length the library passes to `i2osp2` is in `[0, 65536)`. -/
theorem LengthCall.length_range (c : LengthCall) (hc : c.Guard) :
    0 ≤ c.length ∧ c.length < 0x10000 := by
  cases c with
  | candidate kem | sk kem | deriveKeyPair kem | sharedSecret kem =>
    cases kem <;> decide
  | exp kdf => cases kdf <;> decide
  | key aead | baseNonce aead => cases aead <;> decide
  | sec kdf length =>
    have := KdfId.hkdfMax_le kdf
    simp only [Guard] at hc
    simp only [LengthCall.length]
    omega

/-- The internal HKDF lengths are within RFC 5869's `L ≤ 255 * HashLen`, so
`Hkdf.expand` gets no out-of-range length either. -/
theorem LengthCall.length_le_hkdfMax (c : LengthCall) (hc : c.Guard) {kdf : KdfId}
    (hk : c.kdf = some kdf) : c.length ≤ 255 * (kdf.hashSize : Int) := by
  cases c with
  | candidate kem | sk kem | sharedSecret kem =>
    cases kem <;> simp [LengthCall.kdf, kemKdf] at hk <;> subst hk <;> decide
  | deriveKeyPair _ | key _ | baseNonce _ => simp [LengthCall.kdf] at hk
  | exp kdf' =>
    simp only [LengthCall.kdf, Option.some.injEq] at hk
    subst hk; cases kdf' <;> decide
  | sec kdf' length =>
    simp only [LengthCall.kdf, Option.some.injEq] at hk
    subst hk
    simp only [LengthCall.Guard] at hc
    simp only [LengthCall.length]
    omega

/-- `i2osp2` never raises on a library length: `Labeled_kdf.expand` and
`kem_expand` hand every call RFC 9180's `labeled_info`. -/
theorem LengthCall.labeledInfo_ok (c : LengthCall) (hc : c.Guard) (suiteId info : Bytes) :
    labeledInfo suiteId c.label info c.length =
      some (labeledInfoSpec suiteId c.label info c.length.toNat) :=
  labeledInfo_eq_spec _ _ _ (c.length_range hc).1 (c.length_range hc).2

/-- The ML-KEM and hybrid seed derivation never raises and is
draft-ietf-hpke-pq-05's `LabeledDerive(ikm, "DeriveKeyPair", "", Nsk)`. -/
theorem deriveKeyPair_input_ok (kem : KemId) (ikm : Bytes) :
    kemDeriveShake256Input kem (ascii "DeriveKeyPair") [] ikm kem.privateKeySize =
      some (labeledDeriveSpec (kemSuiteId kem) ikm (ascii "DeriveKeyPair") []
        kem.privateKeySize) := by
  have h := (LengthCall.deriveKeyPair kem).length_range trivial
  simp only [LengthCall.length] at h
  have hl : (ascii "DeriveKeyPair").length < 0x10000 := by decide +kernel
  rw [kemDeriveShake256Input_eq_spec _ _ _ _ hl h.1 h.2, Int.toNat_natCast]

/-- draft-ietf-hpke-pq-05 Section 3 derives a 64-byte seed for ML-KEM, and
Section 4 a 32-byte one for a hybrid. -/
theorem mlkem_seed_length (kem : KemId) (h : kem.isDh = false) :
    kem.privateKeySize = if kem.isHybrid then 32 else 64 := by
  cases kem <;> simp_all [KemId.isDh, KemId.isHybrid, KemId.privateKeySize]

/-- `Util.byte counter` in `candidate` never raises: `sample` counts from 0 and
stops once `counter > 255` (lines 705-706). -/
theorem candidate_byte_ok (counter : Nat) (h : ¬counter > 255) :
    byte counter = some (i2osp counter 1) := by
  rw [byte_of_range (by omega) (by omega), Int.toNat_natCast]

/-- Mirror of `Rfc9180.export` (lines 904-914) up to the KDF call: the `info`
it hands to `Kdf.expand_unchecked`, or its error. `internalError` is the
handler for an `Invalid_argument` from `i2osp2`. -/
def exportInfo (kdf : KdfId) (suiteId exporterContext : Bytes) (length : Int) :
    Except Err Bytes :=
  if length < 0 ∨ length > 255 * (kdf.hashSize : Int) then .error .exportLengthOutOfRange
  else
    match labeledInfo suiteId (ascii "sec") exporterContext length with
    | some info => .ok info
    | none => .error (.internalError "I2OSP(2)")

/-- `export` returns `Export_length_out_of_range` or RFC 9180's `labeled_info`;
its handler never sees `i2osp2` raise. -/
theorem exportInfo_eq (kdf : KdfId) (suiteId ctx : Bytes) (length : Int) :
    exportInfo kdf suiteId ctx length =
      if length < 0 ∨ length > 255 * (kdf.hashSize : Int) then
        .error .exportLengthOutOfRange
      else .ok (labeledInfoSpec suiteId (ascii "sec") ctx length.toNat) := by
  unfold exportInfo
  split
  · rfl
  · rename_i hg
    have h := (LengthCall.sec kdf length).length_range hg
    simp only [LengthCall.length] at h
    rw [labeledInfo_eq_spec _ _ _ h.1 h.2]

theorem exportInfo_ne_internalError (kdf : KdfId) (suiteId ctx : Bytes) (length : Int)
    (reason : String) : exportInfo kdf suiteId ctx length ≠ .error (.internalError reason) := by
  rw [exportInfo_eq]
  split <;> simp

/-- Mirror of the checks of `Kdf.expand` (lines 164-171); `ok` means it runs
`expand_unchecked`. -/
def kdfExpandCheck (kdf : KdfId) (prkLength : Nat) (length : Int) : Except Err Unit :=
  if prkLength < kdf.hashSize then
    .error (.invalidLength "the pseudorandom key is shorter than the hash output")
  else if length < 0 ∨ length > 255 * (kdf.hashSize : Int) then
    .error (.invalidLength "the output length is out of range")
  else .ok ()

/-- RFC 5869 Section 2.3: `HKDF-Expand(PRK, info, L)` takes a PRK of at least
`HashLen` octets and `L <= 255*HashLen`. -/
def hkdfExpandDomain (hashLen prkLength L : Nat) : Prop :=
  hashLen ≤ prkLength ∧ L ≤ 255 * hashLen

/-- `Kdf.expand` accepts exactly RFC 5869's domain, `HashLen` being `Nh`. -/
theorem kdfExpandCheck_ok_iff (kdf : KdfId) (prkLength : Nat) (length : Int) :
    kdfExpandCheck kdf prkLength length = .ok () ↔
      0 ≤ length ∧ hkdfExpandDomain kdf.hashSize prkLength length.toNat := by
  unfold kdfExpandCheck hkdfExpandDomain
  by_cases h1 : prkLength < kdf.hashSize
  · simp only [h1, ite_true, reduceCtorEq, false_iff]; omega
  · by_cases h2 : length < 0 ∨ length > 255 * (kdf.hashSize : Int)
    · simp only [h1, h2, ite_false, ite_true, reduceCtorEq, false_iff]; omega
    · simp only [h1, h2, ite_false, true_iff]; omega

/-! ## RFC 9180 input limits against OCaml strings -/

/-- The variable-length application inputs of RFC 9180 Section 7.2.1. -/
inductive AppInput where
  | psk | pskId | info | exporterContext | ikm
  deriving DecidableEq, Repr

/-- RFC 9180 Section 7.2.1, Table 4: inclusive maximum lengths in bytes. The
library checks none of them. -/
def inputLimit : KdfId → AppInput → Nat
  | .hkdfSha256, .psk => 2 ^ 61 - 88
  | .hkdfSha256, .pskId => 2 ^ 61 - 93
  | .hkdfSha256, .info => 2 ^ 61 - 91
  | .hkdfSha256, .exporterContext => 2 ^ 61 - 120
  | .hkdfSha256, .ikm => 2 ^ 61 - 84
  | .hkdfSha384, .psk => 2 ^ 125 - 152
  | .hkdfSha384, .pskId => 2 ^ 125 - 157
  | .hkdfSha384, .info => 2 ^ 125 - 155
  | .hkdfSha384, .exporterContext => 2 ^ 125 - 200
  | .hkdfSha384, .ikm => 2 ^ 125 - 148
  | .hkdfSha512, .psk => 2 ^ 125 - 152
  | .hkdfSha512, .pskId => 2 ^ 125 - 157
  | .hkdfSha512, .info => 2 ^ 125 - 155
  | .hkdfSha512, .exporterContext => 2 ^ 125 - 216
  | .hkdfSha512, .ikm => 2 ^ 125 - 148

/-- `max_size_hash_input`: FIPS 180-4 limits SHA-256 to `2^64 - 1` bits and
SHA-384 and SHA-512 to `2^128 - 1` bits; in whole bytes. -/
def maxHashInput : KdfId → Nat
  | .hkdfSha256 => (2 ^ 64 - 1) / 8
  | .hkdfSha384 | .hkdfSha512 => (2 ^ 128 - 1) / 8

/-- `Nb`, the hash block size in bytes, which HMAC's padded key occupies. -/
def hashBlockSize : KdfId → Nat
  | .hkdfSha256 => 64
  | .hkdfSha384 | .hkdfSha512 => 128

/-- The bytes hashed with an input besides the input itself: the HMAC key
block, `"HPKE-v1"`, the suite id (the KEM's for `ikm`), and the label; for
`exporter_context`, which goes through `LabeledExpand`, also `I2OSP(L, 2)`,
`T(i-1)` of up to `Nh` bytes and the counter byte. -/
def inputOverhead (kdf : KdfId) : AppInput → Nat
  | .psk => hashBlockSize kdf + versionLabel.length + 10 + (ascii "secret").length
  | .pskId => hashBlockSize kdf + versionLabel.length + 10 + (ascii "psk_id_hash").length
  | .info => hashBlockSize kdf + versionLabel.length + 10 + (ascii "info_hash").length
  | .exporterContext => hashBlockSize kdf + kdf.hashSize + 1 + 2 + versionLabel.length + 10
      + (ascii "sec").length
  | .ikm => hashBlockSize kdf + versionLabel.length + 5 + (ascii "dkp_prk").length

/-- Table 4 is Section 7.2.1's `max_size_hash_input - Nb - size_version_label -
size_suite_id - size_input_label`, with the labels the library uses. -/
theorem inputLimit_eq (kdf : KdfId) (input : AppInput) :
    inputLimit kdf input = maxHashInput kdf - inputOverhead kdf input := by
  cases kdf <;> cases input <;> decide +kernel

theorem inputLimit_ge (kdf : KdfId) (input : AppInput) : 2 ^ 61 - 120 ≤ inputLimit kdf input := by
  cases kdf <;> cases input <;> decide

/-- `Sys.max_string_length` = `word_size / 8 * max_array_length - 1` (stdlib
`sys.ml`) with `max_array_length = Max_wosize = 2^(word_size - 10 - R) - 1`
(`caml/mlvalues.h`: 8 tag bits, 2 color bits, `R` reserved header bits, 0 by
default). -/
def ocamlMaxStringLength (wordSize reserved : Nat) : Nat :=
  wordSize / 8 * (2 ^ (wordSize - 10 - reserved) - 1) - 1

/-- As printed by OCaml 5.4.1 on 64-bit: `2^57 - 9`. -/
theorem ocamlMaxStringLength_64 : ocamlMaxStringLength 64 0 = 144115188075855863 := by
  decide

/-- On 32-bit: `2^24 - 5`, about 16 MiB. -/
theorem ocamlMaxStringLength_32 : ocamlMaxStringLength 32 0 = 16777211 := by decide

theorem ocamlMaxStringLength_le (reserved : Nat) {wordSize : Nat}
    (hw : wordSize = 32 ∨ wordSize = 64) :
    ocamlMaxStringLength wordSize reserved ≤ 2 ^ 57 - 9 := by
  have hp : 2 ^ (wordSize - 10 - reserved) ≤ 2 ^ (wordSize - 10) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  unfold ocamlMaxStringLength
  rcases hw with rfl | rfl
  · have : 2 ^ (32 - 10) = 4194304 := by decide
    have := Nat.mul_le_mul_left (32 / 8) (Nat.sub_le_sub_right hp 1)
    omega
  · have : 2 ^ (64 - 10) = 18014398509481984 := by decide
    have := Nat.mul_le_mul_left (64 / 8) (Nat.sub_le_sub_right hp 1)
    omega

/-- Every OCaml string, on 32-bit or 64-bit, is shorter than every limit of
RFC 9180 Table 4, so the unchecked limits are unreachable. -/
theorem ocaml_string_within_inputLimit (reserved : Nat) {wordSize : Nat}
    (hw : wordSize = 32 ∨ wordSize = 64) (s : Bytes)
    (hs : s.length ≤ ocamlMaxStringLength wordSize reserved) (kdf : KdfId)
    (input : AppInput) : s.length < inputLimit kdf input := by
  have h1 := ocamlMaxStringLength_le reserved hw
  have h2 := inputLimit_ge kdf input
  have h3 : (2 : Nat) ^ 57 - 9 < 2 ^ 61 - 120 := by decide
  omega

/-! The converse fails on 32-bit: an input within Table 4 and within
`Sys.max_string_length` can make the labeled string that `^` builds exceed
`Sys.max_string_length`, and `^` then raises `Invalid_argument "Bytes.create"`.
The thresholds, for inputs of `n` bytes: -/

/-- `LabeledExtract(_, "info_hash", info)`: `n ≥ 16777186`. -/
theorem info_overflows_32 (kem : KemId) (kdf : KdfId) (aead : Option AeadId)
    (info : Bytes) :
    ocamlMaxStringLength 32 0 <
        (labeledIkmSpec (suiteId kem kdf aead) (ascii "info_hash") info).length ↔
      16777186 ≤ info.length := by
  have : (ascii "info_hash").length = 9 := by decide +kernel
  rw [ocamlMaxStringLength_32, length_labeledIkmSpec, length_suiteId, this]
  omega

/-- `LabeledExtract(_, "psk_id_hash", psk_id)`: `n ≥ 16777184`. -/
theorem pskId_overflows_32 (kem : KemId) (kdf : KdfId) (aead : Option AeadId)
    (pskId : Bytes) :
    ocamlMaxStringLength 32 0 <
        (labeledIkmSpec (suiteId kem kdf aead) (ascii "psk_id_hash") pskId).length ↔
      16777184 ≤ pskId.length := by
  have : (ascii "psk_id_hash").length = 11 := by decide +kernel
  rw [ocamlMaxStringLength_32, length_labeledIkmSpec, length_suiteId, this]
  omega

/-- `LabeledExtract(shared_secret, "secret", psk)`: `n ≥ 16777189`. -/
theorem psk_overflows_32 (kem : KemId) (kdf : KdfId) (aead : Option AeadId)
    (psk : Bytes) :
    ocamlMaxStringLength 32 0 <
        (labeledIkmSpec (suiteId kem kdf aead) (ascii "secret") psk).length ↔
      16777189 ≤ psk.length := by
  have : (ascii "secret").length = 6 := by decide +kernel
  rw [ocamlMaxStringLength_32, length_labeledIkmSpec, length_suiteId, this]
  omega

/-- `LabeledExpand(exporter_secret, "sec", exporter_context, L)`:
`n ≥ 16777190`. `export` turns this into `Internal_error` (line 914). -/
theorem exporterContext_overflows_32 (kem : KemId) (kdf : KdfId) (aead : Option AeadId)
    (ctx : Bytes) (L : Nat) :
    ocamlMaxStringLength 32 0 <
        (labeledInfoSpec (suiteId kem kdf aead) (ascii "sec") ctx L).length ↔
      16777190 ≤ ctx.length := by
  have : (ascii "sec").length = 3 := by decide +kernel
  rw [ocamlMaxStringLength_32, length_labeledInfoSpec, length_suiteId, this]
  omega

/-- DHKEM `LabeledExtract("", "dkp_prk", ikm)`: `n ≥ 16777193`. -/
theorem dhIkm_overflows_32 (kem : KemId) (ikm : Bytes) :
    ocamlMaxStringLength 32 0 <
        (labeledIkmSpec (kemSuiteId kem) (ascii "dkp_prk") ikm).length ↔
      16777193 ≤ ikm.length := by
  have : (ascii "dkp_prk").length = 7 := by decide +kernel
  rw [ocamlMaxStringLength_32, length_labeledIkmSpec, length_kemSuiteId, this]
  omega

/-- ML-KEM `LabeledDerive(ikm, "DeriveKeyPair", "", 64)`: `n ≥ 16777183`. -/
theorem mlkemIkm_overflows_32 (kem : KemId) (ikm : Bytes) (L : Nat) :
    ocamlMaxStringLength 32 0 <
        (labeledDeriveSpec (kemSuiteId kem) ikm (ascii "DeriveKeyPair") [] L).length ↔
      16777183 ≤ ikm.length := by
  have : (ascii "DeriveKeyPair").length = 13 := by decide +kernel
  rw [ocamlMaxStringLength_32, length_labeledDeriveSpec, length_kemSuiteId, this]
  simp only [List.length_nil]
  omega

end Hpke
