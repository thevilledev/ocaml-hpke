/-
AEAD plaintext limits (`lib/hpke.ml`, `Aead.plaintext_fits`, lines 200-207, and
its callers `Aead.seal`/`Aead.open_`, lines 265-282, and
`Rfc9180.seal`/`open_ciphertext`, lines 942-972).

Specifications:

* AES-GCM, NIST SP 800-38D Section 5.2.1.1: `len(P) ≤ 2^39 - 256` bits. With a
  96-bit IV the plaintext is encrypted under the 32-bit counters
  `inc32(J0) = 2, 3, ...`; the bound is exactly the condition that the counter
  never wraps back to 0 or 1 (1 masks the tag). RFC 5116 Section 5.1 prints
  `P_MAX = 2^36 - 31` octets, which erratum 5219 corrects to `2^36 - 32`.
* ChaCha20-Poly1305, RFC 8439 Section 2.8 (RFC 7539 erratum 4858): the
  keystream uses the 32-bit block counters `1, 2, ...`, so
  `P_MAX = (2^32 - 1) * 64 = 2^38 - 64` octets.

The dependency: mirage-crypto 2.4 rejects AES-GCM inputs of more than
`2^32 - 2` blocks and ChaCha20 inputs of more than `2^32 - 1` blocks by raising
`Invalid_argument` (`Cipher_block.Counters.C128be32.check_blocks`,
`Chacha20.check_aead_blocks_and_key`, with `(//)` rounding up).

Finding (proved below as `gcm_limit_off_by_one` and `seal_contract_violated`):
`plaintext_fits` accepts an AES-GCM plaintext of exactly `2^36 - 31` bytes. That
is one byte beyond SP 800-38D; mirage-crypto then raises, and `Aead.seal` and
`Rfc9180.Sender.seal` return `Internal_error "CTR: too many blocks"` where
`hpke.mli` promises `Plaintext_too_long`. `plaintextFitsFixed` (bound
`2^36 - 32`) is proved exact for both AEADs.
-/

import HpkeSpec.Registry

namespace Hpke

/-! ## The mirror -/

/-- The bound `Aead.plaintext_fits` compares against (as `Int64`). -/
def plaintextMax : AeadId → Nat
  | .aes128Gcm | .aes256Gcm => 2 ^ 36 - 31
  | .chacha20Poly1305 => 2 ^ 38 - 64

/-- `Aead.plaintext_fits id length`: `Int64.compare length maximum <= 0`.
Lengths are OCaml string lengths, hence non-negative and below `2^62`, so the
`Int64` comparison is the comparison of naturals. -/
def plaintextFits (id : AeadId) (length : Nat) : Bool := length ≤ plaintextMax id

/-! ## The block counters -/

/-- mirage-crypto's `x // y`, integer division rounding up. -/
def ceilDiv (x y : Nat) : Nat := if x > 0 then 1 + (x - 1) / y else 0

/-- The 32-bit GCM counter values used to encrypt `len` bytes under a 96-bit
IV: `inc32` applied `i + 1` times to `J0 = IV || 0^31 || 1`, for each block. -/
def gcmCounters (len : Nat) : List Nat :=
  (List.range (ceilDiv len 16)).map fun i => (2 + i) % 2 ^ 32

/-- The ChaCha20 block counters of RFC 8439's AEAD for `len` bytes. -/
def chachaCounters (len : Nat) : List Nat :=
  (List.range (ceilDiv len 64)).map fun i => (1 + i) % 2 ^ 32

/-- SP 800-38D's requirement: no GCM counter wraps (so none repeats and none
equals the tag counter 1 or wraps to 0). -/
def gcmNoWrap (len : Nat) : Prop := ∀ i < ceilDiv len 16, 2 + i < 2 ^ 32

/-- RFC 8439's requirement: no ChaCha20 block counter wraps. -/
def chachaNoWrap (len : Nat) : Prop := ∀ i < ceilDiv len 64, 1 + i < 2 ^ 32

/-- mirage-crypto's GCM check: `check_block_count 0xfffffffeL (len // 16)`. -/
def mirageGcmAccepts (len : Nat) : Bool := ceilDiv len 16 ≤ 0xfffffffe

/-- mirage-crypto's ChaCha20 check (32-byte key, 12-byte nonce):
`Int64.of_int (len // 64) > 0xffffffffL` raises. -/
def mirageChachaAccepts (len : Nat) : Bool := ceilDiv len 64 ≤ 0xffffffff

/-- What the dependency accepts, per AEAD. -/
def mirageAccepts : AeadId → Nat → Bool
  | .aes128Gcm | .aes256Gcm => mirageGcmAccepts
  | .chacha20Poly1305 => mirageChachaAccepts

/-- The standards' maximum plaintext length, in bytes. -/
def specPMax : AeadId → Nat
  | .aes128Gcm | .aes256Gcm => (2 ^ 39 - 256) / 8
  | .chacha20Poly1305 => (2 ^ 32 - 1) * 64

theorem specPMax_values :
    specPMax .aes128Gcm = 2 ^ 36 - 32 ∧ specPMax .chacha20Poly1305 = 2 ^ 38 - 64 := by
  decide

private theorem ceilDiv_le_iff (len d k : Nat) (hd : 0 < d) :
    ceilDiv len d ≤ k ↔ len ≤ d * k := by
  unfold ceilDiv
  split
  · constructor
    · intro h
      have := Nat.lt_mul_div_succ (len - 1) hd
      have h2 : d * ((len - 1) / d + 1) ≤ d * k := Nat.mul_le_mul_left d (by omega)
      rw [Nat.mul_succ] at this h2
      omega
    · intro h
      have : (len - 1) / d < k := by
        apply Nat.div_lt_of_lt_mul
        omega
      omega
  · constructor <;> intro <;> omega

/-- The no-wrap condition is exactly SP 800-38D's `2^36 - 32` bytes. -/
theorem gcmNoWrap_iff (len : Nat) : gcmNoWrap len ↔ len ≤ 2 ^ 36 - 32 := by
  unfold gcmNoWrap
  have key := ceilDiv_le_iff len 16 (2 ^ 32 - 2) (by decide)
  constructor
  · intro h
    apply (show len ≤ 16 * (2 ^ 32 - 2) → len ≤ 2 ^ 36 - 32 by intro h; omega)
    apply key.mp
    refine Classical.byContradiction fun hne => ?_
    have := h (2 ^ 32 - 2) (by omega)
    omega
  · intro h i hi
    have := key.mpr (by omega)
    omega

theorem chachaNoWrap_iff (len : Nat) : chachaNoWrap len ↔ len ≤ 2 ^ 38 - 64 := by
  unfold chachaNoWrap
  have key := ceilDiv_le_iff len 64 (2 ^ 32 - 1) (by decide)
  constructor
  · intro h
    apply (show len ≤ 64 * (2 ^ 32 - 1) → len ≤ 2 ^ 38 - 64 by intro h; omega)
    apply key.mp
    refine Classical.byContradiction fun hne => ?_
    have := h (2 ^ 32 - 1) (by omega)
    omega
  · intro h i hi
    have := key.mpr (by omega)
    omega

/-- The spec bound is the no-wrap bound. -/
theorem specPMax_is_noWrap (len : Nat) :
    (gcmNoWrap len ↔ len ≤ specPMax .aes128Gcm) ∧
    (chachaNoWrap len ↔ len ≤ specPMax .chacha20Poly1305) := by
  rw [specPMax_values.1, specPMax_values.2]
  exact ⟨gcmNoWrap_iff len, chachaNoWrap_iff len⟩

/-- Without a wrap the counters are pairwise distinct and avoid the tag's 1. -/
theorem gcmCounters_nodup (len : Nat) (h : gcmNoWrap len) :
    (gcmCounters len).Nodup ∧ 1 ∉ gcmCounters len ∧ 0 ∉ gcmCounters len := by
  unfold gcmCounters
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_congr_left (g := fun i => 2 + i)
      (fun i hi => Nat.mod_eq_of_lt (h i (List.mem_range.mp hi)))]
    unfold List.Nodup
    rw [List.pairwise_map]
    exact List.nodup_range.imp fun hab => by omega
  · simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi
    rw [Nat.mod_eq_of_lt (h i hi)]; omega
  · simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi
    rw [Nat.mod_eq_of_lt (h i hi)]; omega

/-- mirage-crypto's checks are exactly the standards' limits. -/
theorem mirageAccepts_iff (id : AeadId) (len : Nat) :
    mirageAccepts id len = true ↔ len ≤ specPMax id := by
  have g := ceilDiv_le_iff len 16 0xfffffffe (by decide)
  have c := ceilDiv_le_iff len 64 0xffffffff (by decide)
  cases id <;>
  simp only [mirageAccepts, mirageGcmAccepts, mirageChachaAccepts, specPMax,
    decide_eq_true_eq] <;> omega

/-! ## The defect -/

/-- `plaintext_fits` accepts one AES-GCM length beyond SP 800-38D, and only one. -/
theorem gcm_limit_off_by_one (id : AeadId) (hid : id = .aes128Gcm ∨ id = .aes256Gcm) :
    plaintextFits id (2 ^ 36 - 31) = true ∧ ¬ gcmNoWrap (2 ^ 36 - 31) ∧
    ∀ len, plaintextFits id len = true ∧ ¬ gcmNoWrap len → len = 2 ^ 36 - 31 := by
  rcases hid with rfl | rfl <;>
  refine ⟨by decide, by rw [gcmNoWrap_iff]; omega, fun len ⟨h1, h2⟩ => ?_⟩ <;>
  have h1 := of_decide_eq_true h1 <;>
  simp only [plaintextMax] at h1 <;>
  rw [gcmNoWrap_iff] at h2 <;> omega

/-- ChaCha20-Poly1305's bound is exact. -/
theorem chacha_limit_exact (len : Nat) :
    plaintextFits .chacha20Poly1305 len = true ↔ chachaNoWrap len := by
  rw [chachaNoWrap_iff]
  exact ⟨of_decide_eq_true, decide_eq_true⟩

/-! ## `Aead.seal`'s error contract

`Aead.seal key ~nonce ~aad ~plaintext` (lines 265-271): wrong nonce length,
then `Plaintext_too_long` unless `plaintext_fits`, then `encrypt`, which turns
the dependency's `Invalid_argument` into `Internal_error`. With a correct nonce
its outcome depends only on the length. -/

inductive SealOutcome where
  | ciphertext
  | plaintextTooLong
  | internalError
  deriving DecidableEq, Repr

/-- The outcome of `Aead.seal` (and of `Rfc9180.seal` below its message limit)
for a plaintext of `len` bytes and a well-formed nonce. -/
def sealOutcome (fits : AeadId → Nat → Bool) (id : AeadId) (len : Nat) : SealOutcome :=
  if !fits id len then .plaintextTooLong
  else if !mirageAccepts id len then .internalError
  else .ciphertext

/-- The documented contract (`hpke.mli`): `Plaintext_too_long` beyond the
AEAD's limit, a ciphertext within it, never an internal error. -/
def sealContract (outcome : AeadId → Nat → SealOutcome) : Prop :=
  ∀ id len, outcome id len = if len ≤ specPMax id then .ciphertext else .plaintextTooLong

/-- The shipped bound breaks the contract at `2^36 - 31` bytes. -/
theorem seal_contract_violated :
    sealOutcome plaintextFits .aes128Gcm (2 ^ 36 - 31) = .internalError ∧
    ¬ sealContract (sealOutcome plaintextFits) := by
  refine ⟨by decide, fun h => ?_⟩
  have := h .aes128Gcm (2 ^ 36 - 31)
  revert this
  decide

/-- The corrected bound, `2^36 - 32` for AES-GCM. -/
def plaintextMaxFixed : AeadId → Nat
  | .aes128Gcm | .aes256Gcm => 2 ^ 36 - 32
  | .chacha20Poly1305 => 2 ^ 38 - 64

def plaintextFitsFixed (id : AeadId) (length : Nat) : Bool :=
  length ≤ plaintextMaxFixed id

theorem plaintextMaxFixed_eq_spec (id : AeadId) : plaintextMaxFixed id = specPMax id := by
  cases id <;> decide

/-- With the corrected bound the contract holds for every AEAD and length. -/
theorem seal_contract_fixed : sealContract (sealOutcome plaintextFitsFixed) := by
  intro id len
  unfold sealOutcome plaintextFitsFixed
  rw [plaintextMaxFixed_eq_spec]
  by_cases h : len ≤ specPMax id
  · have := (mirageAccepts_iff id len).mpr h
    simp [h, this]
  · simp [h]

/-! ## Opening

`Aead.open_` and `Rfc9180.open_ciphertext` reject a ciphertext shorter than the
tag or whose plaintext part does not fit, as `Open_error`, before decrypting.
-/

/-- The length precondition both open paths check. -/
def openLengthOk (fits : AeadId → Nat → Bool) (id : AeadId) (ctLen : Nat) : Bool :=
  !(ctLen < id.tagSize || !fits id (ctLen - id.tagSize))

/-- With the shipped bound, one AES-GCM ciphertext length passes the check and
then makes mirage-crypto raise; `decrypt` maps that to `Open_error`, so the
open contract (`Open_error` for malformed ciphertexts) still holds. -/
theorem open_boundary :
    openLengthOk plaintextFits .aes128Gcm (2 ^ 36 - 31 + 16) = true ∧
    mirageAccepts .aes128Gcm (2 ^ 36 - 31) = false := by
  decide

theorem openLengthOk_fixed (id : AeadId) (ctLen : Nat) :
    openLengthOk plaintextFitsFixed id ctLen = true →
      mirageAccepts id (ctLen - id.tagSize) = true := by
  intro h
  simp only [openLengthOk, plaintextFitsFixed, Bool.not_or, Bool.not_not,
    Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
  rw [mirageAccepts_iff, ← plaintextMaxFixed_eq_spec]
  exact h.2

end Hpke
