/-
The message sequence number of an HPKE context (`lib/hpke.ml`,
`Rfc9180.sequence_exhausted`, `increment_sequence`, `nonce`, lines 916-935).

The OCaml code keeps the sequence number as 12 mutable bytes, big-endian, and
updates them in place. The mirrors below follow the code step for step: the
exhaustion check is the `for` loop's `&&`-accumulation, the increment is the
index-driven recursion that stops at index 0, and the nonce is the `String.init`
over the indices of `base_nonce`.

The main results:

* `incrementSequence_spec`: the increment is `seq + 1 mod 256^n`;
* `sequenceExhausted_iff`: the exhaustion test holds exactly at `256^n - 1`,
  the value at which RFC 9180's `IncrementSeq` raises
  `MessageLimitReachedError`;
* `nonce_spec`: the nonce is RFC 9180's `ComputeNonce`,
  `xor(base_nonce, I2OSP(seq, Nn))`;
* `nonce_injective`: distinct sequence numbers give distinct nonces.
-/

import HpkeSpec.Bytes

namespace Hpke

/-! ## Mirrors of the OCaml functions -/

/-- `sequence_exhausted`: `exhausted := !exhausted && byte = 0xff` over every
index, starting from `true`. -/
def sequenceExhausted (s : Bytes) : Bool :=
  s.foldl (fun exhausted b => exhausted && b.toNat == 0xff) true

/-- The inner `increment index` of `increment_sequence`: store
`(value + 1) land 0xff` at `index`, and continue at `index - 1` only when the
old value was `0xff` and `index > 0`. -/
def incrementFrom (s : Bytes) : Nat → Bytes
  | 0 =>
    let value := s.getD 0 0
    s.set 0 (UInt8.ofNat ((value.toNat + 1) &&& 0xff))
  | index + 1 =>
    let value := s.getD (index + 1) 0
    let s' := s.set (index + 1) (UInt8.ofNat ((value.toNat + 1) &&& 0xff))
    if value.toNat = 0xff then incrementFrom s' index else s'

/-- `increment_sequence`: `increment (Bytes.length sequence - 1)`. -/
def incrementSequence (s : Bytes) : Bytes := incrementFrom s (s.length - 1)

/-- `nonce`: `String.init (String.length base_nonce) (fun index ->
base_nonce.[index] lxor Bytes.get_uint8 sequence index)`. -/
def nonceOf (baseNonce seq : Bytes) : Bytes :=
  (List.range baseNonce.length).map fun index =>
    baseNonce.getD index 0 ^^^ seq.getD index 0

/-- The sequence number of a fresh context: `Bytes.make 12 '\000'`. -/
def initialSequence : Bytes := List.replicate 12 0

/-! ## Specification (RFC 9180, Section 5.2) -/

/-- `ComputeNonce(seq) = xor(base_nonce, I2OSP(seq, Nn))`. -/
def computeNonce (baseNonce : Bytes) (seq : Nat) : Bytes :=
  xorBytes baseNonce (i2osp seq baseNonce.length)

/-- The largest sequence number, `(1 << (8*Nn)) - 1`. -/
def maxSeq (n : Nat) : Nat := 256 ^ n - 1

/-! ## Positional arithmetic -/

private theorem byte_succ_land (v : UInt8) :
    (UInt8.ofNat ((v.toNat + 1) &&& 0xff)).toNat = (v.toNat + 1) % 256 := by
  have h : (v.toNat + 1) &&& 0xff = (v.toNat + 1) % 256 := by
    have := Nat.and_two_pow_sub_one_eq_mod (v.toNat + 1) 8
    simpa using this
  rw [h]; simp

private theorem set_eq_take_cons_drop (s : Bytes) (k : Nat) (x : UInt8)
    (hk : k < s.length) : s.set k x = s.take k ++ x :: s.drop (k + 1) := by
  simp [List.set_eq_take_append_cons_drop, hk]

private theorem eq_take_cons_drop (s : Bytes) (k : Nat) (hk : k < s.length) :
    s = s.take k ++ s[k] :: s.drop (k + 1) := by
  conv => lhs; rw [← List.take_append_drop k s]
  rw [List.drop_eq_getElem_cons hk]

/-- `os2ip` split at position `k`: the prefix, the digit, and the suffix. -/
private theorem os2ip_split (s : Bytes) (k : Nat) (x : UInt8) :
    os2ip (s.take k ++ x :: s.drop (k + 1))
      = os2ip (s.take k) * (256 * 256 ^ (s.length - 1 - k))
        + x.toNat * 256 ^ (s.length - 1 - k) + os2ip (s.drop (k + 1)) := by
  rw [os2ip_append, os2ip_cons]
  simp only [List.length_cons, List.length_drop]
  have : s.length - (k + 1) = s.length - 1 - k := by omega
  rw [this, Nat.pow_succ, Nat.mul_comm (256 ^ _) 256, Nat.add_assoc]

private theorem getD_eq_getElem (s : Bytes) (k : Nat) (hk : k < s.length) :
    s.getD k 0 = s[k] := by
  simp [List.getD, List.getElem?_eq_getElem hk]

/-- `os2ip s` split around its digit at index `k`. -/
private theorem os2ip_eq_split (s : Bytes) (k : Nat) (hk : k < s.length) :
    os2ip s = os2ip (s.take k) * (256 * 256 ^ (s.length - 1 - k))
        + s[k].toNat * 256 ^ (s.length - 1 - k) + os2ip (s.drop (k + 1)) := by
  have := os2ip_split s k s[k]
  rw [← eq_take_cons_drop s k hk] at this
  exact this

/-- Adding `c * P` to a number whose digit at weight `P` is `v`, with the
digit's successor still a digit, stays below `256^n`. -/
private theorem no_overflow {T M Q P v R : Nat} (hT : T < M) (hQ : Q = 256 * P)
    (hv : v + 1 < 256) (hR : R < P) :
    T * Q + (v + 1) * P + R < M * Q := by
  have h1 : T * Q + Q ≤ M * Q := by
    have := Nat.mul_le_mul_right Q (show T + 1 ≤ M by omega)
    rwa [Nat.succ_mul] at this
  have h2 : (v + 1) * P ≤ 255 * P := Nat.mul_le_mul_right P (by omega)
  generalize T * Q = TQ at *
  generalize M * Q = MQ at *
  generalize (v + 1) * P = vP at *
  omega

theorem length_incrementFrom (s : Bytes) (i : Nat) :
    (incrementFrom s i).length = s.length := by
  induction i generalizing s with
  | zero => simp [incrementFrom]
  | succ i ih =>
    simp only [incrementFrom]
    split <;> simp [ih]

/-- The recursion adds one unit at position `i` (weight `256^(n-1-i)`), with
the carry running towards index 0 and dropped there. -/
theorem os2ip_incrementFrom (s : Bytes) (i : Nat) (hi : i < s.length) :
    os2ip (incrementFrom s i)
      = (os2ip s + 256 ^ (s.length - 1 - i)) % 256 ^ s.length := by
  induction i generalizing s with
  | zero =>
    simp only [incrementFrom]
    rw [getD_eq_getElem s 0 hi, set_eq_take_cons_drop s 0 _ hi, os2ip_split,
      os2ip_eq_split s 0 hi]
    simp only [List.take_zero, os2ip_nil, Nat.zero_mul, Nat.zero_add, Nat.sub_zero,
      byte_succ_land]
    have hR := os2ip_lt (s.drop 1)
    simp only [List.length_drop] at hR
    have hn : 256 ^ s.length = 256 * 256 ^ (s.length - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    rw [hn]
    generalize 256 ^ (s.length - 1) = P at *
    generalize os2ip (s.drop 1) = R at *
    have hv := s[0].toNat_lt
    generalize s[0].toNat = v at *
    by_cases h255 : v = 255
    · subst h255
      simp only [show (255 + 1) % 256 = 0 by rfl, Nat.zero_mul, Nat.zero_add]
      rw [show 255 * P + R + P = R + 256 * P by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show R < 256 * P by omega)]
    · rw [Nat.mod_eq_of_lt (show v + 1 < 256 by omega)]
      have h2 : (v + 1) * P ≤ 255 * P := Nat.mul_le_mul_right P (by omega)
      rw [Nat.succ_mul] at h2
      rw [Nat.mod_eq_of_lt (by omega), Nat.succ_mul]
      omega
  | succ i ih =>
    have hk : i + 1 < s.length := hi
    simp only [incrementFrom]
    rw [getD_eq_getElem s (i + 1) hk]
    have hT := os2ip_lt (s.take (i + 1))
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at hT
    have hR := os2ip_lt (s.drop (i + 1 + 1))
    simp only [List.length_drop] at hR
    have hRw : s.length - (i + 1 + 1) = s.length - 1 - (i + 1) := by omega
    rw [hRw] at hR
    have hn : 256 ^ s.length
        = 256 ^ (i + 1) * (256 * 256 ^ (s.length - 1 - (i + 1))) := by
      rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
    have hw : 256 ^ (s.length - 1 - i) = 256 * 256 ^ (s.length - 1 - (i + 1)) := by
      rw [← Nat.pow_succ']; congr 1; omega
    split
    · -- The digit was `0xff`: it becomes 0 and the carry moves left.
      rename_i h255
      have hlen : (s.set (i + 1) (UInt8.ofNat ((s[i + 1].toNat + 1) &&& 0xff))).length
          = s.length := by simp
      rw [ih _ (by rw [hlen]; omega), hlen]
      rw [set_eq_take_cons_drop s (i + 1) _ hk, os2ip_split, byte_succ_land, h255,
        os2ip_eq_split s (i + 1) hk, h255, hw]
      congr 1
      simp only [show (255 + 1) % 256 = 0 by rfl, Nat.zero_mul, Nat.add_zero]
      omega
    · -- No carry: the digit is incremented in place, without overflow.
      rename_i h255
      rw [set_eq_take_cons_drop s (i + 1) _ hk, os2ip_split, byte_succ_land,
        os2ip_eq_split s (i + 1) hk]
      have hv := s[i + 1].toNat_lt
      rw [Nat.mod_eq_of_lt (show s[i + 1].toNat + 1 < 256 by omega), hn]
      generalize os2ip (s.take (i + 1)) = T at *
      generalize os2ip (s.drop (i + 1 + 1)) = R at *
      generalize 256 ^ (s.length - 1 - (i + 1)) = P at *
      generalize 256 ^ (i + 1) = M at *
      generalize s[i + 1].toNat = v at *
      have hlt := no_overflow (Q := 256 * P) hT rfl (show v + 1 < 256 by omega) hR
      have e1 : (v + 1) * P = v * P + P := Nat.succ_mul v P
      rw [Nat.mod_eq_of_lt (by omega)]
      omega

/-! ## The increment -/

/-- `increment_sequence` computes `seq + 1 mod 256^n`. -/
theorem os2ip_incrementSequence (s : Bytes) (hs : 0 < s.length) :
    os2ip (incrementSequence s) = (os2ip s + 1) % 256 ^ s.length := by
  unfold incrementSequence
  rw [os2ip_incrementFrom s _ (by omega)]
  simp [show s.length - 1 - (s.length - 1) = 0 by omega]

theorem length_incrementSequence (s : Bytes) :
    (incrementSequence s).length = s.length := length_incrementFrom _ _

/-- The increment is `I2OSP(seq + 1, n)`, which wraps to zero only from the
exhausted value. -/
theorem incrementSequence_spec (s : Bytes) (hs : 0 < s.length) :
    incrementSequence s = i2osp (os2ip s + 1) s.length := by
  apply os2ip_injective (by simp [length_incrementSequence])
  rw [os2ip_incrementSequence s hs, os2ip_i2osp]

/-- In terms of sequence numbers: `I2OSP(q, n) ↦ I2OSP(q + 1, n)`. -/
theorem incrementSequence_i2osp (q n : Nat) (hn : 0 < n) (hq : q + 1 < 256 ^ n) :
    incrementSequence (i2osp q n) = i2osp (q + 1) n := by
  have hq' : q < 256 ^ n := by omega
  have := incrementSequence_spec (i2osp q n) (by simpa using hn)
  rw [this, os2ip_i2osp, Nat.mod_eq_of_lt hq', length_i2osp]

/-! ## Exhaustion -/

private theorem foldl_and (s : Bytes) (b : Bool) :
    s.foldl (fun exhausted x => exhausted && x.toNat == 0xff) b
      = (b && s.all (fun x => x.toNat == 0xff)) := by
  induction s generalizing b with
  | nil => simp
  | cons x xs ih => simp [ih, Bool.and_assoc]

theorem sequenceExhausted_iff_all (s : Bytes) :
    sequenceExhausted s = true ↔ ∀ x ∈ s, x.toNat = 0xff := by
  simp [sequenceExhausted, foldl_and]

theorem all_ff_iff (s : Bytes) :
    (∀ x ∈ s, x.toNat = 0xff) ↔ os2ip s = maxSeq s.length := by
  unfold maxSeq
  induction s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mem_cons, forall_eq_or_imp, os2ip_cons, List.length_cons, Nat.pow_succ]
    have hP : 0 < 256 ^ xs.length := Nat.pow_pos (by decide)
    have hR := os2ip_lt xs
    have hx := x.toNat_lt
    constructor
    · rintro ⟨h1, h2⟩
      rw [h1, ih.mp h2]
      generalize 256 ^ xs.length = P at *
      omega
    · intro h
      -- A digit below 255 leaves the total below `256^(k+1) - 1`.
      have h255 : x.toNat = 255 := by
        refine Classical.byContradiction fun hne => ?_
        have : x.toNat * 256 ^ xs.length ≤ 254 * 256 ^ xs.length :=
          Nat.mul_le_mul_right _ (by omega)
        generalize 256 ^ xs.length = P at *
        generalize x.toNat * P = xP at *
        omega
      refine ⟨h255, ih.mpr ?_⟩
      rw [h255] at h
      generalize 256 ^ xs.length = P at *
      omega

/-- `sequence_exhausted` holds exactly at `(1 << (8*Nn)) - 1`. -/
theorem sequenceExhausted_iff (s : Bytes) :
    sequenceExhausted s = true ↔ os2ip s = maxSeq s.length :=
  (sequenceExhausted_iff_all s).trans (all_ff_iff s)

theorem sequenceExhausted_i2osp (q n : Nat) (hq : q < 256 ^ n) :
    sequenceExhausted (i2osp q n) = true ↔ q = maxSeq n := by
  rw [sequenceExhausted_iff, os2ip_i2osp, Nat.mod_eq_of_lt hq, length_i2osp]

/-! ## The nonce -/

theorem nonceOf_eq_xorBytes (baseNonce seq : Bytes)
    (h : baseNonce.length = seq.length) :
    nonceOf baseNonce seq = xorBytes baseNonce seq := by
  apply List.ext_getElem
  · simp [nonceOf, xorBytes, h]
  · intro i h1 h2
    simp only [nonceOf, List.length_map, List.length_range] at h1
    simp [nonceOf, xorBytes, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem (show i < seq.length by omega)]

/-- The OCaml nonce is RFC 9180's `ComputeNonce`. -/
theorem nonce_spec (baseNonce : Bytes) (q : Nat) :
    nonceOf baseNonce (i2osp q baseNonce.length) = computeNonce baseNonce q :=
  nonceOf_eq_xorBytes _ _ (by simp)

/-- Under one `base_nonce`, distinct in-range sequence numbers give distinct
nonces. Together with the context model this rules out nonce reuse. -/
theorem nonce_injective (baseNonce : Bytes) {p q : Nat}
    (hp : p < 256 ^ baseNonce.length) (hq : q < 256 ^ baseNonce.length)
    (h : computeNonce baseNonce p = computeNonce baseNonce q) : p = q :=
  i2osp_injective hp hq (xorBytes_injective (by simp) (by simp) h)

/-! ## The initial state -/

theorem initialSequence_eq : initialSequence = i2osp 0 12 := by decide

theorem initialSequence_not_exhausted : sequenceExhausted initialSequence = false := by
  decide

end Hpke
