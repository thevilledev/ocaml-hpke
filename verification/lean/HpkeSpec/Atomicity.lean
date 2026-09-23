/-
The sequence number between byte writes (`lib/hpke.ml`,
`Rfc9180.increment_sequence`, lines 923-929).

`Context.lean` treats `increment_sequence` as one atomic step. On OCaml 5 it is
not: the recursive `increment` polls in its prologue (native arm64 code:
`ldr x16, [x28]; cmp x27, x16; b.ls caml_call_gc`), and every self tail call
jumps back to that poll after storing a byte. At a poll, pending signals run
their OCaml handlers, and a handler may raise (`Sys.Break`, a timeout on
`SIGALRM`, ...). `Fun.protect` then releases the context and re-raises; the
sequence keeps whatever bytes were stored so far.

This file models every state the sequence passes through, one per byte store.

* `increment_rolls_back`: the shipped code passes through states *below* the
  old sequence number. From `.. 00 ff`, it first stores `00` into the last
  byte, so an exception at the next poll leaves the sequence 255 lower, and the
  next seals reuse the nonces of 255 messages already sent.
* `fixed_never_below`: storing the carried byte first and then clearing the
  trailing `0xff` bytes (`incrementFixed`) passes only through states at or
  above the new sequence number. An interrupted increment can skip sequence
  numbers but never repeat one, wherever the polls are.
* `incrementFixed_eq_all`: the fixed increment computes the same value as the
  shipped one on every non-empty sequence, so the fix changes only the order
  of the stores.
-/

import HpkeSpec.Sequence

namespace Hpke

/-! ## The shipped code, store by store -/

/-- The states `increment index` leaves after each `Bytes.set_uint8`, in
order; the last is `incrementFrom s index`. -/
def incrementStores (s : Bytes) : Nat → List Bytes
  | 0 =>
    let value := s.getD 0 0
    [s.set 0 (UInt8.ofNat ((value.toNat + 1) &&& 0xff))]
  | index + 1 =>
    let value := s.getD (index + 1) 0
    let s' := s.set (index + 1) (UInt8.ofNat ((value.toNat + 1) &&& 0xff))
    if value.toNat = 0xff then s' :: incrementStores s' index else [s']

theorem incrementStores_last (s : Bytes) (i : Nat) :
    (incrementStores s i).getLast? = some (incrementFrom s i) := by
  induction i generalizing s with
  | zero => rfl
  | succ i ih =>
    simp only [incrementStores, incrementFrom]
    split
    · rw [List.getLast?_cons, ih]; rfl
    · rfl

/-- The witness: a two-byte sequence `00 ff` (value 255) is first stored as
`00 00` (value 0). With twelve bytes the same happens at every carry. -/
theorem increment_rolls_back :
    let s : Bytes := [0x00, 0xff]
    sequenceExhausted s = false ∧
    ∃ t ∈ incrementStores s (s.length - 1), os2ip t < os2ip s := by
  refine ⟨by decide, [0x00, 0x00], by decide, by decide⟩

/-- In the shipped 12-byte sequence: at `2^8 - 1 = 255`, the first store
takes the sequence back to 0. -/
theorem increment_rolls_back_12 :
    ∃ t ∈ incrementStores (i2osp 255 12) 11, os2ip t = 0 ∧ os2ip (i2osp 255 12) = 255 := by
  refine ⟨i2osp 0 12, by decide, by decide, by decide⟩

/-! ## The fix: carry first, then clear -/

/-- The index that takes the carry: the last byte below `0xff`, or 0.
`let rec carry index = if Bytes.get_uint8 sequence index < 0xff || index = 0
then index else carry (index - 1)`. -/
def carryIndex (s : Bytes) : Nat → Nat
  | 0 => 0
  | index + 1 => if (s.getD (index + 1) 0).toNat < 0xff then index + 1 else carryIndex s index

/-- The two stores of the fixed `increment_sequence`: `Bytes.set_uint8` of the
carried byte, then `Bytes.fill` of the bytes after it with zeros. -/
def incrementFixedStores (s : Bytes) : List Bytes :=
  let index := carryIndex s (s.length - 1)
  let s1 := s.set index (UInt8.ofNat (((s.getD index 0).toNat + 1) &&& 0xff))
  let s2 := s1.take (index + 1) ++ List.replicate (s.length - index - 1) 0
  [s1, s2]

def incrementFixed (s : Bytes) : Bytes := (incrementFixedStores s).getLast!

theorem carryIndex_le (s : Bytes) (i : Nat) : carryIndex s i ≤ i := by
  induction i with
  | zero => simp [carryIndex]
  | succ i ih => simp only [carryIndex]; split <;> omega

/-- Every byte after the carry index is `0xff`. -/
private theorem carryIndex_suffix (s : Bytes) (i : Nat) (hi : i < s.length) :
    ∀ j, carryIndex s i < j → j ≤ i → (s.getD j 0).toNat = 0xff := by
  induction i with
  | zero => intro j h1 h2; simp [carryIndex] at h1; omega
  | succ i ih =>
    intro j h1 h2
    simp only [carryIndex] at h1
    split at h1
    · omega
    · rename_i hlt
      by_cases hj : j = i + 1
      · subst hj; have := (s.getD (i + 1) 0).toNat_lt; omega
      · exact ih (by omega) j h1 (by omega)

/-- The carried byte is below `0xff`, unless the carry reached index 0. -/
private theorem carryIndex_byte (s : Bytes) (i : Nat) :
    carryIndex s i = 0 ∨ (s.getD (carryIndex s i) 0).toNat < 0xff := by
  induction i with
  | zero => simp [carryIndex]
  | succ i ih => simp only [carryIndex]; split <;> simp_all

private theorem getD_eq_getElem' (s : Bytes) (k : Nat) (hk : k < s.length) :
    s.getD k 0 = s[k] := by
  simp [List.getD, List.getElem?_eq_getElem hk]

/-- The trailing run of `0xff` bytes is `256^k - 1`. -/
private theorem os2ip_all_ff (l : Bytes) (h : ∀ x ∈ l, x.toNat = 0xff) :
    os2ip l = 256 ^ l.length - 1 := by
  have := (all_ff_iff l).mp h
  simpa [maxSeq] using this

private theorem os2ip_zeros (k : Nat) : os2ip (List.replicate k (0 : UInt8)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, os2ip_cons, ih]; simp

/-- `incrementFixedStores` with the carry index named. -/
private theorem stores_eq (s : Bytes) (c : Nat) (hc : c = carryIndex s (s.length - 1)) :
    incrementFixedStores s =
      [s.set c (UInt8.ofNat (((s.getD c 0).toNat + 1) &&& 0xff)),
       (s.set c (UInt8.ofNat (((s.getD c 0).toNat + 1) &&& 0xff))).take (c + 1)
         ++ List.replicate (s.length - c - 1) 0] := by
  subst hc; rfl

/-- A byte below `0xff` increments without wrapping. -/
private theorem succ_byte (x : UInt8) (hx : x.toNat < 0xff) :
    (UInt8.ofNat ((x.toNat + 1) &&& 0xff)).toNat = x.toNat + 1 := by
  have : (x.toNat + 1) &&& 0xff = x.toNat + 1 := by
    rw [show (0xff : Nat) = 2 ^ 8 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (by omega)
  rw [this]; simp; omega

/-- The decomposition `s = P ++ [x] ++ F` around the carry index `c`, with `F`
the `k` trailing `0xff` bytes, and the values of the two stores. -/
private theorem stores_values (s : Bytes) (c : Nat) (hcdef : c = carryIndex s (s.length - 1))
    (hs : 0 < s.length) (hx : (s.getD c 0).toNat < 0xff) :
    os2ip s = os2ip (s.take c) * (256 * 256 ^ (s.length - 1 - c))
        + (s.getD c 0).toNat * 256 ^ (s.length - 1 - c) + (256 ^ (s.length - 1 - c) - 1) ∧
    os2ip ((incrementFixedStores s)[0]!) = os2ip (s.take c) * (256 * 256 ^ (s.length - 1 - c))
        + ((s.getD c 0).toNat + 1) * 256 ^ (s.length - 1 - c) + (256 ^ (s.length - 1 - c) - 1) ∧
    os2ip ((incrementFixedStores s)[1]!) = os2ip (s.take c) * (256 * 256 ^ (s.length - 1 - c))
        + ((s.getD c 0).toNat + 1) * 256 ^ (s.length - 1 - c) := by
  have hc : c < s.length := by have := carryIndex_le s (s.length - 1); omega
  have hsuf : ∀ x ∈ s.drop (c + 1), x.toNat = 0xff := by
    intro x hx'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx'
    simp only [List.length_drop] at hj
    rw [List.getElem_drop]
    have := carryIndex_suffix s (s.length - 1) (by omega) (c + 1 + j) (by omega) (by omega)
    rwa [getD_eq_getElem' s _ (by omega)] at this
  have hF := os2ip_all_ff _ hsuf
  simp only [List.length_drop] at hF
  rw [show s.length - (c + 1) = s.length - 1 - c by omega] at hF
  have hv := succ_byte (s.getD c 0) hx
  have hsplit : s = s.take c ++ s[c] :: s.drop (c + 1) := by
    conv => lhs; rw [← List.take_append_drop c s]
    rw [List.drop_eq_getElem_cons hc]
  have hset : ∀ v : UInt8, s.set c v = s.take c ++ v :: s.drop (c + 1) := by
    intro v; simp [List.set_eq_take_append_cons_drop, hc]
  rw [stores_eq s c hcdef]
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
  refine ⟨?_, ?_, ?_⟩
  · conv => lhs; rw [hsplit]
    rw [os2ip_append, os2ip_cons, hF, getD_eq_getElem' s c hc]
    simp only [List.length_cons, List.length_drop, Nat.pow_succ]
    rw [show s.length - (c + 1) = s.length - 1 - c by omega, Nat.mul_comm (256 ^ _) 256]
    omega
  · rw [hset, os2ip_append, os2ip_cons, hF, hv]
    simp only [List.length_cons, List.length_drop, Nat.pow_succ]
    rw [show s.length - (c + 1) = s.length - 1 - c by omega, Nat.mul_comm (256 ^ _) 256]
    omega
  · have ht : (s.take c ++ UInt8.ofNat (((s.getD c 0).toNat + 1) &&& 0xff) :: s.drop (c + 1)).take (c + 1)
        = s.take c ++ [UInt8.ofNat (((s.getD c 0).toNat + 1) &&& 0xff)] := by
      have hlen : (s.take c).length = c := by simp; omega
      rw [List.take_append, hlen, List.take_of_length_le (by rw [hlen]; omega),
        show c + 1 - c = 1 by omega]
      rfl
    rw [hset, ht, os2ip_append, os2ip_zeros, os2ip_snoc, hv]
    simp only [List.length_replicate, Nat.add_zero]
    rw [show s.length - c - 1 = s.length - 1 - c by omega, Nat.add_mul, Nat.mul_assoc]

/-- A non-exhausted sequence has a byte below `0xff` at the carry index. -/
private theorem carry_byte_lt (s : Bytes) (hs : 0 < s.length)
    (hne : sequenceExhausted s = false) :
    (s.getD (carryIndex s (s.length - 1)) 0).toNat < 0xff := by
  rcases carryIndex_byte s (s.length - 1) with h | h
  · rw [h]
    refine Classical.byContradiction fun hge => ?_
    have hall : ∀ j < s.length, (s.getD j 0).toNat = 0xff := by
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0; have := (s.getD 0 0).toNat_lt; omega
      · exact carryIndex_suffix s (s.length - 1) (by omega) j (by rw [h]; omega) (by omega)
    have : sequenceExhausted s = true := by
      rw [sequenceExhausted_iff_all]
      intro x hx'
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx'
      have := hall j hj
      rwa [getD_eq_getElem' s j hj] at this
    simp_all
  · exact h

/-- The fixed increment computes `seq + 1` below the limit... -/
theorem incrementFixed_spec (s : Bytes) (hs : 0 < s.length)
    (hne : sequenceExhausted s = false) :
    os2ip (incrementFixed s) = os2ip s + 1 := by
  have hx := carry_byte_lt s hs hne
  obtain ⟨h0, -, h2⟩ := stores_values s _ rfl hs hx
  have : incrementFixed s = (incrementFixedStores s)[1]! := rfl
  rw [this, h2, h0]
  have hP := Nat.pow_pos (n := s.length - 1 - carryIndex s (s.length - 1)) (by decide : 0 < 256)
  generalize os2ip (List.take _ s) * _ = A
  generalize 256 ^ _ = P at *
  rw [Nat.succ_mul]; omega

/-- ...and no intermediate state is below the new value. -/
theorem fixed_never_below (s : Bytes) (hs : 0 < s.length)
    (hne : sequenceExhausted s = false) :
    ∀ t ∈ incrementFixedStores s, os2ip s + 1 ≤ os2ip t := by
  have hx := carry_byte_lt s hs hne
  obtain ⟨h0, h1, h2⟩ := stores_values s _ rfl hs hx
  have hP := Nat.pow_pos (n := s.length - 1 - carryIndex s (s.length - 1)) (by decide : 0 < 256)
  intro t ht
  have e1 : t = (incrementFixedStores s)[0]! ∨ t = (incrementFixedStores s)[1]! := by
    have hlen : incrementFixedStores s = [(incrementFixedStores s)[0]!, (incrementFixedStores s)[1]!] := rfl
    rw [hlen] at ht
    simpa using ht
  rcases e1 with rfl | rfl
  · rw [h1, h0]
    generalize os2ip (List.take _ s) * _ = A
    generalize 256 ^ _ = P at *
    rw [Nat.succ_mul]; omega
  · rw [h2, h0]
    generalize os2ip (List.take _ s) * _ = A
    generalize 256 ^ _ = P at *
    rw [Nat.succ_mul]; omega

/-- The fixed increment agrees with the shipped one wherever the context
calls it (below the limit). -/
theorem incrementFixed_eq (s : Bytes) (hs : 0 < s.length)
    (hne : sequenceExhausted s = false) :
    incrementFixed s = incrementSequence s := by
  have hlen2 : (incrementFixed s).length = s.length := by
    simp only [incrementFixed, incrementFixedStores]
    have := carryIndex_le s (s.length - 1)
    simp [List.getLast!, List.length_take]; omega
  apply os2ip_injective (by rw [hlen2, length_incrementSequence])
  rw [incrementFixed_spec s hs hne, os2ip_incrementSequence s hs]
  have hlt : os2ip s < maxSeq s.length := by
    have := os2ip_lt s
    have hne' : os2ip s ≠ maxSeq s.length := by
      intro h; rw [← sequenceExhausted_iff] at h; simp_all
    unfold maxSeq at *; omega
  unfold maxSeq at hlt
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem carryIndex_all_ff (s : Bytes) (i : Nat) (hi : i < s.length)
    (h : ∀ j < s.length, (s.getD j 0).toNat = 0xff) : carryIndex s i = 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hb := h (i + 1) hi
    simp only [carryIndex, hb]
    exact ih (by omega)

private theorem os2ip_zero_prefix (k : Nat) : os2ip ([0] ++ List.replicate k (0 : UInt8)) = 0 := by
  rw [os2ip_append, os2ip_zeros]; simp [os2ip]

/-- The fixed increment computes exactly what the shipped one does, on every
non-empty sequence: below the limit by `incrementFixed_eq`, and at the limit
both wrap to zero. The context never increments at the limit. -/
theorem incrementFixed_eq_all (s : Bytes) (hs : 0 < s.length) :
    incrementFixed s = incrementSequence s := by
  cases hne : sequenceExhausted s with
  | false => exact incrementFixed_eq s hs hne
  | true =>
    have hall := (sequenceExhausted_iff_all s).mp hne
    have hall' : ∀ j < s.length, (s.getD j 0).toNat = 0xff := fun j hj => by
      rw [getD_eq_getElem' s j hj]; exact hall _ (List.getElem_mem hj)
    have hc := carryIndex_all_ff s (s.length - 1) (by omega) hall'
    have h0 : s.getD 0 0 = 0xff := UInt8.toNat_inj.mp (by rw [hall' 0 hs]; rfl)
    have hfix : incrementFixed s = [0] ++ List.replicate (s.length - 1) 0 := by
      simp only [incrementFixed, incrementFixedStores, hc, h0]
      obtain ⟨x, xs, rfl⟩ : ∃ x xs, s = x :: xs := by
        cases s with
        | nil => simp at hs
        | cons x xs => exact ⟨x, xs, rfl⟩
      simp [List.getLast!]
    apply os2ip_injective (by rw [hfix, length_incrementSequence]; simp; omega)
    rw [hfix, os2ip_zero_prefix, os2ip_incrementSequence s hs,
      (sequenceExhausted_iff s).mp hne]
    unfold maxSeq
    have : 0 < 256 ^ s.length := Nat.pow_pos (by decide)
    rw [Nat.sub_add_cancel this, Nat.mod_self]

end Hpke
