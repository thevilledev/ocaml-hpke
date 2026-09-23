/-
Byte strings and the integer conversions of RFC 8017 used by RFC 9180.

An OCaml `string` or `bytes` value is modelled as a list of `UInt8`, most
significant byte first. `i2osp x n` is `I2OSP(x, n)` and `os2ip` is `OS2IP`.
RFC 9180 only ever calls `I2OSP(x, n)` with `x < 256^n`; this model is total
and reduces `x` modulo `256^n`, which the lemmas below make explicit.
-/

namespace Hpke

abbrev Bytes := List UInt8

/-- `OS2IP`: the big-endian value of a byte string. -/
def os2ip (b : Bytes) : Nat :=
  b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- `I2OSP(x, n)`: the `n`-byte big-endian encoding of `x mod 256^n`. -/
def i2osp : Nat → Nat → Bytes
  | _, 0 => []
  | x, n + 1 => i2osp (x / 256) n ++ [UInt8.ofNat (x % 256)]

/-- Bytewise exclusive or, as RFC 9180's `xor` on equal-length strings. -/
def xorBytes (a b : Bytes) : Bytes := List.zipWith (· ^^^ ·) a b

/-- A byte string made of one repeated byte, OCaml's `String.make`. -/
def replicateByte (n : Nat) (b : UInt8) : Bytes := List.replicate n b

/-- ASCII text as bytes, for labels such as `"HPKE-v1"`. -/
def ascii (s : String) : Bytes := s.toUTF8.toList

private theorem foldl_os2ip (acc : Nat) (b : Bytes) :
    b.foldl (fun acc x => acc * 256 + x.toNat) acc
      = acc * 256 ^ b.length + os2ip b := by
  induction b generalizing acc with
  | nil => simp [os2ip]
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons, os2ip]
    rw [ih, ih (0 * 256 + x.toNat)]
    simp only [os2ip, Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc,
      Nat.mul_comm 256, Nat.add_assoc]

@[simp] theorem os2ip_nil : os2ip [] = 0 := rfl

theorem os2ip_append (a b : Bytes) :
    os2ip (a ++ b) = os2ip a * 256 ^ b.length + os2ip b := by
  unfold os2ip
  rw [List.foldl_append]
  exact foldl_os2ip _ b

theorem os2ip_cons (x : UInt8) (xs : Bytes) :
    os2ip (x :: xs) = x.toNat * 256 ^ xs.length + os2ip xs := by
  have := os2ip_append [x] xs
  simpa [os2ip] using this

theorem os2ip_snoc (a : Bytes) (x : UInt8) :
    os2ip (a ++ [x]) = os2ip a * 256 + x.toNat := by
  rw [os2ip_append]; simp [os2ip]

theorem os2ip_lt (b : Bytes) : os2ip b < 256 ^ b.length := by
  induction b with
  | nil => simp
  | cons x xs ih =>
    rw [os2ip_cons, List.length_cons, Nat.pow_succ]
    have h1 : x.toNat * 256 ^ xs.length ≤ 255 * 256 ^ xs.length :=
      Nat.mul_le_mul_right _ (by have := x.toNat_lt; omega)
    generalize x.toNat * 256 ^ xs.length = A at *
    generalize 256 ^ xs.length = P at *
    omega

/-- `OS2IP` is injective on strings of one length. -/
theorem os2ip_injective {a b : Bytes} (hl : a.length = b.length)
    (h : os2ip a = os2ip b) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x xs ih =>
    cases b with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      rw [os2ip_cons, os2ip_cons, hl] at h
      have hx := os2ip_lt xs
      have hy := os2ip_lt ys
      rw [hl] at hx
      -- Split `x * P + r = y * P + r'` with `r, r' < P` by division.
      have hP : 0 < 256 ^ ys.length := Nat.pow_pos (by decide)
      have hdiv : (x.toNat * 256 ^ ys.length + os2ip xs) / 256 ^ ys.length
          = (y.toNat * 256 ^ ys.length + os2ip ys) / 256 ^ ys.length := by rw [h]
      rw [Nat.mul_comm x.toNat, Nat.mul_comm y.toNat,
        Nat.mul_add_div hP, Nat.mul_add_div hP,
        Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy] at hdiv
      have hxy : x = y := UInt8.toNat_inj.mp (by simpa using hdiv)
      subst hxy
      have hrest : os2ip xs = os2ip ys := by omega
      rw [ih hl hrest]

@[simp] theorem length_i2osp (x n : Nat) : (i2osp x n).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [i2osp, ih]

theorem os2ip_i2osp (x n : Nat) : os2ip (i2osp x n) = x % 256 ^ n := by
  induction n generalizing x with
  | zero => simp [i2osp, Nat.mod_one]
  | succ n ih =>
    simp only [i2osp, os2ip_snoc, ih]
    have h : (UInt8.ofNat (x % 256)).toNat = x % 256 := by
      simp
    rw [h, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
    generalize x / 256 % 256 ^ n = A
    omega

theorem i2osp_os2ip (b : Bytes) : i2osp (os2ip b) b.length = b := by
  apply os2ip_injective (by simp)
  rw [os2ip_i2osp, Nat.mod_eq_of_lt (os2ip_lt b)]

theorem i2osp_mod (x n : Nat) : i2osp (x % 256 ^ n) n = i2osp x n := by
  have h := i2osp_os2ip (i2osp x n)
  rw [length_i2osp, os2ip_i2osp] at h
  exact h

/-- `I2OSP(·, n)` is injective on its domain `[0, 256^n)`. -/
theorem i2osp_injective {x y n : Nat} (hx : x < 256 ^ n) (hy : y < 256 ^ n)
    (h : i2osp x n = i2osp y n) : x = y := by
  have := congrArg os2ip h
  rw [os2ip_i2osp, os2ip_i2osp, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  exact this

@[simp] theorem length_xorBytes (a b : Bytes) :
    (xorBytes a b).length = min a.length b.length := by
  simp [xorBytes]

theorem xorBytes_cancel (a b : Bytes) (h : a.length = b.length) :
    xorBytes a (xorBytes a b) = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [xorBytes]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have := ih ys h
      simp only [xorBytes, List.zipWith_cons_cons] at this ⊢
      rw [this, ← UInt8.xor_assoc, UInt8.xor_self, UInt8.zero_xor]

/-- XOR with a fixed pad is injective: distinct sequence numbers give distinct
nonces under one `base_nonce`. -/
theorem xorBytes_injective {a b c : Bytes} (hb : a.length = b.length)
    (hc : a.length = c.length) (h : xorBytes a b = xorBytes a c) : b = c := by
  rw [← xorBytes_cancel a b hb, ← xorBytes_cancel a c hc, h]

end Hpke
