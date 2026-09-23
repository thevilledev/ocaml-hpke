import HpkeSpec.Bytes
import HpkeSpec.Registry

/-!
# Private-key handling

Mirrors of the private-key code of `lib/hpke.ml` and the specifications it
implements:

* `Util.hex_value`, `Util.of_hex_exn` and `curve_order`, against the group
  orders `n` of P-256, P-384 and P-521 (FIPS 186-5, SEC 2);
* `Util.all_zero` and `valid_nist_scalar` (with a bit-exact model of
  `Eqaf.compare_be` from eqaf 0.10), against `0 < OS2IP(sk) < n`
  (RFC 9180 Sections 7.1.2 and 7.1.3);
* the P-256/P-384/P-521 branch of `derive_key_pair_inner`, against the
  `DeriveKeyPair` rejection-sampling loop of RFC 9180 Section 7.1.3;
* `Util.normalize_x25519` and `Util.normalize_x448`, against
  `decodeScalar25519` and `decodeScalar448` of RFC 7748 Section 5;
* the byte-level part of `Private_key.of_bytes`;
* the retry loop of `generate_key_pair` for the Diffie-Hellman KEMs.

Every definition is computable, so it can be `#eval`ed to produce conformance
vectors; on a set of edge cases (orders `n - 1`, `n`, `n + 1`, zero, wrong
lengths, candidate functions that are rejected 0, 3, 255 or 256 times, empty
candidates, short X25519/X448 inputs, unequal-length comparisons) the
mirrors print exactly what the OCaml code (copied from `lib/hpke.ml` and linked
against eqaf 0.10) prints, exception messages included. OCaml's `Invalid_argument msg` is modelled as `Except.error msg`
(`OCaml.Raises`). Everything lives in `Hpke.Scalar` so that its names cannot
clash with sibling modules.
-/

set_option autoImplicit false

namespace Hpke
namespace Scalar

/-! ## OCaml primitives -/

namespace OCaml

/-- An OCaml computation that returns a value or raises `Invalid_argument msg`. -/
abbrev Raises (α : Type) := Except String α

/-- `Sys.int_size` on the 64-bit platforms the library is built for. OCaml's
`int` is then two's complement on 63 bits, modelled as `BitVec 63`. -/
def intSize : Nat := 63

/-- `Char.chr` (stdlib `char.ml`): raises outside `0 .. 255`. -/
def charChr (n : Nat) : Raises UInt8 :=
  if n > 255 then .error "Char.chr" else .ok (UInt8.ofNat n)

/-- `Bytes.get_uint8 b i` (`%bytes_safe_get`). -/
def getUint8 (b : Bytes) (i : Nat) : Raises Nat :=
  if h : i < b.length then .ok b[i].toNat else .error "index out of bounds"

/-- `Bytes.set_uint8 b i v` (`%bytes_safe_set`, which stores `v land 0xff`),
returning the updated byte string. -/
def setUint8 (b : Bytes) (i : Nat) (v : Nat) : Raises Bytes :=
  if i < b.length then .ok (b.set i (UInt8.ofNat v)) else .error "index out of bounds"

end OCaml

open OCaml

/-! ## `Eqaf.compare_be`

A transcription of `compare_be` from `eqaf.ml` (eqaf 0.10, the version in the
opam switch), with OCaml's `int` as a `BitVec w`, `w = Sys.int_size`:

```ocaml
let[@inline always] compare (a:int) b = a - b
let[@inline always] sixteen_if_minus_one_or_less n = (n asr Sys.int_size) land 16
let[@inline always] eight_if_one_or_more n = ((-n) asr Sys.int_size) land 8

let compare_be ~ln a b =
  let r = ref 0 in
  let i = ref 0 in
  while !i < ln do
    let xa = get a !i and xb = get b !i in
    let c = compare xa xb in
    r := !r lor ((sixteen_if_minus_one_or_less c + eight_if_one_or_more c) lsr !r) ;
    incr i ;
  done ;
  (!r land 8) - (!r land 16)

let compare_be a b =
  let al = String.length a in
  let bl = String.length b in
  if al < bl then 1
  else if al > bl then (-1)
  else compare_be ~ln:al (* = bl *) a b
```

Semantics (`compareBe_toInt`): on equal lengths the result is `-16`, `0` or `8`
as the big-endian value of `a` is below, equal to or above that of `b`. On
unequal lengths no byte is read and the *shorter* string compares greater
(`1`), which is the opposite of `String.compare` although `eqaf.mli` promises
the same order; `valid_nist_scalar` checks the length first, so this never
matters there. -/

namespace Eqaf

/-- `get x i = String.unsafe_get x i |> Char.code`. -/
def get (w : Nat) (x : Bytes) (i : Nat) : BitVec w := BitVec.ofNat w (x.getD i 0).toNat

/-- `compare (a:int) b = a - b`. -/
def compare {w : Nat} (a b : BitVec w) : BitVec w := a - b

/-- `sixteen_if_minus_one_or_less n = (n asr Sys.int_size) land 16`. -/
def sixteenIfMinusOneOrLess {w : Nat} (n : BitVec w) : BitVec w := n.sshiftRight w &&& 16

/-- `eight_if_one_or_more n = ((-n) asr Sys.int_size) land 8`. -/
def eightIfOneOrMore {w : Nat} (n : BitVec w) : BitVec w := (-n).sshiftRight w &&& 8

/-- The loop body's update of `r` from the difference `c`:
`r lor ((sixteen_if_minus_one_or_less c + eight_if_one_or_more c) lsr r)`. -/
def update {w : Nat} (r c : BitVec w) : BitVec w :=
  r ||| ((sixteenIfMinusOneOrLess c + eightIfOneOrMore c) >>> r)

/-- The `while !i < ln` loop of `compare_be ~ln a b`, from index `i` with
accumulator `r`. -/
def compareBeLoop (w ln : Nat) (a b : Bytes) (i : Nat) (r : BitVec w) : BitVec w :=
  if i < ln then
    let xa := get w a i
    let xb := get w b i
    let c := compare xa xb
    compareBeLoop w ln a b (i + 1) (update r c)
  else r
termination_by ln - i

/-- `compare_be ~ln a b`. -/
def compareBeLn (w ln : Nat) (a b : Bytes) : BitVec w :=
  let r := compareBeLoop w ln a b 0 0
  (r &&& 8) - (r &&& 16)

/-- `Eqaf.compare_be a b`. -/
def compareBe (w : Nat) (a b : Bytes) : BitVec w :=
  let al := a.length
  let bl := b.length
  if al < bl then 1
  else if al > bl then -1
  else compareBeLn w al a b

/-- The value `compare_be` returns, as an integer. -/
def compareBeSpec (a b : Bytes) : Int :=
  if a.length < b.length then 1
  else if b.length < a.length then -1
  else if os2ip a < os2ip b then -16
  else if os2ip b < os2ip a then 8
  else 0

/-- The facts about one integer width that the proof of `compareBe_toInt` needs,
all checked by evaluation: the loop body over every byte difference
`d - 256 ∈ [-256, 255]` and accumulator `r ∈ {0, 8, 16}`, and the final
`(r land 8) - (r land 16)`. -/
structure WidthOk (w : Nat) : Prop where
  pow : 256 ≤ 2 ^ w
  update : ∀ d, d < 512 → ∀ r ∈ [0, 8, 16],
    update (BitVec.ofNat w r) (BitVec.ofNat w (2 ^ w - 256 + d)) =
      BitVec.ofNat w (if r = 0 then (if d < 256 then 16 else if 256 < d then 8 else 0) else r)
  final : ∀ r ∈ [0, 8, 16],
    ((BitVec.ofNat w r &&& 8) - (BitVec.ofNat w r &&& 16)).toInt
      = if r = 16 then (-16 : Int) else (r : Int)
  one : (1 : BitVec w).toInt = 1
  minusOne : (-1 : BitVec w).toInt = -1

/-- 64-bit OCaml (`Sys.int_size = 63`). -/
theorem widthOk63 : WidthOk 63 := by
  constructor <;> decide +kernel

/-- 32-bit OCaml (`Sys.int_size = 31`). -/
theorem widthOk31 : WidthOk 31 := by
  constructor <;> decide +kernel

/-- 16 if the first differing byte is smaller in `a`, 8 if it is larger in `a`,
and 0 if there is none. -/
def firstDiff : Bytes → Bytes → Nat
  | x :: xs, y :: ys => if x < y then 16 else if y < x then 8 else firstDiff xs ys
  | _, _ => 0

private theorem compare_get {w : Nat} (hw : 256 ≤ 2 ^ w) (x y : UInt8) :
    compare (BitVec.ofNat w x.toNat) (BitVec.ofNat w y.toNat)
      = BitVec.ofNat w (2 ^ w - 256 + (x.toNat + 256 - y.toNat)) := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  unfold compare
  rw [BitVec.ofNat_sub_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy hw)]
  apply congrArg (BitVec.ofNat w)
  generalize 2 ^ w = P at *
  simp only [Nat.reducePow] at hx hy
  omega

private theorem get_of_lt (w : Nat) {x : Bytes} {i : Nat} (h : i < x.length) :
    get w x i = BitVec.ofNat w x[i].toNat := by
  simp [get, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

private theorem compareBeLoop_eq {w : Nat} (hw : WidthOk w) (a b : Bytes)
    (hab : a.length = b.length) :
    ∀ k i r, a.length - i = k → i ≤ a.length → (r = 0 ∨ r = 8 ∨ r = 16) →
      compareBeLoop w a.length a b i (BitVec.ofNat w r)
        = BitVec.ofNat w (if r = 0 then firstDiff (a.drop i) (b.drop i) else r) := by
  intro k
  induction k with
  | zero =>
    intro i r hk hi _
    have hia : i = a.length := by omega
    subst hia
    rw [compareBeLoop]
    simp [hab, firstDiff]
    split <;> simp_all
  | succ k ih =>
    intro i r hk hi hr
    have hia : i < a.length := by omega
    have hib : i < b.length := by omega
    rw [compareBeLoop, ite_eq_left hia]
    simp only
    rw [get_of_lt w hia, get_of_lt w hib, compare_get hw.pow]
    have hd : a[i].toNat + 256 - b[i].toNat < 512 := by
      have := a[i].toNat_lt; simp only [Nat.reducePow] at this; omega
    rw [hw.update _ hd r (by simp; omega)]
    rw [ih (i + 1) _ (by omega) (by omega)
      (by split <;> (try split) <;> (try split) <;> omega)]
    rw [List.drop_eq_getElem_cons hia, List.drop_eq_getElem_cons hib]
    simp only [firstDiff, UInt8.lt_iff_toNat_lt]
    by_cases hr0 : r = 0
    · subst hr0
      have hy := b[i].toNat_lt
      simp only [Nat.reducePow] at hy
      by_cases h1 : a[i].toNat < b[i].toNat
      · simp [h1, show a[i].toNat + 256 - b[i].toNat < 256 by omega]
      · by_cases h2 : b[i].toNat < a[i].toNat
        · simp [h1, h2, show ¬ a[i].toNat + 256 - b[i].toNat < 256 by omega,
            show 256 < a[i].toNat + 256 - b[i].toNat by omega]
        · simp [h1, h2, show ¬ a[i].toNat + 256 - b[i].toNat < 256 by omega,
            show ¬ 256 < a[i].toNat + 256 - b[i].toNat by omega]
    · simp [hr0]

theorem firstDiff_eq {a b : Bytes} (h : a.length = b.length) :
    firstDiff a b =
      if os2ip a < os2ip b then 16 else if os2ip b < os2ip a then 8 else 0 := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [firstDiff]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have hx := os2ip_lt xs
      have hy := os2ip_lt ys
      rw [h] at hx
      simp only [firstDiff, os2ip_cons, h, UInt8.lt_iff_toNat_lt]
      generalize hP : 256 ^ ys.length = P at hx hy
      by_cases h1 : x.toNat < y.toNat
      · have : (x.toNat + 1) * P ≤ y.toNat * P := Nat.mul_le_mul_right _ h1
        rw [Nat.succ_mul] at this
        simp [h1, show x.toNat * P + os2ip xs < y.toNat * P + os2ip ys by omega]
      · by_cases h2 : y.toNat < x.toNat
        · have : (y.toNat + 1) * P ≤ x.toNat * P := Nat.mul_le_mul_right _ h2
          rw [Nat.succ_mul] at this
          simp [h1, h2, show ¬ x.toNat * P + os2ip xs < y.toNat * P + os2ip ys by omega,
            show y.toNat * P + os2ip ys < x.toNat * P + os2ip xs by omega]
        · have hxy : x.toNat = y.toNat := by omega
          rw [ih h, hxy]
          simp

/-- `Eqaf.compare_be` returns exactly `compareBeSpec`, on 64-bit and on 32-bit
OCaml. -/
theorem compareBe_toInt {w : Nat} (hw : WidthOk w) (a b : Bytes) :
    (compareBe w a b).toInt = compareBeSpec a b := by
  unfold compareBe compareBeSpec
  dsimp only
  by_cases h1 : a.length < b.length
  · rw [ite_eq_left h1, ite_eq_left h1]; exact hw.one
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : b.length < a.length
    · rw [ite_eq_left (show a.length > b.length from h2), ite_eq_left h2]; exact hw.minusOne
    · have hab : a.length = b.length := by omega
      rw [ite_eq_right (show ¬ a.length > b.length from h2), ite_eq_right h2]
      unfold compareBeLn
      dsimp only
      have := compareBeLoop_eq hw a b hab a.length 0 0 (by simp) (by simp) (by simp)
      simp only [List.drop_zero, ↓reduceIte] at this
      rw [show (0 : BitVec w) = BitVec.ofNat w 0 from rfl, this, firstDiff_eq hab]
      by_cases h3 : os2ip a < os2ip b
      · rw [ite_eq_left h3, ite_eq_left h3, hw.final 16 (by simp)]; rfl
      · rw [ite_eq_right h3, ite_eq_right h3]
        by_cases h4 : os2ip b < os2ip a
        · rw [ite_eq_left h4, ite_eq_left h4, hw.final 8 (by simp)]; rfl
        · rw [ite_eq_right h4, ite_eq_right h4, hw.final 0 (by simp)]; rfl

/-- The sign `valid_nist_scalar` tests: on equal lengths `compare_be a b < 0`
exactly when `OS2IP(a) < OS2IP(b)`. -/
theorem compareBe_slt_zero {w : Nat} (hw : WidthOk w) {a b : Bytes}
    (h : a.length = b.length) :
    (compareBe w a b).slt 0 = true ↔ os2ip a < os2ip b := by
  have h0 : (0 : BitVec w).toInt = 0 := by simp
  rw [BitVec.slt_iff_toInt_lt, compareBe_toInt hw, h0]
  unfold compareBeSpec
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  by_cases h3 : os2ip a < os2ip b
  · simp [h3]
  · rw [ite_eq_right h3]
    split <;> simp_all

end Eqaf

/-! ## Hexadecimal decoding and the group orders -/

/-- `Util.hex_value` (`lib/hpke.ml` lines 297-301), on the code of an OCaml
`char`. -/
def hexValue (c : UInt8) : Raises Nat :=
  if '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat then .ok (c.toNat - '0'.toNat)
  else if 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'f'.toNat then .ok (c.toNat - 'a'.toNat + 10)
  else if 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'F'.toNat then .ok (c.toNat - 'A'.toNat + 10)
  else .error "invalid hexadecimal digit"

/-- `Util.of_hex_exn` (lines 303-308) on the bytes of an OCaml string:
`String.init (len / 2) (fun i -> Char.chr ((hex_value hex.[2i] lsl 4) lor
hex_value hex.[2i+1]))`. `String.init` calls its function on `0, 1, ...` in
order; OCaml may evaluate the two `hex_value` calls in either order, which
cannot be observed because both raise the same exception. -/
def ofHexBytes (hex : Bytes) : Raises Bytes :=
  if hex.length % 2 ≠ 0 then .error "odd hexadecimal string"
  else (List.range (hex.length / 2)).mapM fun i => do
    let hi ← hexValue (hex.getD (i * 2) 0)
    let lo ← hexValue (hex.getD (i * 2 + 1) 0)
    charChr ((hi <<< 4) ||| lo)

/-- `Util.of_hex_exn` on a string literal. -/
def ofHexExn (hex : String) : Raises Bytes := ofHexBytes (ascii hex)

/-- `curve_order` (lines 334-347), with the hexadecimal literals copied from
`lib/hpke.ml`. -/
def curveOrder : KemId → Raises Bytes
  | .p256 => ofHexExn
      "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"
  | .p384 => ofHexExn
      "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973"
  | .p521 => ofHexExn
      "01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409"
  | .x25519 => .error "X25519 has no rejection-sampling order"
  | .x448 => .error "X448 has no rejection-sampling order"
  | .mlkem512 | .mlkem768 | .mlkem1024 => .error "ML-KEM has no rejection-sampling order"

/-- The order `n` of the P-256 base point (FIPS 186-5 / SEC 2 `secp256r1`),
in decimal, from the `Order` field of `openssl ecparam -name prime256v1
-param_enc explicit -text -noout` (OpenSSL 3.6.4). -/
def p256Order : Nat :=
  115792089210356248762697446949407573529996955224135760342422259061068512044369

/-- The order `n` of the P-384 base point (`secp384r1`), from OpenSSL 3.6.4. -/
def p384Order : Nat :=
  39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643

/-- The order `n` of the P-521 base point (`secp521r1`), from OpenSSL 3.6.4. -/
def p521Order : Nat :=
  6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449

/-- The NIST-curve DHKEMs, the ones that rejection-sample their scalars. -/
def isNist : KemId → Bool
  | .p256 | .p384 | .p521 => true
  | _ => false

/-- The group order of a NIST-curve KEM (`0` for the others, where it is never
used). -/
def groupOrder : KemId → Nat
  | .p256 => p256Order
  | .p384 => p384Order
  | .p521 => p521Order
  | _ => 0

private theorem Except.eq_ok_of_toOption {ε α : Type} {e : Except ε α} {a : α}
    (h : e.toOption = some a) : e = .ok a := by
  cases e <;> simp_all [Except.toOption]

/-- The literal in `curve_order` decodes to the published P-256 order. -/
theorem curveOrder_p256 : curveOrder .p256 = .ok (i2osp p256Order 32) :=
  Except.eq_ok_of_toOption (by decide +kernel)

theorem curveOrder_p384 : curveOrder .p384 = .ok (i2osp p384Order 48) :=
  Except.eq_ok_of_toOption (by decide +kernel)

theorem curveOrder_p521 : curveOrder .p521 = .ok (i2osp p521Order 66) :=
  Except.eq_ok_of_toOption (by decide +kernel)

/-- Each order fits `Nsk` bytes, so `I2OSP(n, Nsk)` loses nothing; P-521's
order has 521 bits. -/
theorem groupOrder_bounds :
    2 ^ 255 ≤ p256Order ∧ p256Order < 2 ^ 256 ∧
    2 ^ 383 ≤ p384Order ∧ p384Order < 2 ^ 384 ∧
    2 ^ 520 ≤ p521Order ∧ p521Order < 2 ^ 521 := by
  decide +kernel

theorem groupOrder_lt (kem : KemId) (hk : isNist kem = true) :
    groupOrder kem < 256 ^ kem.privateKeySize := by
  cases kem <;> simp [isNist] at hk <;> decide +kernel

/-- `curve_order kem` is `I2OSP(n, Nsk)`: `Nsk` bytes (32, 48, 66) whose
big-endian value is the group order `n`. -/
theorem curveOrder_eq (kem : KemId) (hk : isNist kem = true) :
    curveOrder kem = .ok (i2osp (groupOrder kem) kem.privateKeySize) := by
  cases kem <;> simp [isNist] at hk
  · exact curveOrder_p256
  · exact curveOrder_p384
  · exact curveOrder_p521

theorem curveOrder_length (kem : KemId) (hk : isNist kem = true) :
    ∃ order, curveOrder kem = .ok order ∧ order.length = kem.privateKeySize ∧
      os2ip order = groupOrder kem := by
  refine ⟨_, curveOrder_eq kem hk, length_i2osp _ _, ?_⟩
  rw [os2ip_i2osp, Nat.mod_eq_of_lt (groupOrder_lt kem hk)]

/-- The decoded orders are 32, 48 and 66 bytes long. -/
theorem curveOrder_lengths :
    (curveOrder .p256).map List.length = .ok 32 ∧
    (curveOrder .p384).map List.length = .ok 48 ∧
    (curveOrder .p521).map List.length = .ok 66 := by
  rw [curveOrder_p256, curveOrder_p384, curveOrder_p521]
  simp [Except.map, length_i2osp]

/-- `Nsk` (`Kem.private_key_size`) of the NIST curves is 32, 48 and 66, the
lengths of the decoded orders. -/
theorem privateKeySize_nist :
    KemId.privateKeySize .p256 = 32 ∧ KemId.privateKeySize .p384 = 48 ∧
    KemId.privateKeySize .p521 = 66 := ⟨rfl, rfl, rfl⟩

/-! ## `Util.all_zero` -/

/-- `Util.all_zero` (lines 310-315): OR every byte into an OCaml `int`
accumulator (at most `0xff`, so it never overflows) and compare it with 0. -/
def allZero (value : Bytes) : Bool :=
  let accumulator := value.foldl (fun acc byte => acc ||| byte.toNat) 0
  accumulator == 0

private theorem foldl_lor_eq_zero (b : Bytes) (acc : Nat) :
    b.foldl (fun acc byte => acc ||| byte.toNat) acc = 0 ↔ acc = 0 ∧ ∀ x ∈ b, x = 0 := by
  induction b generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, Nat.or_eq_zero_iff]
    have : x.toNat = 0 ↔ x = 0 := by
      rw [← UInt8.toNat_inj]; rfl
    simp only [List.mem_cons, forall_eq_or_imp, this, and_assoc]

theorem os2ip_eq_zero_iff (b : Bytes) : os2ip b = 0 ↔ ∀ x ∈ b, x = 0 := by
  induction b with
  | nil => simp
  | cons x xs ih =>
    rw [os2ip_cons, Nat.add_eq_zero_iff, Nat.mul_eq_zero, ih]
    have hP : 256 ^ xs.length ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))
    have : x.toNat = 0 ↔ x = 0 := by
      rw [← UInt8.toNat_inj]; rfl
    simp only [hP, or_false, this, List.mem_cons, forall_eq_or_imp]

/-- `all_zero b` holds exactly when every byte is zero. -/
theorem allZero_iff (b : Bytes) : allZero b = true ↔ ∀ x ∈ b, x = 0 := by
  simp only [allZero, beq_iff_eq, foldl_lor_eq_zero, true_and]

/-- `all_zero b` holds exactly when `OS2IP(b) = 0`. -/
theorem allZero_iff_os2ip (b : Bytes) : allZero b = true ↔ os2ip b = 0 := by
  rw [allZero_iff, os2ip_eq_zero_iff]

/-! ## `valid_nist_scalar` -/

/-- `valid_nist_scalar` (lines 349-352), with `&&` short-circuiting left to
right, so `curve_order` is only evaluated for a nonzero string of length
`Nsk`, and `<` the signed comparison of OCaml ints. -/
def validNistScalar (kem : KemId) (bytes : Bytes) : Raises Bool :=
  if bytes.length = kem.privateKeySize then
    if !(allZero bytes) then
      match curveOrder kem with
      | .ok order => .ok ((Eqaf.compareBe intSize bytes order).slt 0)
      | .error e => .error e
    else .ok false
  else .ok false

/-- `valid_nist_scalar` never raises for a NIST curve and accepts exactly the
encodings `sk` of RFC 9180 with `0 < OS2IP(sk) < n` and `len(sk) = Nsk`. -/
theorem validNistScalar_eq (kem : KemId) (hk : isNist kem = true) (b : Bytes) :
    validNistScalar kem b =
      .ok (decide (b.length = kem.privateKeySize ∧ 0 < os2ip b ∧ os2ip b < groupOrder kem)) := by
  unfold validNistScalar
  by_cases hl : b.length = kem.privateKeySize
  · rw [ite_eq_left hl, curveOrder_eq kem hk]
    have hlen : b.length = (i2osp (groupOrder kem) kem.privateKeySize).length := by
      rw [length_i2osp, hl]
    have hcmp := Eqaf.compareBe_slt_zero (w := intSize) Eqaf.widthOk63 hlen
    rw [os2ip_i2osp, Nat.mod_eq_of_lt (groupOrder_lt kem hk)] at hcmp
    by_cases hz : allZero b = true
    · have h0 := (allZero_iff_os2ip b).mp hz
      simp [hz, h0]
    · have h0 : 0 < os2ip b := by
        rw [allZero_iff_os2ip] at hz; omega
      simp only [hz, Bool.not_false, ite_true]
      congr 1
      rw [Bool.eq_iff_iff, decide_eq_true_iff, hcmp]
      exact ⟨fun h => ⟨hl, h0, h⟩, fun h => h.2.2⟩
  · simp [hl]

/-- The statement of RFC 9180 Sections 7.1.2 and 7.1.3: `valid_nist_scalar`
holds iff `len(b) = Nsk` and `0 < OS2IP(b) < n`. -/
theorem validNistScalar_iff (kem : KemId) (hk : isNist kem = true) (b : Bytes) :
    validNistScalar kem b = .ok true ↔
      b.length = kem.privateKeySize ∧ 0 < os2ip b ∧ os2ip b < groupOrder kem := by
  rw [validNistScalar_eq kem hk]
  constructor
  · intro h
    injection h with h
    exact of_decide_eq_true h
  · intro h
    rw [decide_eq_true h]

/-! ## Byte-level facts -/

/-- A property of every byte follows from checking it on `0 .. 255`. -/
private theorem byte_cases {P : UInt8 → Prop} (h : ∀ n, n < 256 → P (UInt8.ofNat n))
    (x : UInt8) : P x := by
  have := h x.toNat x.toNat_lt
  rwa [UInt8.ofNat_toNat] at this

/-- `Bytes.set_uint8 b i (Bytes.get_uint8 b i land m)` stores `b[i] &&& m`. -/
private theorem ofNat_toNat_and (x : UInt8) (m : Nat) (hm : m < 256) :
    UInt8.ofNat (x.toNat &&& m) = x &&& UInt8.ofNat m := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_and, UInt8.toNat_ofNat', UInt8.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right hm), Nat.mod_eq_of_lt hm]

private theorem ofNat_toNat_or (x : UInt8) (m : Nat) (hm : m < 256) :
    UInt8.ofNat (x.toNat ||| m) = x ||| UInt8.ofNat m := by
  apply UInt8.toNat_inj.mp
  have hx := x.toNat_lt
  rw [UInt8.toNat_or, UInt8.toNat_ofNat', UInt8.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow hx (by simpa using hm)), Nat.mod_eq_of_lt hm]

private theorem and_ff (x : UInt8) : x &&& 0xff = x :=
  byte_cases (P := fun x => x &&& 0xff = x) (by decide +kernel) x

private theorem and_01_le (x : UInt8) : (x &&& 0x01).toNat ≤ 1 :=
  byte_cases (P := fun x => (x &&& 0x01).toNat ≤ 1) (by decide +kernel) x

/-! ## `DeriveKeyPair` for P-256, P-384 and P-521 -/

/-- Lines 709-710: for P-521 only,
`Bytes.set_uint8 candidate 0 (Bytes.get_uint8 candidate 0 land 0x01)`. -/
def maskCandidate (kem : KemId) (candidate : Bytes) : Raises Bytes :=
  if kem = .p521 then do
    let v ← getUint8 candidate 0
    setUint8 candidate 0 (v &&& 0x01)
  else .ok candidate

/-- The `sample` loop of `derive_key_pair_inner` (lines 705-715), the
P-256/P-384/P-521 branch of `secret_result`. `candidate counter` stands for
`Labeled_kdf.kem_expand kem ~prk:dkp_prk ~label:"candidate"
~info:(Util.byte counter) (Kem.private_key_size kem)` (lines 687-689), an
`Nsk`-byte string. The outer `Except String` is an escaping
`Invalid_argument`. -/
def sample (kem : KemId) (candidate : Nat → Bytes) (counter : Nat) :
    Raises (Except Err Bytes) :=
  if counter > 255 then .ok (.error .deriveKeyPairFailure)
  else
    match maskCandidate kem (candidate counter) with
    | .error e => .error e
    | .ok c =>
      match validNistScalar kem c with
      | .error e => .error e
      | .ok true => .ok (.ok c)
      | .ok false => sample kem candidate (counter + 1)
termination_by 256 - counter

/-- `bitmask` of RFC 9180 Section 7.1.3: `0xFF` for P-256 and P-384, `0x01` for
P-521. -/
def bitmask : KemId → UInt8
  | .p521 => 0x01
  | _ => 0xff

/-- The `while` loop of `DeriveKeyPair` (RFC 9180 Section 7.1.3) from the state
`(sk, counter)`, with `LabeledExpand(dkp_prk, "candidate", I2OSP(counter, 1),
Nsk)` abstracted as `candidate counter`:

```
while sk == 0 or sk >= order:
  if counter > 255:
    raise DeriveKeyPairError
  bytes = LabeledExpand(dkp_prk, "candidate", I2OSP(counter, 1), Nsk)
  bytes[0] = bytes[0] & bitmask
  sk = OS2IP(bytes)
  counter = counter + 1
return (sk, pk(sk))
```
-/
def rfcDeriveLoop (kem : KemId) (candidate : Nat → Bytes) (sk counter : Nat) :
    Except Err Nat :=
  if sk = 0 ∨ sk ≥ groupOrder kem then
    if counter > 255 then .error .deriveKeyPairFailure
    else
      let bytes := candidate counter
      let bytes := bytes.modifyHead (· &&& bitmask kem)
      let sk := os2ip bytes
      rfcDeriveLoop kem candidate sk (counter + 1)
  else .ok sk
termination_by 256 - counter

/-- The scalar `DeriveKeyPair` computes: `sk = 0`, `counter = 0`, then the
loop. -/
def rfcDeriveKeyPair (kem : KemId) (candidate : Nat → Bytes) : Except Err Nat :=
  rfcDeriveLoop kem candidate 0 0

/-- Masking the first of 66 bytes with `0x01` leaves a value below `2^521`. -/
theorem mask_p521_lt (b : Bytes) (hb : b.length = 66) :
    os2ip (b.modifyHead (· &&& 0x01)) < 2 ^ 521 := by
  cases b with
  | nil => simp at hb
  | cons x xs =>
    have hb' : xs.length = 65 := by simp at hb; omega
    simp only [List.modifyHead_cons, os2ip_cons, hb']
    have h1 := and_01_le x
    have h2 := os2ip_lt xs
    rw [hb'] at h2
    have h3 : (x &&& 0x01).toNat * 256 ^ 65 ≤ 1 * 256 ^ 65 := Nat.mul_le_mul_right _ h1
    have h4 : (2 : Nat) ^ 521 = 2 * 256 ^ 65 := by decide +kernel
    omega

/-- Masking with `0xFF` is the identity, which is why `lib/hpke.ml` masks only
for P-521. -/
theorem mask_ff (b : Bytes) : b.modifyHead (· &&& 0xff) = b := by
  cases b with
  | nil => rfl
  | cons x xs => simp [and_ff]

/-- `maskCandidate` is the RFC's `bytes[0] = bytes[0] & bitmask` on a nonempty
string of a NIST-curve KEM. -/
theorem maskCandidate_eq (kem : KemId) (hk : isNist kem = true) (b : Bytes)
    (hb : b ≠ []) : maskCandidate kem b = .ok (b.modifyHead (· &&& bitmask kem)) := by
  cases b with
  | nil => exact absurd rfl hb
  | cons x xs =>
    cases kem <;> simp [isNist] at hk
    · simp [maskCandidate, bitmask, and_ff]
    · simp [maskCandidate, bitmask, and_ff]
    · rw [maskCandidate, ite_eq_left rfl]
      show setUint8 (x :: xs) 0 (x.toNat &&& 0x01) = _
      rw [setUint8, ite_eq_left (by simp), ofNat_toNat_and x 1 (by decide)]
      rfl

private theorem rfcDeriveLoop_invalid (kem : KemId) (candidate : Nat → Bytes)
    {sk : Nat} (h : sk = 0 ∨ sk ≥ groupOrder kem) (counter : Nat) :
    rfcDeriveLoop kem candidate sk counter = rfcDeriveLoop kem candidate 0 counter := by
  unfold rfcDeriveLoop
  rw [ite_eq_left h, ite_eq_left (Or.inl rfl)]

private theorem sample_eq_rfc_from (kem : KemId) (hk : isNist kem = true)
    (candidate : Nat → Bytes) (hc : ∀ i, (candidate i).length = kem.privateKeySize) :
    ∀ k counter, 256 - counter = k →
      sample kem candidate counter
        = .ok ((rfcDeriveLoop kem candidate 0 counter).map (i2osp · kem.privateKeySize)) := by
  have hne : ∀ i, candidate i ≠ [] := by
    intro i h
    have := hc i
    rw [h] at this
    cases kem <;> simp [isNist] at hk <;> simp [KemId.privateKeySize] at this
  intro k
  induction k with
  | zero =>
    intro counter hk0
    rw [sample, rfcDeriveLoop, ite_eq_left (by omega), ite_eq_left (Or.inl rfl),
      ite_eq_left (by omega)]
    rfl
  | succ k ih =>
    intro counter hk0
    rw [sample, rfcDeriveLoop, ite_eq_right (by omega), ite_eq_left (Or.inl rfl),
      ite_eq_right (by omega), maskCandidate_eq kem hk _ (hne counter)]
    simp only
    generalize hm : (candidate counter).modifyHead (· &&& bitmask kem) = m
    have hml : m.length = kem.privateKeySize := by
      rw [← hm, List.length_modifyHead, hc]
    rw [validNistScalar_eq kem hk]
    by_cases hv : 0 < os2ip m ∧ os2ip m < groupOrder kem
    · simp only [hml, hv, and_self, decide_true]
      rw [rfcDeriveLoop, ite_eq_right (by omega)]
      simp only [Except.map]
      rw [← hml, i2osp_os2ip]
    · simp only [hml, hv, and_false, decide_false]
      rw [ih (counter + 1) (by omega),
        rfcDeriveLoop_invalid kem candidate (sk := os2ip m) (by omega) (counter + 1)]

/-- The mirror of the P-256/P-384/P-521 branch of `derive_key_pair_inner`
agrees with RFC 9180's `DeriveKeyPair` for every candidate function (every
`LabeledExpand` output of `Nsk` bytes): both fail with
`DeriveKeyPairError`, or the mirror returns `SerializePrivateKey(sk) =
I2OSP(sk, Nsk)` of the RFC's `sk`. No `Invalid_argument` escapes. -/
theorem sample_eq_rfc (kem : KemId) (hk : isNist kem = true) (candidate : Nat → Bytes)
    (hc : ∀ i, (candidate i).length = kem.privateKeySize) :
    sample kem candidate 0
      = .ok ((rfcDeriveKeyPair kem candidate).map (i2osp · kem.privateKeySize)) :=
  sample_eq_rfc_from kem hk candidate hc _ 0 rfl

/-- Any scalar the mirror returns passes `valid_nist_scalar`, whatever the
candidate function. -/
theorem sample_valid (kem : KemId) (candidate : Nat → Bytes) :
    ∀ k counter b, 256 - counter = k → sample kem candidate counter = .ok (.ok b) →
      validNistScalar kem b = .ok true := by
  intro k
  induction k with
  | zero =>
    intro counter b hk0 h
    rw [sample, ite_eq_left (by omega)] at h
    cases h
  | succ k ih =>
    intro counter b hk0 h
    rw [sample, ite_eq_right (by omega)] at h
    split at h
    · cases h
    · rename_i c _
      split at h
      · cases h
      · rename_i hv
        cases h
        exact hv
      · exact ih (counter + 1) b (by omega) h

/-- For a NIST curve a returned scalar has `Nsk` bytes and `0 < OS2IP(sk) < n`. -/
theorem sample_ok_range (kem : KemId) (hk : isNist kem = true) (candidate : Nat → Bytes)
    (b : Bytes) (h : sample kem candidate 0 = .ok (.ok b)) :
    b.length = kem.privateKeySize ∧ 0 < os2ip b ∧ os2ip b < groupOrder kem :=
  (validNistScalar_iff kem hk b).mp (sample_valid kem candidate _ 0 b rfl h)

/-- The RFC loop only returns `0 < sk < order`. -/
theorem rfcDeriveLoop_ok (kem : KemId) (candidate : Nat → Bytes) :
    ∀ k counter sk r, 256 - counter = k → rfcDeriveLoop kem candidate sk counter = .ok r →
      0 < r ∧ r < groupOrder kem := by
  intro k
  induction k with
  | zero =>
    intro counter sk r hk0 h
    rw [rfcDeriveLoop] at h
    split at h
    · rw [ite_eq_left (by omega)] at h; cases h
    · cases h; omega
  | succ k ih =>
    intro counter sk r hk0 h
    rw [rfcDeriveLoop] at h
    split at h
    · rw [ite_eq_right (by omega)] at h
      exact ih (counter + 1) _ r (by omega) h
    · cases h; omega

/-! ## X25519 and X448 clamping -/

/-- `Util.normalize_x25519` (lines 317-321). Its second update is
`Bytes.get_uint8 bytes 31 land 127 lor 64`: function application binds
tightest, and OCaml's `land` and `lor` share one precedence level (that of `*`)
and associate to the left, so this is `(b31 land 127) lor 64` as RFC 7748
intends (checked with `ocaml -dparsetree`, OCaml 5.4.1, and on all 256 byte
values). -/
def normalizeX25519 (bytes : Bytes) : Raises Bytes := do
  let v0 ← getUint8 bytes 0
  let bytes ← setUint8 bytes 0 (v0 &&& 248)
  let v31 ← getUint8 bytes 31
  setUint8 bytes 31 ((v31 &&& 127) ||| 64)

/-- `Util.normalize_x448` (lines 323-327). -/
def normalizeX448 (bytes : Bytes) : Raises Bytes := do
  let v0 ← getUint8 bytes 0
  let bytes ← setUint8 bytes 0 (v0 &&& 252)
  let v55 ← getUint8 bytes 55
  setUint8 bytes 55 (v55 ||| 128)

/-- RFC 7748 Section 5:
`decodeLittleEndian(b, bits) = sum([b[i] << 8*i for i in range((bits+7)/8)])`. -/
def decodeLittleEndian (b : Bytes) (bits : Nat) : Nat :=
  ((List.range ((bits + 7) / 8)).map fun i => (b.getD i 0).toNat <<< (8 * i)).sum

/-- RFC 7748 Section 5, `decodeScalar25519` on a 32-byte string:
```
k_list[0] &= 248
k_list[31] &= 127
k_list[31] |= 64
return decodeLittleEndian(k_list, 255)
```
-/
def decodeScalar25519 (k : Bytes) : Nat :=
  let kList := k
  let kList := kList.modify 0 (· &&& 248)
  let kList := kList.modify 31 (· &&& 127)
  let kList := kList.modify 31 (· ||| 64)
  decodeLittleEndian kList 255

/-- RFC 7748 Section 5, `decodeScalar448` on a 56-byte string:
```
k_list[0] &= 252
k_list[55] |= 128
return decodeLittleEndian(k_list, 448)
```
-/
def decodeScalar448 (k : Bytes) : Nat :=
  let kList := k
  let kList := kList.modify 0 (· &&& 252)
  let kList := kList.modify 55 (· ||| 128)
  decodeLittleEndian kList 448

/-- The clamped bytes, as pure list updates. -/
def clamp25519 (k : Bytes) : Bytes :=
  (k.modify 0 (· &&& 248)).modify 31 (fun x => (x &&& 127) ||| 64)

def clamp448 (k : Bytes) : Bytes :=
  (k.modify 0 (· &&& 252)).modify 55 (· ||| 128)

private theorem clamp25519_byte (x : UInt8) :
    UInt8.ofNat ((x.toNat &&& 127) ||| 64) = (x &&& 127) ||| 64 :=
  byte_cases (P := fun x => UInt8.ofNat ((x.toNat &&& 127) ||| 64) = (x &&& 127) ||| 64)
    (by decide +kernel) x

private theorem set_eq_modify {l : Bytes} {i : Nat} (h : i < l.length) (f : UInt8 → UInt8) :
    l.set i (f l[i]) = l.modify i f := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.getElem_set, List.getElem_modify]
  split <;> simp_all

/-- On 32 bytes `normalize_x25519` never raises and computes `clamp25519`. -/
theorem normalizeX25519_eq (b : Bytes) (hb : b.length = 32) :
    normalizeX25519 b = .ok (clamp25519 b) := by
  have h0 : 0 < b.length := by omega
  have h31 : 31 < b.length := by omega
  have e1 : setUint8 b 0 (b[0].toNat &&& 248) = .ok (b.modify 0 (· &&& 248)) := by
    rw [setUint8, ite_eq_left h0, ofNat_toNat_and _ _ (by decide)]
    exact congrArg Except.ok (set_eq_modify h0 (· &&& 248))
  have hl1 : 31 < (b.modify 0 (· &&& 248)).length := by simpa using h31
  have e2 : setUint8 (b.modify 0 (· &&& 248)) 31
      (((b.modify 0 (· &&& 248))[31]'hl1).toNat &&& 127 ||| 64) = .ok (clamp25519 b) := by
    rw [setUint8, ite_eq_left hl1, clamp25519_byte]
    exact congrArg Except.ok (set_eq_modify hl1 (fun x => (x &&& 127) ||| 64))
  simp only [normalizeX25519, getUint8, dite_eq_left h0]
  show (setUint8 b 0 (b[0].toNat &&& 248) >>= _) = _
  rw [e1]
  show (getUint8 (b.modify 0 (· &&& 248)) 31 >>= _) = _
  rw [getUint8, dite_eq_left hl1]
  exact e2

/-- On 56 bytes `normalize_x448` never raises and computes `clamp448`. -/
theorem normalizeX448_eq (b : Bytes) (hb : b.length = 56) :
    normalizeX448 b = .ok (clamp448 b) := by
  have h0 : 0 < b.length := by omega
  have h55 : 55 < b.length := by omega
  have e1 : setUint8 b 0 (b[0].toNat &&& 252) = .ok (b.modify 0 (· &&& 252)) := by
    rw [setUint8, ite_eq_left h0, ofNat_toNat_and _ _ (by decide)]
    exact congrArg Except.ok (set_eq_modify h0 (· &&& 252))
  have hl1 : 55 < (b.modify 0 (· &&& 252)).length := by simpa using h55
  have e2 : setUint8 (b.modify 0 (· &&& 252)) 55
      (((b.modify 0 (· &&& 252))[55]'hl1).toNat ||| 128) = .ok (clamp448 b) := by
    rw [setUint8, ite_eq_left hl1, ofNat_toNat_or _ _ (by decide)]
    exact congrArg Except.ok (set_eq_modify hl1 (· ||| 128))
  simp only [normalizeX448, getUint8, dite_eq_left h0]
  show (setUint8 b 0 (b[0].toNat &&& 252) >>= _) = _
  rw [e1]
  show (getUint8 (b.modify 0 (· &&& 252)) 55 >>= _) = _
  rw [getUint8, dite_eq_left hl1]
  exact e2

/-! ### Little-endian decoding -/

private theorem os2ip_reverse_cons (x : UInt8) (xs : Bytes) :
    os2ip (x :: xs).reverse = os2ip xs.reverse * 256 + x.toNat := by
  rw [List.reverse_cons, os2ip_snoc]

private theorem os2ip_reverse_take_succ (k : Bytes) (n : Nat) (h : n < k.length) :
    os2ip (k.take (n + 1)).reverse = k[n].toNat * 256 ^ n + os2ip (k.take n).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.reverse_append,
    List.reverse_singleton, List.singleton_append, os2ip_cons, List.length_reverse,
    List.length_take, Nat.min_eq_left (by omega)]

private theorem sum_range_decode (b : Bytes) (n : Nat) :
    ((List.range n).map fun i => (b.getD i 0).toNat <<< (8 * i)).sum
      = os2ip (b.take n).reverse := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h : n < b.length
    · rw [os2ip_reverse_take_succ b n h, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem h, Option.getD_some, Nat.shiftLeft_eq, Nat.pow_mul]
      simp only [Nat.reducePow]
      exact Nat.add_comm _ _
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      simp

/-- `decodeLittleEndian` of a string of exactly `(bits + 7) / 8` bytes is the
big-endian value of the reversed string. -/
theorem decodeLittleEndian_eq (b : Bytes) (bits : Nat) (hb : b.length = (bits + 7) / 8) :
    decodeLittleEndian b bits = os2ip b.reverse := by
  rw [decodeLittleEndian, sum_range_decode, List.take_of_length_le (by omega)]

/-- A little-endian value is its top byte times `256^n` plus a remainder below
`256^n`. -/
private theorem le_value_top (k : Bytes) (n : Nat) (hk : k.length = n + 1) :
    os2ip k.reverse = k[n].toNat * 256 ^ n + os2ip (k.take n).reverse ∧
      os2ip (k.take n).reverse < 256 ^ n := by
  refine ⟨?_, ?_⟩
  · have := os2ip_reverse_take_succ k n (by omega)
    rwa [List.take_of_length_le (by omega)] at this
  · have := os2ip_lt (k.take n).reverse
    rwa [List.length_reverse, List.length_take, Nat.min_eq_left (by omega)] at this

private theorem le_value_low (k : Bytes) (h : 0 < k.length) :
    ∃ A, os2ip k.reverse = A * 256 + k[0].toNat := by
  cases k with
  | nil => simp at h
  | cons x xs => exact ⟨_, os2ip_reverse_cons x xs⟩

private theorem testBit_of_bounds (s k : Nat) (h1 : 2 ^ k ≤ s) (h2 : s < 2 * 2 ^ k) :
    s.testBit k = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
  rfl

/-! ### X25519 -/

private theorem byte_and248 (x : UInt8) : (x &&& 248).toNat % 8 = 0 :=
  byte_cases (P := fun x => (x &&& 248).toNat % 8 = 0) (by decide +kernel) x

private theorem byte_top25519 (x : UInt8) :
    64 ≤ ((x &&& 127) ||| 64).toNat ∧ ((x &&& 127) ||| 64).toNat < 128 :=
  byte_cases (P := fun x => 64 ≤ ((x &&& 127) ||| 64).toNat ∧ ((x &&& 127) ||| 64).toNat < 128)
    (by decide +kernel) x

private theorem byte_idem25519 (x : UInt8) :
    (x &&& 248) &&& 248 = x &&& 248 ∧
      (((x &&& 127) ||| 64) &&& 127) ||| 64 = (x &&& 127) ||| 64 :=
  byte_cases (P := fun x => (x &&& 248) &&& 248 = x &&& 248 ∧
      (((x &&& 127) ||| 64) &&& 127) ||| 64 = (x &&& 127) ||| 64) (by decide +kernel) x

theorem length_clamp25519 (k : Bytes) : (clamp25519 k).length = k.length := by
  simp [clamp25519]

private theorem clamp25519_getElem (k : Bytes) (j : Nat) (h : j < (clamp25519 k).length) :
    (clamp25519 k)[j] =
      if j = 0 then k[j]'(by simp [clamp25519] at h; omega) &&& 248
      else if j = 31 then (k[j]'(by simp [clamp25519] at h; omega) &&& 127) ||| 64
      else k[j]'(by simp [clamp25519] at h; omega) := by
  simp only [clamp25519, List.getElem_modify]
  by_cases h0 : j = 0
  · subst h0; simp
  · by_cases h31 : j = 31
    · subst h31; simp
    · simp [h0, h31, Ne.symm h0, Ne.symm h31]

/-- RFC 7748's `decodeScalar25519` reads the bytes `normalize_x25519` stores. -/
theorem decodeScalar25519_eq (k : Bytes) :
    decodeScalar25519 k = decodeLittleEndian (clamp25519 k) 255 := by
  simp only [decodeScalar25519, clamp25519, List.modify_modify_eq]
  rfl

/-- The normalized bytes decode (little-endian) to the scalar RFC 7748's
`decodeScalar25519` produces from the original bytes. -/
theorem decode_normalizeX25519 (b : Bytes) (hb : b.length = 32) :
    (normalizeX25519 b).map (decodeLittleEndian · 255) = .ok (decodeScalar25519 b) := by
  rw [normalizeX25519_eq b hb, decodeScalar25519_eq]
  rfl

/-- `clamp25519` is idempotent (on strings of any length). -/
theorem clamp25519_idem (k : Bytes) :
    clamp25519 (clamp25519 k) = clamp25519 k := by
  apply List.ext_getElem (by simp [length_clamp25519])
  intro j h1 h2
  rw [clamp25519_getElem _ j h1, clamp25519_getElem _ j h2]
  by_cases h0 : j = 0
  · subst h0; simp [(byte_idem25519 _).1]
  · by_cases h31 : j = 31
    · subst h31; simp [(byte_idem25519 _).2]
    · simp [h0, h31]

/-- `normalize_x25519` is idempotent, so `Private_key.to_bytes` followed by
`Private_key.of_bytes` stores the same bytes. -/
theorem normalizeX25519_idem (b nb : Bytes) (hb : b.length = 32)
    (h : normalizeX25519 b = .ok nb) : normalizeX25519 nb = .ok nb := by
  rw [normalizeX25519_eq b hb] at h
  cases h
  rw [normalizeX25519_eq _ (by rw [length_clamp25519, hb]), clamp25519_idem b]

/-- The X25519 scalar is a multiple of the cofactor 8, has bit 254 set and is
below `2^255`. -/
theorem decodeScalar25519_props (b : Bytes) (hb : b.length = 32) :
    decodeScalar25519 b % 8 = 0 ∧ (decodeScalar25519 b).testBit 254 = true ∧
      2 ^ 254 ≤ decodeScalar25519 b ∧ decodeScalar25519 b < 2 ^ 255 := by
  have hl : (clamp25519 b).length = 32 := by rw [length_clamp25519, hb]
  rw [decodeScalar25519_eq, decodeLittleEndian_eq _ _ (by rw [hl])]
  have ⟨htop, hrest⟩ := le_value_top (clamp25519 b) 31 hl
  have ⟨A, hlow⟩ := le_value_low (clamp25519 b) (by omega)
  have h31 := byte_top25519 (b[31]'(by omega))
  have h0 := byte_and248 (b[0]'(by omega))
  rw [clamp25519_getElem] at htop hlow
  simp only [show (31 : Nat) ≠ 0 by decide, ite_false, ite_true] at htop hlow
  generalize hT : ((b[31]'(by omega) &&& 127) ||| 64).toNat = T at htop h31
  generalize hP : (256 : Nat) ^ 31 = P at htop hrest
  have hP1 : 64 * P ≤ T * P := Nat.mul_le_mul_right _ h31.1
  have hP2 : T * P ≤ 127 * P := Nat.mul_le_mul_right _ (by omega)
  have e1 : (2 : Nat) ^ 254 = 64 * P := by subst hP; decide +kernel
  have e2 : (2 : Nat) ^ 255 = 128 * P := by subst hP; decide +kernel
  have e3 : 2 * (2 : Nat) ^ 254 = 128 * P := by subst hP; decide +kernel
  have hlo : 2 ^ 254 ≤ os2ip (clamp25519 b).reverse := by omega
  have hhi : os2ip (clamp25519 b).reverse < 2 ^ 255 := by omega
  exact ⟨by omega, testBit_of_bounds _ _ hlo (by omega), hlo, hhi⟩

/-! ### X448 -/

private theorem byte_and252 (x : UInt8) : (x &&& 252).toNat % 4 = 0 :=
  byte_cases (P := fun x => (x &&& 252).toNat % 4 = 0) (by decide +kernel) x

private theorem byte_top448 (x : UInt8) : 128 ≤ (x ||| 128).toNat :=
  byte_cases (P := fun x => 128 ≤ (x ||| 128).toNat) (by decide +kernel) x

private theorem byte_idem448 (x : UInt8) :
    (x &&& 252) &&& 252 = x &&& 252 ∧ (x ||| 128) ||| 128 = x ||| 128 :=
  byte_cases (P := fun x => (x &&& 252) &&& 252 = x &&& 252 ∧ (x ||| 128) ||| 128 = x ||| 128)
    (by decide +kernel) x

theorem length_clamp448 (k : Bytes) : (clamp448 k).length = k.length := by
  simp [clamp448]

private theorem clamp448_getElem (k : Bytes) (j : Nat) (h : j < (clamp448 k).length) :
    (clamp448 k)[j] =
      if j = 0 then k[j]'(by simp [clamp448] at h; omega) &&& 252
      else if j = 55 then k[j]'(by simp [clamp448] at h; omega) ||| 128
      else k[j]'(by simp [clamp448] at h; omega) := by
  simp only [clamp448, List.getElem_modify]
  by_cases h0 : j = 0
  · subst h0; simp
  · by_cases h55 : j = 55
    · subst h55; simp
    · simp [h0, h55, Ne.symm h0, Ne.symm h55]

theorem decodeScalar448_eq (k : Bytes) :
    decodeScalar448 k = decodeLittleEndian (clamp448 k) 448 := rfl

/-- The normalized bytes decode (little-endian) to the scalar RFC 7748's
`decodeScalar448` produces from the original bytes. -/
theorem decode_normalizeX448 (b : Bytes) (hb : b.length = 56) :
    (normalizeX448 b).map (decodeLittleEndian · 448) = .ok (decodeScalar448 b) := by
  rw [normalizeX448_eq b hb, decodeScalar448_eq]
  rfl

theorem clamp448_idem (k : Bytes) :
    clamp448 (clamp448 k) = clamp448 k := by
  apply List.ext_getElem (by simp [length_clamp448])
  intro j h1 h2
  rw [clamp448_getElem _ j h1, clamp448_getElem _ j h2]
  by_cases h0 : j = 0
  · subst h0; simp [(byte_idem448 _).1]
  · by_cases h55 : j = 55
    · subst h55; simp [(byte_idem448 _).2]
    · simp [h0, h55]

/-- `normalize_x448` is idempotent. -/
theorem normalizeX448_idem (b nb : Bytes) (hb : b.length = 56)
    (h : normalizeX448 b = .ok nb) : normalizeX448 nb = .ok nb := by
  rw [normalizeX448_eq b hb] at h
  cases h
  rw [normalizeX448_eq _ (by rw [length_clamp448, hb]), clamp448_idem b]

/-- The X448 scalar is a multiple of the cofactor 4, has bit 447 set and is
below `2^448`. -/
theorem decodeScalar448_props (b : Bytes) (hb : b.length = 56) :
    decodeScalar448 b % 4 = 0 ∧ (decodeScalar448 b).testBit 447 = true ∧
      2 ^ 447 ≤ decodeScalar448 b ∧ decodeScalar448 b < 2 ^ 448 := by
  have hl : (clamp448 b).length = 56 := by rw [length_clamp448, hb]
  rw [decodeScalar448_eq, decodeLittleEndian_eq _ _ (by rw [hl])]
  have ⟨htop, hrest⟩ := le_value_top (clamp448 b) 55 hl
  have ⟨A, hlow⟩ := le_value_low (clamp448 b) (by omega)
  have h55 := byte_top448 (b[55]'(by omega))
  have h55' := UInt8.toNat_lt (b[55]'(by omega) ||| 128)
  have h0 := byte_and252 (b[0]'(by omega))
  rw [clamp448_getElem] at htop hlow
  simp only [show (55 : Nat) ≠ 0 by decide, ite_false, ite_true] at htop hlow
  generalize hT : (b[55]'(by omega) ||| 128).toNat = T at htop h55 h55'
  generalize hP : (256 : Nat) ^ 55 = P at htop hrest
  have hP1 : 128 * P ≤ T * P := Nat.mul_le_mul_right _ h55
  have hP2 : T * P ≤ 255 * P := Nat.mul_le_mul_right _ (by simp at h55'; omega)
  have e1 : (2 : Nat) ^ 447 = 128 * P := by subst hP; decide +kernel
  have e2 : (2 : Nat) ^ 448 = 256 * P := by subst hP; decide +kernel
  have e3 : 2 * (2 : Nat) ^ 447 = 256 * P := by subst hP; decide +kernel
  have hlo : 2 ^ 447 ≤ os2ip (clamp448 b).reverse := by omega
  have hhi : os2ip (clamp448 b).reverse < 2 ^ 448 := by omega
  exact ⟨by omega, testBit_of_bounds _ _ hlo (by omega), hlo, hhi⟩

/-! ## `Private_key.of_bytes` -/

/-- The byte-level part of `Private_key.of_bytes` (lines 568-580): the length
check, then the bytes the key stores (clamped for X25519/X448, range-checked
for the NIST curves, as given for ML-KEM), before `secret_and_public` builds the
key. -/
def privateKeyBytes (kem : KemId) (bytes : Bytes) : Raises (Except Err Bytes) :=
  if bytes.length ≠ kem.privateKeySize then
    .ok (.error (.invalidPrivateKey "wrong encoded length"))
  else
    match kem with
    | .x25519 => (normalizeX25519 bytes).map .ok
    | .x448 => (normalizeX448 bytes).map .ok
    | .p256 | .p384 | .p521 =>
      match validNistScalar kem bytes with
      | .ok true => .ok (.ok bytes)
      | .ok false => .ok (.error (.invalidPrivateKey "scalar is outside the valid range"))
      | .error e => .error e
    | .mlkem512 | .mlkem768 | .mlkem1024 => .ok (.ok bytes)

/-- `Private_key.of_bytes` never lets an `Invalid_argument` escape. -/
theorem privateKeyBytes_noRaise (kem : KemId) (b : Bytes) :
    ∃ r, privateKeyBytes kem b = .ok r := by
  unfold privateKeyBytes
  by_cases hl : b.length ≠ kem.privateKeySize
  · exact ⟨_, ite_eq_left hl⟩
  · rw [ite_eq_right hl]
    have hl' : b.length = kem.privateKeySize := Decidable.of_not_not hl
    cases kem with
    | x25519 => rw [normalizeX25519_eq b hl']; exact ⟨_, rfl⟩
    | x448 => rw [normalizeX448_eq b hl']; exact ⟨_, rfl⟩
    | p256 | p384 | p521 =>
      dsimp only
      rw [validNistScalar_eq _ rfl]
      split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
      · rename_i heq; cases heq
    | mlkem512 | mlkem768 | mlkem1024 => exact ⟨_, rfl⟩

/-- Storing is stable: the bytes `Private_key.of_bytes` stores (what
`Private_key.to_bytes` returns) are accepted again and stored unchanged. -/
theorem privateKeyBytes_stable (kem : KemId) (b nb : Bytes)
    (h : privateKeyBytes kem b = .ok (.ok nb)) : privateKeyBytes kem nb = .ok (.ok nb) := by
  unfold privateKeyBytes at h
  by_cases hl : b.length ≠ kem.privateKeySize
  · rw [ite_eq_left hl] at h; cases h
  · rw [ite_eq_right hl] at h
    have hl' : b.length = kem.privateKeySize := Decidable.of_not_not hl
    cases kem with
    | x25519 =>
      rw [normalizeX25519_eq b hl'] at h
      change Except.ok (Except.ok (clamp25519 b)) = _ at h
      injection h with h; injection h with h; subst h
      have hl2 : (clamp25519 b).length = 32 := by rw [length_clamp25519]; exact hl'
      unfold privateKeyBytes
      rw [ite_eq_right (by rw [hl2]; decide), normalizeX25519_eq _ hl2, clamp25519_idem]
      rfl
    | x448 =>
      rw [normalizeX448_eq b hl'] at h
      change Except.ok (Except.ok (clamp448 b)) = _ at h
      injection h with h; injection h with h; subst h
      have hl2 : (clamp448 b).length = 56 := by rw [length_clamp448]; exact hl'
      unfold privateKeyBytes
      rw [ite_eq_right (by rw [hl2]; decide), normalizeX448_eq _ hl2, clamp448_idem]
      rfl
    | p256 | p384 | p521 =>
      dsimp only at h
      split at h
      · rename_i hv
        injection h with h; injection h with h; subst h
        unfold privateKeyBytes
        rw [ite_eq_right hl]
        dsimp only
        rw [hv]
      · cases h
      · cases h
    | mlkem512 | mlkem768 | mlkem1024 =>
      change Except.ok (Except.ok b) = _ at h
      injection h with h; injection h with h; subst h
      unfold privateKeyBytes
      rw [ite_eq_right hl]

/-! ## `generate_key_pair` for the Diffie-Hellman KEMs -/

/-- `generate_key_pair` retries an attempt only on `Derive_key_pair_failure`. -/
def retryable {α : Type} : Except Err α → Bool
  | .error .deriveKeyPairFailure => true
  | _ => false

theorem retryable_iff {α : Type} (r : Except Err α) :
    retryable r = true ↔ r = .error .deriveKeyPairFailure := by
  cases r with
  | ok a => simp [retryable]
  | error e => cases e <;> simp [retryable]

/-- The `generate` loop of `generate_key_pair` (lines 726-733). `attempt i`
abstracts the result of the `i`-th call `derive_key_pair kem ~ikm` (on the `i`-th
`Nsk`-byte output of the RNG); `made` counts the calls so far and `attempts`
is OCaml's counter. -/
def generateLoop {α : Type} (attempt : Nat → Except Err α) (made : Nat) :
    Nat → Except Err α
  | 0 => .error .deriveKeyPairFailure
  | attempts + 1 =>
    match attempt made with
    | .ok pair => .ok pair
    | .error .deriveKeyPairFailure => generateLoop attempt (made + 1) attempts
    | .error e => .error e

/-- `generate_key_pair ~rng kem` for P-256, P-384, P-521, X25519 and X448:
`generate 8` (line 736). -/
def generateKeyPairDh {α : Type} (attempt : Nat → Except Err α) : Except Err α :=
  generateLoop attempt 0 8

/-- The specification: the first of the eight attempts that is not a
`Derive_key_pair_failure`, or `Derive_key_pair_failure` if there is none. -/
def generateSpec {α : Type} (attempt : Nat → Except Err α) : Except Err α :=
  (((List.range 8).map attempt).find? (fun r => !retryable r)).getD
    (.error .deriveKeyPairFailure)

private theorem generateLoop_eq {α : Type} (attempt : Nat → Except Err α) (n : Nat) :
    ∀ m, generateLoop attempt m n
      = (((List.range' m n).map attempt).find? (fun r => !retryable r)).getD
          (.error .deriveKeyPairFailure) := by
  induction n with
  | zero => intro m; rfl
  | succ n ih =>
    intro m
    rw [List.range'_succ, List.map_cons, List.find?_cons, generateLoop]
    cases h : attempt m with
    | ok a => simp [retryable]
    | error e => cases e <;> simp [retryable, ih]

theorem generateKeyPairDh_eq_spec {α : Type} (attempt : Nat → Except Err α) :
    generateKeyPairDh attempt = generateSpec attempt := by
  rw [generateKeyPairDh, generateLoop_eq, generateSpec, List.range_eq_range']

private theorem getElem_attempts {α : Type} (attempt : Nat → Except Err α) (i : Nat)
    (h : i < ((List.range 8).map attempt).length) :
    ((List.range 8).map attempt)[i] = attempt i := by
  simp

/-- `generate_key_pair` succeeds with `p` iff some attempt `i < 8` returns `p`
and every earlier attempt failed with `Derive_key_pair_failure`. -/
theorem generateKeyPairDh_ok_iff {α : Type} (attempt : Nat → Except Err α) (p : α) :
    generateKeyPairDh attempt = .ok p ↔
      ∃ i < 8, attempt i = .ok p ∧ ∀ j < i, attempt j = .error .deriveKeyPairFailure := by
  rw [generateKeyPairDh_eq_spec, generateSpec]
  constructor
  · intro h
    cases hf : ((List.range 8).map attempt).find? (fun r => !retryable r) with
    | none => rw [hf] at h; cases h
    | some r =>
      rw [hf] at h
      simp only [Option.getD_some] at h
      subst h
      obtain ⟨_, i, hi, hr, hj⟩ := List.find?_eq_some_iff_getElem.mp hf
      simp only [List.length_map, List.length_range] at hi
      refine ⟨i, hi, by rw [← hr, getElem_attempts], fun j hji => ?_⟩
      have := hj j hji
      rw [getElem_attempts, Bool.not_not, retryable_iff] at this
      exact this
  · rintro ⟨i, hi, hp, hj⟩
    have hf : ((List.range 8).map attempt).find? (fun r => !retryable r) = some (.ok p) := by
      rw [List.find?_eq_some_iff_getElem]
      refine ⟨by simp [retryable], i, by simpa using hi, by rw [getElem_attempts, hp],
        fun j hji => ?_⟩
      rw [getElem_attempts, Bool.not_not, retryable_iff]
      exact hj j hji
    rw [hf]; rfl

/-- `generate_key_pair` fails with an error `e` other than
`Derive_key_pair_failure` iff some attempt `i < 8` fails with `e` and every
earlier attempt failed with `Derive_key_pair_failure`: that error is
propagated at once. -/
theorem generateKeyPairDh_error_iff {α : Type} (attempt : Nat → Except Err α) (e : Err)
    (he : e ≠ .deriveKeyPairFailure) :
    generateKeyPairDh attempt = .error e ↔
      ∃ i < 8, attempt i = .error e ∧ ∀ j < i, attempt j = .error .deriveKeyPairFailure := by
  rw [generateKeyPairDh_eq_spec, generateSpec]
  have hne : retryable (Except.error e : Except Err α) = false := by
    cases h : retryable (Except.error e : Except Err α)
    · rfl
    · rw [retryable_iff] at h; injection h with h; exact absurd h he
  constructor
  · intro h
    cases hf : ((List.range 8).map attempt).find? (fun r => !retryable r) with
    | none => rw [hf] at h; injection h with h; exact absurd h.symm he
    | some r =>
      rw [hf] at h
      simp only [Option.getD_some] at h
      subst h
      obtain ⟨_, i, hi, hr, hj⟩ := List.find?_eq_some_iff_getElem.mp hf
      simp only [List.length_map, List.length_range] at hi
      refine ⟨i, hi, by rw [← hr, getElem_attempts], fun j hji => ?_⟩
      have := hj j hji
      rw [getElem_attempts, Bool.not_not, retryable_iff] at this
      exact this
  · rintro ⟨i, hi, hp, hj⟩
    have hf : ((List.range 8).map attempt).find? (fun r => !retryable r) = some (.error e) := by
      rw [List.find?_eq_some_iff_getElem]
      refine ⟨by simp [hne], i, by simpa using hi, by rw [getElem_attempts, hp],
        fun j hji => ?_⟩
      rw [getElem_attempts, Bool.not_not, retryable_iff]
      exact hj j hji
    rw [hf]; rfl

/-- `generate_key_pair` fails with `Derive_key_pair_failure` iff all eight
attempts did. -/
theorem generateKeyPairDh_dkpf_iff {α : Type} (attempt : Nat → Except Err α) :
    generateKeyPairDh attempt = .error .deriveKeyPairFailure ↔
      ∀ i < 8, attempt i = .error .deriveKeyPairFailure := by
  rw [generateKeyPairDh_eq_spec, generateSpec]
  constructor
  · intro h i hi
    cases hf : ((List.range 8).map attempt).find? (fun r => !retryable r) with
    | none =>
      have := List.find?_eq_none.mp hf (attempt i) (List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩)
      rw [Bool.not_eq_true', Bool.not_eq_false, retryable_iff] at this
      exact this
    | some r =>
      rw [hf] at h
      simp only [Option.getD_some] at h
      subst h
      have := (List.find?_eq_some_iff_getElem.mp hf).1
      simp [retryable] at this
  · intro h
    have hf : ((List.range 8).map attempt).find? (fun r => !retryable r) = none := by
      rw [List.find?_eq_none]
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      rw [h i (by simpa using hi)]
      simp [retryable]
    rw [hf]; rfl

end Scalar
end Hpke
