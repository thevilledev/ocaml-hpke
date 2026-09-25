/-
Generates `verification/conformance/vectors.txt`: inputs and the outputs the
Lean mirrors compute for them. `verification/conformance/conformance.ml`
replays every line against the real `lib/hpke.ml`, so a mirror that does not
transcribe the OCaml code faithfully fails `dune runtest`.

Run from `verification/lean`:

    lake env lean --run Conformance.lean > ../conformance/vectors.txt

Line format: a tag, then space-separated fields; byte strings are lowercase
hexadecimal, `-` is the empty string.
-/

import HpkeSpec.Registry
import HpkeSpec.Sequence
import HpkeSpec.AeadLimits
import HpkeSpec.Encoding
import HpkeSpec.Scalar
import HpkeSpec.Setup

open Hpke

namespace Conformance

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!

def hex (b : Bytes) : String :=
  if b.isEmpty then "-" else String.ofList (b.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit x.toNat])

def bool (b : Bool) : String := if b then "1" else "0"

/-- splitmix64, for reproducible pseudo-random inputs. -/
def mix (x : Nat) : Nat :=
  let m := 2 ^ 64
  let z := (x + 0x9e3779b97f4a7c15) % m
  let z := ((z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9) % m
  let z := ((z ^^^ (z >>> 27)) * 0x94d049bb133111eb) % m
  z ^^^ (z >>> 31)

def randBytes (seed n : Nat) : Bytes :=
  (List.range n).map fun i => UInt8.ofNat (mix (seed * 1000003 + i))

def kemName : KemId → String
  | .p256 => "p256" | .p384 => "p384" | .p521 => "p521" | .x25519 => "x25519"
  | .x448 => "x448" | .mlkem512 => "mlkem512" | .mlkem768 => "mlkem768"
  | .mlkem1024 => "mlkem1024"

def kdfName : KdfId → String
  | .hkdfSha256 => "sha256" | .hkdfSha384 => "sha384" | .hkdfSha512 => "sha512"

def aeadName : AeadId → String
  | .aes128Gcm => "aes128gcm" | .aes256Gcm => "aes256gcm"
  | .chacha20Poly1305 => "chacha20poly1305"

def errName (e : Err) : String :=
  match e.cls with
  | .unsupportedAlgorithm => "unsupported_algorithm"
  | .invalidPublicKey => "invalid_public_key"
  | .invalidPrivateKey => "invalid_private_key"
  | .invalidEncapsulation => "invalid_encapsulation"
  | .keyMismatch => "key_mismatch"
  | .unsupportedMode => "unsupported_mode"
  | .deriveKeyPairFailure => "derive_key_pair_failure"
  | .invalidPsk => "invalid_psk"
  | .invalidLength => "invalid_length"
  | .messageLimitReached => "message_limit_reached"
  | .plaintextTooLong => "plaintext_too_long"
  | .exportLengthOutOfRange => "export_length_out_of_range"
  | .concurrentUse => "concurrent_use"
  | .openError => "open_error"
  | .internalError => "internal_error"

def result {α} (render : α → String) : Except Err α → String
  | .ok a => "ok " ++ render a
  | .error e => "error " ++ errName e

/-! ## Registry -/

def registry : List String := Id.run do
  let mut out := []
  for n in (List.range 0x50).map Int.ofNat ++ [-1, 0xffff, 0x10000] do
    out := out ++ [s!"kem_of_int {n} {result kemName (KemId.ofInt n)}",
      s!"kdf_of_int {n} {result kdfName (KdfId.ofInt n)}",
      s!"aead_of_int {n} {result aeadName (AeadId.ofInt n)}"]
  for k in KemId.all do
    out := out ++ [s!"kem_sizes {kemName k} {k.toInt} {k.publicKeySize} {k.privateKeySize} {k.encapsulatedKeySize} {k.secretSize} {bool k.supportsAuth}"]
  for k in KdfId.all do
    out := out ++ [s!"kdf_sizes {kdfName k} {k.toInt} {k.hashSize}"]
  for a in AeadId.all do
    out := out ++ [s!"aead_sizes {aeadName a} {a.toInt} {a.keySize} {a.nonceSize} {a.tagSize}"]
  return out

/-! ## Sequence numbers -/

/-- Sequences worth testing at length `n`: the extremes, every run of trailing
`0xff` bytes, a single non-`0xff` byte at every position, and random values. -/
def sequences (n : Nat) : List Bytes :=
  let ff := List.replicate n (255 : UInt8)
  let trailing := (List.range (n + 1)).map fun k =>
    randBytes (n * 31 + k) (n - k) |>.map (fun b => if b = 255 then 254 else b) |> (· ++ List.replicate k 255)
  let holes := (List.range n).map fun i => ff.set i 0x7f
  [i2osp 0 n, i2osp 1 n, i2osp 255 n, i2osp 256 n, ff, i2osp (maxSeq n - 1) n]
    ++ trailing ++ holes ++ (List.range 8).map (fun k => randBytes (n * 97 + k) n)

def sequence : List String := Id.run do
  let mut out := []
  for n in List.range' 1 16 do
    for s in sequences n do
      out := out ++ [s!"increment {hex s} {hex (incrementSequence s)}",
        s!"exhausted {hex s} {bool (sequenceExhausted s)}"]
  for k in List.range 16 do
    let base := randBytes (5000 + k) 12
    let seq := (sequences 12)[k % (sequences 12).length]!
    out := out ++ [s!"nonce {hex base} {hex seq} {hex (nonceOf base seq)}"]
  return out

/-! ## AEAD limits -/

-- `lib/hpke.ml` carries the corrected AES-GCM bound, so the vectors come from
-- `plaintextFitsFixed`; `plaintextFits` keeps the bound the findings are about.
def limits : List String := Id.run do
  let mut out := []
  for a in AeadId.all do
    for len in [0, 1, 16, 2 ^ 36 - 33, 2 ^ 36 - 32, 2 ^ 36 - 31, 2 ^ 36 - 30,
        2 ^ 38 - 65, 2 ^ 38 - 64, 2 ^ 38 - 63, 2 ^ 40] do
      out := out ++ [s!"plaintext_fits {aeadName a} {len} {bool (plaintextFitsFixed a len)}"]
  return out

/-! ## Encodings -/

def optHex : Option Bytes → String
  | some b => hex b
  | none => "raises"

def labels : List String :=
  ["psk_id_hash", "info_hash", "secret", "key", "base_nonce", "exp", "sec",
   "dkp_prk", "candidate", "sk", "eae_prk", "shared_secret", "DeriveKeyPair", ""]

def encodings : List String := Id.run do
  let mut out := []
  for n in [-1, 0, 1, 255, 256, 4660, 0xfffe, 0xffff, 0x10000, 0x7fffffff] do
    out := out ++ [s!"i2osp2 {n} {optHex (i2osp2 n)}"]
  for n in [-1, 0, 1, 127, 255, 256] do
    out := out ++ [s!"byte {n} {optHex (byte n)}"]
  for k in KemId.all do
    out := out ++ [s!"kem_suite_id {kemName k} {hex (kemSuiteId k)}"]
    for f in KdfId.all do
      out := out ++ [s!"suite_id {kemName k} {kdfName f} export {hex (suiteId k f none)}"]
      for a in AeadId.all do
        out := out ++ [s!"suite_id {kemName k} {kdfName f} {aeadName a} {hex (suiteId k f (some a))}"]
  let mut i := 0
  for label in labels do
    for f in KdfId.all do
      i := i + 1
      let sid := suiteId .x25519 f (some .aes128Gcm)
      let salt := randBytes (7000 + i) (i % 3 * 16)
      let ikm := randBytes (8000 + i) (i % 5 * 13)
      let info := randBytes (9000 + i) (i % 4 * 9)
      let prk := randBytes (9500 + i) f.hashSize
      out := out ++ [s!"labeled_extract {kdfName f} {hex sid} {hex salt} {hex (ascii label)} {hex ikm} {hex (labeledIkm sid (ascii label) ikm)}"]
      for len in [0, 1, 12, 32, f.hashSize, 255 * f.hashSize] do
        out := out ++ [s!"labeled_expand {kdfName f} {hex sid} {hex prk} {hex (ascii label)} {hex info} {len} {optHex (labeledInfo sid (ascii label) info len)}"]
    for k in [KemId.mlkem512, .mlkem768, .mlkem1024] do
      i := i + 1
      let ikm := randBytes (9900 + i) (i % 3 * 32)
      let ctx := randBytes (9950 + i) (i % 2 * 7)
      for len in [0, 32, 64] do
        out := out ++ [s!"labeled_derive {kemName k} {hex (ascii label)} {hex ctx} {hex ikm} {len} {optHex (kemDeriveShake256Input k (ascii label) ctx ikm len)}"]
  return out

/-! ## Private keys -/

def raisesHex : Scalar.OCaml.Raises Bytes → String
  | .ok b => hex b
  | .error _ => "raises"

def raisesBool : Scalar.OCaml.Raises Bool → String
  | .ok b => bool b
  | .error _ => "raises"

/-- Scalars worth testing for a KEM: the edges of `[1, n)` for the NIST
curves, and for every KEM zero, one, all-ones, random, and wrong lengths. -/
def scalarInputs (k : KemId) : List Bytes :=
  let n := k.privateKeySize
  let order := Scalar.groupOrder k
  let nist := if Scalar.isNist k then
      [i2osp (order - 1) n, i2osp order n, i2osp (order + 1) n, i2osp (order / 2) n]
    else []
  [i2osp 0 n, i2osp 1 n, List.replicate n 0xff, randBytes (11000 + n) n,
   randBytes (12000 + n) n, [], i2osp 1 (n - 1), i2osp 1 (n + 1), List.replicate (n + 1) 0]
    ++ nist

def privateKeys : List String := Id.run do
  let mut out := []
  for k in KemId.all do
    out := out ++ [s!"curve_order {kemName k} {raisesHex (Scalar.curveOrder k)}"]
    for b in scalarInputs k do
      out := out ++ [s!"valid_nist_scalar {kemName k} {hex b} {raisesBool (Scalar.validNistScalar k b)}"]
      match Scalar.privateKeyBytes k b with
      | .ok r => out := out ++ [s!"private_key {kemName k} {hex b} {result hex r}"]
      | .error _ => pure ()
  for n in [0, 1, 2, 31, 32, 33, 55, 56, 57] do
    for b in [List.replicate n 0, List.replicate n 0xff, randBytes (13000 + n) n] do
      out := out ++ [s!"normalize_x25519 {hex b} {raisesHex (Scalar.normalizeX25519 b)}",
        s!"normalize_x448 {hex b} {raisesHex (Scalar.normalizeX448 b)}",
        s!"all_zero {hex b} {bool (Scalar.allZero b)}"]
  for i in List.range 5 do
    out := out ++ [s!"all_zero {hex ((List.replicate 5 (0 : UInt8)).set i 1)} {bool (Scalar.allZero ((List.replicate 5 (0 : UInt8)).set i 1))}"]
  return out

/-! ## Setup error contracts -/

/-- Every row of `Setup.table`: suite KEM, recipient KEM, sender KEM, mode,
and the result both `setup_*_sender` and `setup_*_receiver` must return. -/
def setups : List String :=
  Setup.table.map fun (s, r, sk, md, c) =>
    s!"setup {kemName s} {kemName r} {(sk.map kemName).getD "-"} {md} {Setup.className c}"

def all : List String := registry ++ sequence ++ limits ++ encodings ++ privateKeys ++ setups

end Conformance

def main : IO Unit := do
  for line in Conformance.all do
    IO.println line
