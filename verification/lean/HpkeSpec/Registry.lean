/-
The closed algorithm registries of `lib/hpke.ml` (`Error`, `Kem`, `Kdf`,
`Aead`) and the tables they must agree with.

Two kinds of definition appear here:

* *mirrors* (`Kem.toInt`, `Kem.publicKeySize`, ...) transcribe the OCaml
  functions case for case, keeping their structure (for example
  `encapsulated_key_size` is defined through `public_key_size` for the
  Diffie-Hellman KEMs, as in OCaml);
* *specifications* (`kemTable`, `kdfTable`, `aeadTable`) transcribe the IANA
  and RFC tables: RFC 9180 Tables 2, 3 and 5 and draft-ietf-hpke-pq-05's
  ML-KEM and PQ/T hybrid tables (Sections 8.1 and 8.2).

The theorems prove that every mirror agrees with its table and that the
integer codecs are mutually inverse on the registry.
-/

namespace Hpke

/-- `Hpke.Error.t`. Payload strings are kept so the model can state which
constructor is returned; their text is irrelevant to every theorem. -/
inductive Err where
  | unsupportedAlgorithm (id : Int)
  | invalidPublicKey (reason : String)
  | invalidPrivateKey (reason : String)
  | invalidEncapsulation (reason : String)
  | keyMismatch
  | unsupportedMode
  | deriveKeyPairFailure
  | invalidPsk (reason : String)
  | invalidLength (reason : String)
  | messageLimitReached
  | plaintextTooLong
  | exportLengthOutOfRange
  | concurrentUse
  | openError
  | internalError (reason : String)
  deriving DecidableEq, Repr

/-- The error class, forgetting payload strings. -/
inductive ErrClass where
  | unsupportedAlgorithm | invalidPublicKey | invalidPrivateKey
  | invalidEncapsulation | keyMismatch | unsupportedMode
  | deriveKeyPairFailure | invalidPsk | invalidLength | messageLimitReached
  | plaintextTooLong | exportLengthOutOfRange | concurrentUse | openError
  | internalError
  deriving DecidableEq, Repr

def Err.cls : Err → ErrClass
  | .unsupportedAlgorithm _ => .unsupportedAlgorithm
  | .invalidPublicKey _ => .invalidPublicKey
  | .invalidPrivateKey _ => .invalidPrivateKey
  | .invalidEncapsulation _ => .invalidEncapsulation
  | .keyMismatch => .keyMismatch
  | .unsupportedMode => .unsupportedMode
  | .deriveKeyPairFailure => .deriveKeyPairFailure
  | .invalidPsk _ => .invalidPsk
  | .invalidLength _ => .invalidLength
  | .messageLimitReached => .messageLimitReached
  | .plaintextTooLong => .plaintextTooLong
  | .exportLengthOutOfRange => .exportLengthOutOfRange
  | .concurrentUse => .concurrentUse
  | .openError => .openError
  | .internalError _ => .internalError

/-! ## KEM registry -/

inductive KemId where
  | p256 | p384 | p521 | x25519 | x448 | mlkem512 | mlkem768 | mlkem1024
  | mlkem768P256 | mlkem768X25519 | mlkem1024P384
  deriving DecidableEq, Repr, Inhabited

inductive KdfId where
  | hkdfSha256 | hkdfSha384 | hkdfSha512
  deriving DecidableEq, Repr, Inhabited

inductive AeadId where
  | aes128Gcm | aes256Gcm | chacha20Poly1305
  deriving DecidableEq, Repr, Inhabited

namespace KemId

def all : List KemId :=
  [p256, p384, p521, x25519, x448, mlkem512, mlkem768, mlkem1024, mlkem768P256,
    mlkem768X25519, mlkem1024P384]

theorem mem_all (k : KemId) : k ∈ all := by cases k <;> simp [all]

/-- Mirror of `Kem.to_int`. -/
def toInt : KemId → Int
  | p256 => 0x0010 | p384 => 0x0011 | p521 => 0x0012
  | x25519 => 0x0020 | x448 => 0x0021
  | mlkem512 => 0x0040 | mlkem768 => 0x0041 | mlkem1024 => 0x0042
  | mlkem768P256 => 0x0050 | mlkem1024P384 => 0x0051 | mlkem768X25519 => 0x647a

/-- Mirror of `Kem.of_int`. -/
def ofInt : Int → Except Err KemId
  | 0x0010 => .ok p256 | 0x0011 => .ok p384 | 0x0012 => .ok p521
  | 0x0020 => .ok x25519 | 0x0021 => .ok x448
  | 0x0040 => .ok mlkem512 | 0x0041 => .ok mlkem768 | 0x0042 => .ok mlkem1024
  | 0x0050 => .ok mlkem768P256 | 0x0051 => .ok mlkem1024P384
  | 0x647a => .ok mlkem768X25519
  | id => .error (.unsupportedAlgorithm id)

/-- Mirror of `Kem.public_key_size` (`Npk`), with the sums the OCaml writes for
the hybrids. -/
def publicKeySize : KemId → Nat
  | p256 => 65 | p384 => 97 | p521 => 133 | x25519 => 32 | x448 => 56
  | mlkem512 => 800 | mlkem768 => 1184 | mlkem1024 => 1568
  | mlkem768P256 => 1184 + 65 | mlkem768X25519 => 1184 + 32 | mlkem1024P384 => 1568 + 97

/-- Mirror of `Kem.private_key_size` (`Nsk`). -/
def privateKeySize : KemId → Nat
  | p256 => 32 | p384 => 48 | p521 => 66 | x25519 => 32 | x448 => 56
  | mlkem512 | mlkem768 | mlkem1024 => 64
  | mlkem768P256 | mlkem768X25519 | mlkem1024P384 => 32

/-- Mirror of `Kem.encapsulated_key_size` (`Nenc`), including its fall-through
to `public_key_size` for the Diffie-Hellman KEMs. -/
def encapsulatedKeySize : KemId → Nat
  | k@p256 | k@p384 | k@p521 | k@x25519 | k@x448 => publicKeySize k
  | mlkem512 => 768 | mlkem768 => 1088 | mlkem1024 => 1568
  | mlkem768P256 => 1088 + 65 | mlkem768X25519 => 1088 + 32 | mlkem1024P384 => 1568 + 97

/-- Mirror of `Kem.secret_size` (`Nsecret`). -/
def secretSize : KemId → Nat
  | p256 => 32 | p384 => 48 | p521 => 64 | x25519 => 32 | x448 => 64
  | mlkem512 | mlkem768 | mlkem1024 => 32
  | mlkem768P256 | mlkem768X25519 | mlkem1024P384 => 32

/-- Mirror of `Kem.supports_auth`. -/
def supportsAuth : KemId → Bool
  | p256 | p384 | p521 | x25519 | x448 => true
  | mlkem512 | mlkem768 | mlkem1024 | mlkem768P256 | mlkem768X25519 | mlkem1024P384 => false

/-- Whether the KEM is a DHKEM of RFC 9180 (as opposed to ML-KEM or a hybrid). -/
def isDh : KemId → Bool
  | p256 | p384 | p521 | x25519 | x448 => true
  | _ => false

/-- Whether the KEM is a DHKEM over a NIST curve. -/
def isNist' : KemId → Bool
  | p256 | p384 | p521 => true
  | _ => false

/-- Whether the KEM is a PQ/T hybrid of draft-ietf-hpke-pq-05 Section 4. -/
def isHybrid : KemId → Bool
  | mlkem768P256 | mlkem768X25519 | mlkem1024P384 => true
  | _ => false

/-- The `Params` of the `Hybrid_kem` functor applications (`pq`, and the group,
named by the DHKEM over it): the ML-KEM parameter set and the nominal group of
each hybrid (draft-irtf-cfrg-concrete-hybrid-kems Section 4). -/
def hybridParts : KemId → Option (KemId × KemId)
  | mlkem768P256 => some (mlkem768, p256)
  | mlkem768X25519 => some (mlkem768, x25519)
  | mlkem1024P384 => some (mlkem1024, p384)
  | _ => none

end KemId

namespace KdfId

def all : List KdfId := [hkdfSha256, hkdfSha384, hkdfSha512]

theorem mem_all (k : KdfId) : k ∈ all := by cases k <;> simp [all]

/-- Mirror of `Kdf.to_int`. -/
def toInt : KdfId → Int
  | hkdfSha256 => 0x0001 | hkdfSha384 => 0x0002 | hkdfSha512 => 0x0003

/-- Mirror of `Kdf.of_int`. -/
def ofInt : Int → Except Err KdfId
  | 0x0001 => .ok hkdfSha256 | 0x0002 => .ok hkdfSha384
  | 0x0003 => .ok hkdfSha512
  | id => .error (.unsupportedAlgorithm id)

/-- Mirror of `Kdf.hash_size` (`Nh`). -/
def hashSize : KdfId → Nat
  | hkdfSha256 => 32 | hkdfSha384 => 48 | hkdfSha512 => 64

end KdfId

namespace AeadId

def all : List AeadId := [aes128Gcm, aes256Gcm, chacha20Poly1305]

theorem mem_all (a : AeadId) : a ∈ all := by cases a <;> simp [all]

/-- Mirror of `Aead.to_int`. -/
def toInt : AeadId → Int
  | aes128Gcm => 0x0001 | aes256Gcm => 0x0002 | chacha20Poly1305 => 0x0003

/-- Mirror of `Aead.of_int`. -/
def ofInt : Int → Except Err AeadId
  | 0x0001 => .ok aes128Gcm | 0x0002 => .ok aes256Gcm
  | 0x0003 => .ok chacha20Poly1305
  | id => .error (.unsupportedAlgorithm id)

/-- Mirror of `Aead.key_size` (`Nk`). -/
def keySize : AeadId → Nat
  | aes128Gcm => 16 | aes256Gcm | chacha20Poly1305 => 32

/-- Mirror of `Aead.nonce_size` (`Nn`). -/
def nonceSize (_ : AeadId) : Nat := 12

/-- Mirror of `Aead.tag_size` (`Nt`). -/
def tagSize (_ : AeadId) : Nat := 16

end AeadId

/-- Mirror of `Labeled_kdf.kem_kdf`, the KDF of a DHKEM; ML-KEM and the hybrids
have none, where OCaml raises `Invalid_argument`. -/
def kemKdf : KemId → Option KdfId
  | .p256 | .x25519 => some .hkdfSha256
  | .p384 => some .hkdfSha384
  | .p521 | .x448 => some .hkdfSha512
  | .mlkem512 | .mlkem768 | .mlkem1024 | .mlkem768P256 | .mlkem768X25519
  | .mlkem1024P384 => none

/-! ## Specification tables -/

/-- A row of the HPKE KEM registry (RFC 9180 Table 2; draft-ietf-hpke-pq-05
Sections 8.1 and 8.2 for ML-KEM and the hybrids): identifier, `Nsecret`, `Nenc`, `Npk`, `Nsk`, `Auth`,
and for a DHKEM the KDF named in the KEM's name. -/
structure KemRow where
  id : Int
  nsecret : Nat
  nenc : Nat
  npk : Nat
  nsk : Nat
  auth : Bool
  kdf : Option KdfId
  deriving DecidableEq, Repr

def kemTable : KemId → KemRow
  | .p256 => ⟨0x0010, 32, 65, 65, 32, true, some .hkdfSha256⟩
  | .p384 => ⟨0x0011, 48, 97, 97, 48, true, some .hkdfSha384⟩
  | .p521 => ⟨0x0012, 64, 133, 133, 66, true, some .hkdfSha512⟩
  | .x25519 => ⟨0x0020, 32, 32, 32, 32, true, some .hkdfSha256⟩
  | .x448 => ⟨0x0021, 64, 56, 56, 56, true, some .hkdfSha512⟩
  | .mlkem512 => ⟨0x0040, 32, 768, 800, 64, false, none⟩
  | .mlkem768 => ⟨0x0041, 32, 1088, 1184, 64, false, none⟩
  | .mlkem1024 => ⟨0x0042, 32, 1568, 1568, 64, false, none⟩
  | .mlkem768P256 => ⟨0x0050, 32, 1153, 1249, 32, false, none⟩
  | .mlkem1024P384 => ⟨0x0051, 32, 1665, 1665, 32, false, none⟩
  | .mlkem768X25519 => ⟨0x647a, 32, 1120, 1216, 32, false, none⟩

/-- RFC 9180 Table 3: identifier and `Nh`. -/
def kdfTable : KdfId → Int × Nat
  | .hkdfSha256 => (0x0001, 32)
  | .hkdfSha384 => (0x0002, 48)
  | .hkdfSha512 => (0x0003, 64)

/-- RFC 9180 Table 5: identifier, `Nk`, `Nn`, `Nt`. -/
def aeadTable : AeadId → Int × Nat × Nat × Nat
  | .aes128Gcm => (0x0001, 16, 12, 16)
  | .aes256Gcm => (0x0002, 32, 12, 16)
  | .chacha20Poly1305 => (0x0003, 32, 12, 16)

/-- The export-only AEAD identifier of RFC 9180 Table 5. -/
def exportOnlyAeadId : Int := 0xFFFF

/-! ## The mirrors agree with the tables -/

theorem kem_matches_table (k : KemId) :
    kemTable k =
      ⟨k.toInt, k.secretSize, k.encapsulatedKeySize, k.publicKeySize,
        k.privateKeySize, k.supportsAuth, kemKdf k⟩ := by
  cases k <;> rfl

theorem kdf_matches_table (k : KdfId) : kdfTable k = (k.toInt, k.hashSize) := by
  cases k <;> rfl

theorem aead_matches_table (a : AeadId) :
    aeadTable a = (a.toInt, a.keySize, a.nonceSize, a.tagSize) := by
  cases a <;> rfl

/-- `Kem.supports_auth` is exactly "is a DHKEM". -/
theorem supportsAuth_iff_isDh (k : KemId) : k.supportsAuth = k.isDh := by
  cases k <;> rfl

/-- A KEM is a DHKEM, a hybrid, or ML-KEM alone, and never two of these. -/
theorem isDh_isHybrid (k : KemId) : ¬ (k.isDh = true ∧ k.isHybrid = true) := by
  cases k <;> simp [KemId.isDh, KemId.isHybrid]

theorem isHybrid_iff_parts (k : KemId) : k.isHybrid = true ↔ (KemId.hybridParts k).isSome := by
  cases k <;> simp [KemId.isHybrid, KemId.hybridParts]

/-- The hybrid sizes of draft-ietf-hpke-pq-05 Section 8.2 are those of
draft-irtf-cfrg-concrete-hybrid-kems Section 4: `Nek` is the ML-KEM `Nek` plus
the group's `Nelem` (the DHKEM `Npk` over the group), `Nct` the ML-KEM `Nct`
plus `Nelem`, and the shared secret the 32 bytes of SHA3-256. -/
theorem hybrid_sizes (k pq g : KemId) (h : KemId.hybridParts k = some (pq, g)) :
    k.publicKeySize = pq.publicKeySize + g.publicKeySize ∧
    k.encapsulatedKeySize = pq.encapsulatedKeySize + g.publicKeySize ∧
    k.privateKeySize = 32 ∧ k.secretSize = 32 ∧
    pq.isDh = false ∧ pq.isHybrid = false ∧ g.isDh = true ∧ g.supportsAuth = true := by
  cases k <;> simp [KemId.hybridParts] at h <;> obtain ⟨rfl, rfl⟩ := h <;> decide

/-- A DHKEM encapsulates to a serialized public key (RFC 9180 Section 4.1). -/
theorem dh_nenc_eq_npk (k : KemId) (h : k.isDh = true) :
    k.encapsulatedKeySize = k.publicKeySize := by
  cases k <;> simp_all [KemId.isDh, KemId.encapsulatedKeySize]

/-! ## Codecs -/

theorem KemId.ofInt_toInt (k : KemId) : KemId.ofInt k.toInt = .ok k := by
  cases k <;> rfl

theorem KdfId.ofInt_toInt (k : KdfId) : KdfId.ofInt k.toInt = .ok k := by
  cases k <;> rfl

theorem AeadId.ofInt_toInt (a : AeadId) : AeadId.ofInt a.toInt = .ok a := by
  cases a <;> rfl

theorem KemId.toInt_ofInt {n : Int} {k : KemId} (h : KemId.ofInt n = .ok k) :
    k.toInt = n := by
  unfold KemId.ofInt at h
  split at h <;> first | (cases h; rfl) | cases h

theorem KdfId.toInt_ofInt {n : Int} {k : KdfId} (h : KdfId.ofInt n = .ok k) :
    k.toInt = n := by
  unfold KdfId.ofInt at h
  split at h <;> first | (cases h; rfl) | cases h

theorem AeadId.toInt_ofInt {n : Int} {a : AeadId} (h : AeadId.ofInt n = .ok a) :
    a.toInt = n := by
  unfold AeadId.ofInt at h
  split at h <;> first | (cases h; rfl) | cases h

theorem KemId.toInt_injective {a b : KemId} (h : a.toInt = b.toInt) : a = b := by
  have := KemId.ofInt_toInt a
  rw [h, KemId.ofInt_toInt] at this
  cases this; rfl

theorem KdfId.toInt_injective {a b : KdfId} (h : a.toInt = b.toInt) : a = b := by
  have := KdfId.ofInt_toInt a
  rw [h, KdfId.ofInt_toInt] at this
  cases this; rfl

theorem AeadId.toInt_injective {a b : AeadId} (h : a.toInt = b.toInt) : a = b := by
  have := AeadId.ofInt_toInt a
  rw [h, AeadId.ofInt_toInt] at this
  cases this; rfl

/-- Every identifier fits `I2OSP(·, 2)` and none is the export-only `0xFFFF`,
so `suite_id` never confuses an AEAD with export-only operation. -/
theorem ids_in_range :
    (∀ k : KemId, 0 ≤ k.toInt ∧ k.toInt < 0x10000) ∧
    (∀ k : KdfId, 0 ≤ k.toInt ∧ k.toInt < 0x10000) ∧
    (∀ a : AeadId, 0 ≤ a.toInt ∧ a.toInt < 0x10000 ∧ a.toInt ≠ exportOnlyAeadId) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro x <;> cases x <;> decide

/-- Every unknown integer is rejected with `Unsupported_algorithm` carrying it. -/
theorem KemId.ofInt_error {n : Int} (h : ∀ k : KemId, k.toInt ≠ n) :
    KemId.ofInt n = .error (.unsupportedAlgorithm n) := by
  unfold KemId.ofInt
  split <;> first | rfl | (exfalso; first
    | exact h .p256 rfl | exact h .p384 rfl | exact h .p521 rfl
    | exact h .x25519 rfl | exact h .x448 rfl | exact h .mlkem512 rfl
    | exact h .mlkem768 rfl | exact h .mlkem1024 rfl | exact h .mlkem768P256 rfl
    | exact h .mlkem768X25519 rfl | exact h .mlkem1024P384 rfl)

theorem AeadId.ofInt_error {n : Int} (h : ∀ a : AeadId, a.toInt ≠ n) :
    AeadId.ofInt n = .error (.unsupportedAlgorithm n) := by
  unfold AeadId.ofInt
  split <;> first | rfl | (exfalso; first
    | exact h .aes128Gcm rfl | exact h .aes256Gcm rfl
    | exact h .chacha20Poly1305 rfl)

theorem KdfId.ofInt_error {n : Int} (h : ∀ k : KdfId, k.toInt ≠ n) :
    KdfId.ofInt n = .error (.unsupportedAlgorithm n) := by
  unfold KdfId.ofInt
  split <;> first | rfl | (exfalso; first
    | exact h .hkdfSha256 rfl | exact h .hkdfSha384 rfl
    | exact h .hkdfSha512 rfl)

end Hpke
