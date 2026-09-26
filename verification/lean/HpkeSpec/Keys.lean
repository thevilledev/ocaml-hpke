/-
Key parsing (`lib/hpke.ml`, `parse_public_bytes`, `Public_key.of_bytes`,
`Private_key.of_bytes`, `dh`, lines 428-490, 560-590, 744-769).

The curve libraries are parameters: `nistPoint k b` is what
`Mirage_crypto_ec.P*.Dsa.pub_of_octets` decides for an uncompressed encoding,
`mlkemKey k b` what `M.encapsulation_key_of_octets` decides (the FIPS 203
modulus check), `scalarOk k b` the NIST scalar check (`valid_nist_scalar`,
proved in `Scalar.lean` to be `0 < OS2IP(b) < n`), `clamp k b` the X25519/X448
clamp, and `derive k b` the dependency's derivation of a public key from a
secret.

Proved:

* the length is checked before anything else, for public and private keys;
* a NIST public key must be the uncompressed SEC1 form (`0x04` prefix): a
  compressed point or the one-byte point at infinity is rejected by length or
  prefix before the curve library is called;
* `Public_key.to_bytes` returns exactly the parsed bytes, so a parsed key
  re-serializes to its input (the canonical-encoding fact `dh_decap` relies
  on when it puts the raw `enc` in `kem_context`);
* `Private_key.of_bytes` stores the clamped bytes for X25519/X448 and the input
  for the others, and fails with `Invalid_private_key` for a NIST scalar out of
  range;
* `dh` rejects keys of different KEMs with `Key_mismatch` before any exchange,
  and an ML-KEM or hybrid secret with `Invalid_private_key`;
* a hybrid public key is accepted only if its ML-KEM half passes the modulus
  check and its element is accepted as a public key of its group: for P-256 and
  P-384 an uncompressed point on the curve, for X25519 any value;
* a hybrid private key is its seed, whatever `derive` makes of it.
-/

import HpkeSpec.Bytes
import HpkeSpec.Registry

namespace Hpke.Keys

/-- The curve and ML-KEM libraries' decisions, as parameters. -/
structure Deps where
  nistPoint : KemId → Bytes → Bool
  x25519Or448 : KemId → Bytes → Bool := fun _ _ => true
  mlkemKey : KemId → Bytes → Bool
  scalarOk : KemId → Bytes → Bool
  clamp : KemId → Bytes → Bytes
  /-- The encoded public key the dependency derives from a secret. -/
  derive : KemId → Bytes → Except Err Bytes

structure PublicKey where
  kem : KemId
  bytes : Bytes
  deriving DecidableEq, Repr

structure PrivateKey where
  kem : KemId
  bytes : Bytes
  publicKey : PublicKey
  deriving DecidableEq, Repr

variable (deps : Deps)

/-- The NIST branch of `parse_public_bytes`: the `'\004'` prefix, then the
curve library. -/
def parseNist (kem : KemId) (b : Bytes) : Except Err Unit :=
  if b.head? ≠ some 4 then
    .error (.invalidPublicKey "only canonical uncompressed SEC1 encodings are accepted")
  else if deps.nistPoint kem b then .ok ()
  else .error (.invalidPublicKey "curve library")

/-- `Group.check_element` of the nominal groups (`Nist_group`,
`X25519_group`): `nist_public_key` for P-256 and P-384, nothing for X25519. -/
def checkElement (group : KemId) (e : Bytes) : Except Err Unit :=
  match group with
  | .p256 | .p384 | .p521 => parseNist deps group e
  | _ => .ok ()

/-- `Hybrid_kem.public_key`: the ML-KEM half (`String.sub bytes 0 Npk`) through
`Mlkem_kem.public_key`, then the element (`String.sub bytes Npk Nelem`)
through `Group.check_element`. -/
def parseHybrid (pq group : KemId) (b : Bytes) : Except Err Unit :=
  if deps.mlkemKey pq (b.take pq.publicKeySize) then
    checkElement deps group ((b.drop pq.publicKeySize).take group.publicKeySize)
  else .error (.invalidPublicKey "modulus")

/-- Mirror of `parse_public_bytes`: length first, then the per-KEM check. -/
def parsePublic (kem : KemId) (b : Bytes) : Except Err Unit :=
  if b.length ≠ kem.publicKeySize then .error (.invalidPublicKey "wrong encoded length")
  else match kem with
    | .x25519 | .x448 => .ok ()
    | .p256 | .p384 | .p521 => parseNist deps kem b
    | .mlkem512 | .mlkem768 | .mlkem1024 =>
      if deps.mlkemKey kem b then .ok () else .error (.invalidPublicKey "modulus")
    | .mlkem768P256 => parseHybrid deps .mlkem768 .p256 b
    | .mlkem768X25519 => parseHybrid deps .mlkem768 .x25519 b
    | .mlkem1024P384 => parseHybrid deps .mlkem1024 .p384 b

/-- Mirror of `Public_key.of_bytes`. -/
def publicOfBytes (kem : KemId) (b : Bytes) : Except Err PublicKey := do
  parsePublic deps kem b
  return { kem, bytes := b }

/-- Mirror of `Private_key.of_bytes`, with `secret_and_public` folded in: the
secret's public key is parsed as any other (`Public_key.of_bytes`) for a DHKEM,
and taken as is from ML-KEM or hybrid key generation. For a hybrid, `derive`
fails with `Invalid_private_key` when the seed yields no scalar. -/
def privateOfBytes (kem : KemId) (b : Bytes) : Except Err PrivateKey := do
  if b.length ≠ kem.privateKeySize then
    throw (.invalidPrivateKey "wrong encoded length")
  let b ← match kem with
    | .x25519 | .x448 => pure (deps.clamp kem b)
    | .p256 | .p384 | .p521 =>
      if deps.scalarOk kem b then pure b
      else throw (.invalidPrivateKey "scalar is outside the valid range")
    | .mlkem512 | .mlkem768 | .mlkem1024 | .mlkem768P256 | .mlkem768X25519
    | .mlkem1024P384 => pure b
  let pub ← deps.derive kem b
  let publicKey ← match kem with
    | .mlkem512 | .mlkem768 | .mlkem1024 | .mlkem768P256 | .mlkem768X25519
    | .mlkem1024P384 => pure { kem, bytes := pub }
    | _ => publicOfBytes deps kem pub
  return { kem, bytes := b, publicKey }

/-- The reason `dh` gives for a secret that is not a Diffie-Hellman one. -/
def notDhReason (kem : KemId) : String :=
  if kem.isHybrid then "hybrid KEM keys cannot perform a Diffie-Hellman exchange"
  else "ML-KEM keys cannot perform a Diffie-Hellman exchange"

/-- Mirror of the checks of `dh` that precede the exchange. -/
def dhPrecheck (sk : PrivateKey) (pk : PublicKey) : Except Err Unit :=
  if sk.kem ≠ pk.kem then .error .keyMismatch
  else if sk.kem.isDh then .ok ()
  else .error (.invalidPrivateKey (notDhReason sk.kem))

/-! ## Public keys -/

theorem publicOfBytes_wrong_length (kem : KemId) (b : Bytes)
    (h : b.length ≠ kem.publicKeySize) :
    ∃ r, publicOfBytes deps kem b = .error (.invalidPublicKey r) := by
  refine ⟨"wrong encoded length", ?_⟩
  simp [publicOfBytes, parsePublic, h, bind, Except.bind]

theorem publicOfBytes_ok {kem : KemId} {b : Bytes} {k : PublicKey}
    (h : publicOfBytes deps kem b = .ok k) :
    k = { kem, bytes := b } ∧ b.length = kem.publicKeySize := by
  unfold publicOfBytes at h
  cases hp : parsePublic deps kem b with
  | error e => simp [hp, bind, Except.bind] at h
  | ok u =>
    simp [hp, bind, Except.bind, pure, Except.pure] at h
    refine ⟨h.symm, ?_⟩
    unfold parsePublic at hp
    by_cases hl : b.length = kem.publicKeySize
    · exact hl
    · simp [hl] at hp

/-- A parsed key serializes to exactly its input: `SerializePublicKey`
inverts `DeserializePublicKey` on everything the parser accepts. -/
theorem serialize_deserialize {kem : KemId} {b : Bytes} {k : PublicKey}
    (h : publicOfBytes deps kem b = .ok k) : k.bytes = b := by
  rw [(publicOfBytes_ok deps h).1]

/-- A NIST key is accepted only in uncompressed form, and only if the curve
library accepts the point. -/
theorem nist_uncompressed {kem : KemId} (hk : kem = .p256 ∨ kem = .p384 ∨ kem = .p521)
    {b : Bytes} {k : PublicKey} (h : publicOfBytes deps kem b = .ok k) :
    b.head? = some 4 ∧ deps.nistPoint kem b = true := by
  have hl := (publicOfBytes_ok deps h).2
  have hn : parseNist deps kem b = .ok () := by
    unfold publicOfBytes parsePublic at h
    rcases hk with rfl | rfl | rfl <;>
    · simp only [hl, ne_eq, not_true_eq_false, ite_false] at h
      cases hp : parseNist deps _ b <;> simp_all [bind, Except.bind]
  unfold parseNist at hn
  by_cases h4 : b.head? = some 4
  · by_cases hp : deps.nistPoint kem b = true
    · exact ⟨h4, hp⟩
    · simp [h4, hp] at hn
  · simp [h4] at hn

/-- The SEC1 point at infinity (`0x00`) and compressed points (`0x02`/`0x03`
prefix, or the compressed length) are rejected. -/
theorem nist_rejects_infinity_and_compressed (kem : KemId)
    (hk : kem = .p256 ∨ kem = .p384 ∨ kem = .p521) (b : Bytes)
    (h : b = [0] ∨ b.head? = some 2 ∨ b.head? = some 3) :
    ∀ k, publicOfBytes deps kem b ≠ .ok k := by
  intro k hok
  have := (nist_uncompressed deps hk hok).1
  rcases h with rfl | h | h <;> simp_all

/-- For X25519 and X448 every string of the right length parses: RFC 9180
Section 7.1.1 makes deserialization the identity, and low-order points are
rejected when used, by the exchange's all-zero check. -/
theorem montgomery_total (kem : KemId) (hk : kem = .x25519 ∨ kem = .x448) (b : Bytes)
    (hl : b.length = kem.publicKeySize) :
    publicOfBytes deps kem b = .ok { kem, bytes := b } := by
  rcases hk with rfl | rfl <;>
  simp [publicOfBytes, parsePublic, hl, bind, Except.bind, pure, Except.pure]

/-! ## Private keys -/

theorem privateOfBytes_wrong_length (kem : KemId) (b : Bytes)
    (h : b.length ≠ kem.privateKeySize) :
    privateOfBytes deps kem b = .error (.invalidPrivateKey "wrong encoded length") := by
  simp [privateOfBytes, h, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- The stored bytes: clamped for X25519/X448, as given otherwise. -/
theorem privateOfBytes_bytes {kem : KemId} {b : Bytes} {k : PrivateKey}
    (h : privateOfBytes deps kem b = .ok k) :
    k.kem = kem ∧ b.length = kem.privateKeySize ∧
    k.bytes = (if kem = .x25519 ∨ kem = .x448 then deps.clamp kem b else b) := by
  unfold privateOfBytes at h
  by_cases hl : b.length = kem.privateKeySize
  · cases kem <;>
    simp only [hl, ne_eq, not_true_eq_false, ite_false, bind, Except.bind, pure,
      Except.pure] at h <;>
    (repeat' split at h) <;> first | (cases h; simp_all) | simp_all
  · simp [hl, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- A NIST scalar the check rejects is an invalid private key. -/
theorem privateOfBytes_scalar_range {kem : KemId}
    (hk : kem = .p256 ∨ kem = .p384 ∨ kem = .p521) {b : Bytes}
    (hl : b.length = kem.privateKeySize) (hs : deps.scalarOk kem b = false) :
    privateOfBytes deps kem b =
      .error (.invalidPrivateKey "scalar is outside the valid range") := by
  rcases hk with rfl | rfl | rfl <;>
  simp [privateOfBytes, hl, hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- The public key of a Diffie-Hellman private key passed the same validation
as a received public key. -/
theorem privateOfBytes_public_valid {kem : KemId} (hk : kem.isDh = true) {b : Bytes}
    {k : PrivateKey} (h : privateOfBytes deps kem b = .ok k) :
    ∃ pub, publicOfBytes deps kem pub = .ok k.publicKey := by
  unfold privateOfBytes at h
  by_cases hl : b.length = kem.privateKeySize
  · cases kem <;> simp [KemId.isDh] at hk <;>
    simp only [hl, ne_eq, not_true_eq_false, ite_false, bind, Except.bind, pure,
      Except.pure] at h <;>
    (repeat' split at h) <;> first
      | (cases h; exact ⟨_, by assumption⟩)
      | simp_all
  · simp [hl, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-! ## The exchange -/

theorem dh_key_mismatch (sk : PrivateKey) (pk : PublicKey) (h : sk.kem ≠ pk.kem) :
    dhPrecheck sk pk = .error .keyMismatch := by
  simp [dhPrecheck, h]

theorem dh_mlkem (sk : PrivateKey) (pk : PublicKey) (h : sk.kem = pk.kem)
    (hm : sk.kem.isDh = false) :
    ∃ r, dhPrecheck sk pk = .error (.invalidPrivateKey r) := by
  refine ⟨notDhReason sk.kem, ?_⟩
  unfold dhPrecheck
  rw [h] at hm
  simp [h, hm]

/-! ## Hybrid keys -/

theorem publicOfBytes_ok_iff (kem : KemId) (b : Bytes) :
    (∃ k, publicOfBytes deps kem b = .ok k) ↔ parsePublic deps kem b = .ok () := by
  unfold publicOfBytes
  cases parsePublic deps kem b <;> simp [bind, Except.bind, pure, Except.pure]

/-- A hybrid public key is accepted exactly when it has the hybrid's length,
its ML-KEM half passes the modulus check, and its element is accepted by its
group, which for P-256 and P-384 means the uncompressed form of a point the
curve library accepts. -/
theorem publicOfBytes_hybrid {kem pq group : KemId}
    (hp : KemId.hybridParts kem = some (pq, group)) (b : Bytes) :
    (∃ k, publicOfBytes deps kem b = .ok k) ↔
      b.length = kem.publicKeySize ∧ deps.mlkemKey pq (b.take pq.publicKeySize) = true ∧
      (group.isNist' = true →
        ((b.drop pq.publicKeySize).take group.publicKeySize).head? = some 4 ∧
        deps.nistPoint group ((b.drop pq.publicKeySize).take group.publicKeySize) = true) := by
  rw [publicOfBytes_ok_iff]
  by_cases hl : b.length = kem.publicKeySize
  · cases kem <;> simp [KemId.hybridParts] at hp <;> obtain ⟨rfl, rfl⟩ := hp <;>
    simp only [parsePublic, hl, ne_eq, not_true_eq_false, ite_false, parseHybrid,
      checkElement, parseNist, KemId.isNist'] <;>
    (repeat' split) <;> simp_all
  · simp [parsePublic, hl]

/-- A hybrid private key stores its seed as given. -/
theorem privateOfBytes_hybrid_bytes {kem : KemId} (hk : kem.isHybrid = true) {b : Bytes}
    {k : PrivateKey} (h : privateOfBytes deps kem b = .ok k) : k.bytes = b := by
  have := (privateOfBytes_bytes deps h).2.2
  rw [this]
  cases kem <;> simp_all [KemId.isHybrid]

theorem dh_ok_iff (sk : PrivateKey) (pk : PublicKey) :
    dhPrecheck sk pk = .ok () ↔ sk.kem = pk.kem ∧ sk.kem.isDh = true := by
  unfold dhPrecheck
  by_cases h : sk.kem = pk.kem <;> by_cases hd : sk.kem.isDh = true <;> simp_all

end Hpke.Keys
