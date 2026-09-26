import HpkeSpec.Bytes
import HpkeSpec.Registry

/-!
# KEM correctness

The KEM layer of `lib/hpke.ml` (lines 744-870): `dh`, `extract_and_expand`,
`encap_with`, `encap`, `dh_decap`, `decap`, `mlkem_without_sender`, the
`Mlkem_kem` functor (lines 385-413), and the `Hybrid_kem` functor of the PQ/T
hybrids with its nominal groups.

The cryptographic primitives are abstract. A Diffie-Hellman group is a record
of functions (`DhGroup`), an ML-KEM parameter set is another (`MlKem`), and the
labeled KDF of a DHKEM is a pair of opaque deterministic functions
(`KemKdf`). What the proofs need from the crypto libraries is stated as named
`Prop`s over these records (`DhGroup.DhCommutes`, `MlKem.Correct`, ...) and
passed to each theorem as a hypothesis; nothing is a global axiom.

Three kinds of definition appear:

* *mirrors* (`dh`, `encapWith`, `dhDecap`, `encap`, `decap`, `MlkemKem.*`)
  transcribe the OCaml, keeping its order of checks and its error constructors;
* *specifications* (`Rfc.*`, `Draft.*`, `HybridKem.CG.*`) transcribe the
  pseudocode of RFC 9180 Section 4.1, of draft-ietf-hpke-pq-05 Section 3, and
  of the CG framework of draft-irtf-cfrg-hybrid-kems Section 5;
* theorems relating them.

A remark on `Decap`: RFC 9180 puts the received `enc` itself (not
`SerializePublicKey(DeserializePublicKey(enc))`) into `kem_context`, exactly as
`dh_decap` does, so `dhDecap` equals `Decap` with no assumption about the
parser. The canonical-encoding assumption is needed elsewhere: the sender puts
the caller's recipient-key bytes where the RFC has `SerializePublicKey(pkR)`,
and the receiver puts the caller's sender-key bytes where the RFC has
`SerializePublicKey(pkS)`. `Rfc.Decap_eq_reserialized` and
`canonical_encoding_needed` make the role of the assumption precise.
-/

namespace Hpke
namespace Kem

theorem ascii_empty : ascii "" = [] := by simp [ascii]

/-! ## Abstract primitives -/

/-- `Labeled_kdf.kem_extract kem` and `Labeled_kdf.kem_expand kem` (lines
664-669): `LabeledExtract` and `LabeledExpand` of RFC 9180 Section 4 with
`suite_id = concat("KEM", I2OSP(kem_id, 2))` over the KEM's own KDF, both
determined by the KEM. Their byte encodings are verified elsewhere; here they
are opaque deterministic functions of their arguments. -/
structure KemKdf where
  labeledExtract : KemId → (salt label ikm : Bytes) → Bytes
  labeledExpand : KemId → (prk label info : Bytes) → (length : Nat) → Bytes

/-- A Diffie-Hellman group as RFC 9180 Section 4 uses it, together with the
two library functions `lib/hpke.ml` calls instead of the abstract ones.

* `pk`, `serialize`, `deserialize`, `dh` are RFC 9180's `pk(skX)`,
  `SerializePublicKey`, `DeserializePublicKey` and `DH(skX, pkY)`. A failing
  `DH` (the RFC's `ValidationError`) is `none`. `deserialize` is the whole
  Diffie-Hellman branch of `parse_public_bytes kem` (lines 428-466), its length
  and SEC1-prefix checks included; its error string is the reason carried by
  `Invalid_public_key`.
* `exchange` is the library exchange (`Mirage_crypto_ec.*.key_exchange`,
  `Curve448.X448.key_exchange`), which takes the peer's key as *octets*: the
  OCaml `dh` passes it `Public_key.to_bytes`, never a parsed point. Its error
  string is `Util.ec_error`.
* `publicOctets sk` is the public-key encoding that the library's
  `secret_of_octets` returns with the secret (lines 509-515). -/
structure DhGroup where
  SK : Type
  PK : Type
  pk : SK → PK
  serialize : PK → Bytes
  deserialize : Bytes → Except String PK
  dh : SK → PK → Option Bytes
  exchange : SK → Bytes → Except String Bytes
  publicOctets : SK → Bytes

namespace DhGroup

variable (G : DhGroup)

/-- **Assumption** (the Diffie-Hellman property): `DH(a, pk(b)) = DH(b, pk(a))`,
failures included. -/
def DhCommutes : Prop := ∀ a b : G.SK, G.dh a (G.pk b) = G.dh b (G.pk a)

/-- **Assumption** on the parser: a serialized key parses back to itself. -/
def SerializeRoundTrip : Prop := ∀ p : G.PK, G.deserialize (G.serialize p) = .ok p

/-- **Assumption** on the parser: it accepts only canonical encodings, so every
accepted string is the serialization of what it parses to. For X25519 and X448
this is immediate, as RFC 9180 Section 7.1.1 makes both functions the
identity; for the NIST curves it holds because `parse_public_bytes` demands the
`0x04` prefix and mirage-crypto-ec rejects coordinates `≥ p`
(`check_coordinate`) and points off the curve. -/
def CanonicalEncoding : Prop :=
  ∀ (b : Bytes) (p : G.PK), G.deserialize b = .ok p → G.serialize p = b

/-- **Assumption** on the library: its exchange on octets that the HPKE parser
accepts computes `DH` on the parsed key (success and value; the error text is
irrelevant). mirage-crypto-ec's `key_exchange` reparses with the same
`P.of_octets` as `pub_of_octets` and rejects the point at infinity. -/
def ExchangeIsDh : Prop :=
  ∀ (sk : G.SK) (b : Bytes) (p : G.PK),
    G.deserialize b = .ok p → (G.exchange sk b).toOption = G.dh sk p

/-- **Assumption** on the library: the public encoding returned with a secret
is `SerializePublicKey(pk(sk))`. -/
def PublicOctetsSerialize : Prop := ∀ sk : G.SK, G.publicOctets sk = G.serialize (G.pk sk)

end DhGroup

/-- One ML-KEM parameter set of FIPS 203 with the octet codecs of the OCaml
`MLKEM` signature (lines 355-380). Errors are the text of `M.pp_error`.

* `dkOfSeed` is `decapsulation_key_of_seed` (`expandDecapsKey` of the draft,
  i.e. `ML-KEM.KeyGen_internal(d, z)`), `ekOfDk` is
  `encapsulation_key_of_decapsulation_key`;
* `ekOfOctets` is the length check of line 429 followed by
  `encapsulation_key_of_octets`, the encapsulation-key check of FIPS 203
  Section 7.2;
* `ctOfOctets` is `ciphertext_of_octets`, the ciphertext type check;
* `encaps ek coins` is `ML-KEM.Encaps` run on the randomness `coins` that
  `encapsulate ~random` draws; `decaps` is `ML-KEM.Decaps`. -/
structure MlKem where
  DK : Type
  EK : Type
  CT : Type
  SS : Type
  Coins : Type
  dkOfSeed : Bytes → Except String DK
  ekOfDk : DK → EK
  ekOfOctets : Bytes → Except String EK
  ekToOctets : EK → Bytes
  ctOfOctets : Bytes → Except String CT
  ctToOctets : CT → Bytes
  ssToOctets : SS → Bytes
  encaps : EK → Coins → CT × SS
  decaps : DK → CT → SS

namespace MlKem

variable (M : MlKem)

/-- **Assumption** (FIPS 203 correctness): `Decaps(dk, c) = K` whenever
`(c, K) = Encaps(ek(dk), coins)`. FIPS 203 only bounds the failure probability
(about `2^-139`, `2^-165`, `2^-175` for the three parameter sets); this
idealises it to zero. -/
def Correct : Prop :=
  ∀ (dk : M.DK) (coins : M.Coins),
    M.decaps dk (M.encaps (M.ekOfDk dk) coins).1 = (M.encaps (M.ekOfDk dk) coins).2

/-- **Assumption** on the library: `ciphertext_of_octets` accepts what
`ciphertext_to_octets` produced. -/
def CiphertextRoundTrip : Prop := ∀ c : M.CT, M.ctOfOctets (M.ctToOctets c) = .ok c

end MlKem

/-! ## `Mlkem_kem` (lines 385-413) -/

namespace MlkemKem

variable (M : MlKem)

/-- `Mlkem_kem.public_key` (lines 389-392). -/
def publicKey (bytes : Bytes) : Except Err M.EK :=
  match M.ekOfOctets bytes with
  | .error reason => .error (.invalidPublicKey reason)
  | .ok ek => .ok ek

/-- `Mlkem_kem.private_key` (lines 394-399). -/
def privateKey (seed : Bytes) : Except Err (M.DK × M.EK × Bytes) :=
  match M.dkOfSeed seed with
  | .error reason => .error (.invalidPrivateKey reason)
  | .ok secret =>
    let pub := M.ekOfDk secret
    .ok (secret, pub, M.ekToOctets pub)

/-- `Mlkem_kem.encap` (lines 401-403): `(shared_secret, ciphertext)`. -/
def encap (coins : M.Coins) (pub : M.EK) : Bytes × Bytes :=
  (M.ssToOctets (M.encaps pub coins).2, M.ctToOctets (M.encaps pub coins).1)

/-- `Mlkem_kem.decap` (lines 408-412). -/
def decap (secret : M.DK) (encapsulatedKey : Bytes) : Except Err Bytes :=
  match M.ctOfOctets encapsulatedKey with
  | .error reason => .error (.invalidEncapsulation reason)
  | .ok ciphertext => .ok (M.ssToOctets (M.decaps secret ciphertext))

end MlkemKem

/-- A nominal group as `Hybrid_kem` uses it (the OCaml `NOMINAL_GROUP`
signature, draft-irtf-cfrg-hybrid-kems Section 3.2).

* `randomScalar seed` is `random_scalar`: `RandomScalar(seed)` together with
  `Exp(g, scalar)`, or `none` when the seed holds no valid scalar. For P-256
  and P-384 its choice of scalar is `Scalar.randomScalar`, proved equal to the
  concrete draft's loop in `Scalar.lean`; for X25519 the seed is the scalar.
* `checkElement` is `check_element`, applied to a received public element.
  The OCaml returns an `Error.t`, always `Invalid_public_key` (from
  `nist_public_key`); the mirror keeps its reason.
* `sharedSecret sk e` is `shared_secret`:
  `ElementToSharedSecret(Exp(e, sk))`, or the reason `e` was refused. -/
structure NominalGroup where
  Scalar : Type
  randomScalar : Bytes → Option (Scalar × Bytes)
  checkElement : Bytes → Except String Unit
  sharedSecret : Scalar → Bytes → Except String Bytes

namespace NominalGroup

variable (G : NominalGroup)

/-- **Assumption** (the Diffie-Hellman property on elements): two scalars
reach the same shared secret from each other's element. -/
def Commutes : Prop :=
  ∀ (s₁ s₂ : Bytes) (a b : G.Scalar) (ea eb : Bytes),
    G.randomScalar s₁ = some (a, ea) → G.randomScalar s₂ = some (b, eb) →
      G.sharedSecret a eb = G.sharedSecret b ea

/-- **Assumption**: elements have the fixed length `Nelem`. -/
def ElementLength (n : Nat) : Prop :=
  ∀ (s : Bytes) (a : G.Scalar) (e : Bytes), G.randomScalar s = some (a, e) → e.length = n

/-- **Assumption**: an element the exchange accepts also passes the public-key
check. For P-256 and P-384 both are mirage-crypto-ec's point decoding; for
X25519 the check accepts everything. -/
def CheckElementSound : Prop :=
  ∀ (sk : G.Scalar) (e v : Bytes), G.sharedSecret sk e = .ok v → G.checkElement e = .ok ()

end NominalGroup

/-- The components of one `Hybrid_kem` functor application: its `Params`
(`kem`, `pq`, `label`), the ML-KEM parameter set `M`, the nominal group `G`
with its `Nseed` and `Nelem`, SHAKE256 as the PRG (`prg seed n`, the first
`n` bytes), SHA3-256 as the KDF, and `coins`, the ML-KEM randomness that
`~random:(fun _ -> String.sub randomness 0 32)` makes of 32 bytes. -/
structure HybridPrims where
  kem : KemId
  pq : KemId
  M : MlKem
  G : NominalGroup
  seedSize : Nat
  elementSize : Nat
  prg : Bytes → Nat → Bytes
  kdf : Bytes → Bytes
  coins : Bytes → M.Coins
  label : Bytes

/-! ## `Hybrid_kem` -/

namespace HybridKem

variable (H : HybridPrims)

/-- `Hybrid_kem.public`. -/
structure Public where
  pq : H.M.EK
  element : Bytes

/-- `Hybrid_kem.secret`. -/
structure Secret where
  pq : H.M.DK
  scalar : H.G.Scalar
  ownElement : Bytes

/-- `Hybrid_kem.public_key`; the caller has checked the length. -/
def publicKey (bytes : Bytes) : Except Err (Public H) := do
  let pq ← MlkemKem.publicKey H.M (bytes.take H.pq.publicKeySize)
  let element := (bytes.drop H.pq.publicKeySize).take H.elementSize
  match H.G.checkElement element with
  | .error reason => .error (.invalidPublicKey reason)
  | .ok () => pure ⟨pq, element⟩

/-- `Hybrid_kem.private_key`: `expandDecapsKey`, with the public key's
encoding. -/
def privateKey (seed : Bytes) : Except Err (Secret H × Public H × Bytes) :=
  let expanded := H.prg seed (H.pq.privateKeySize + H.seedSize)
  match H.G.randomScalar ((expanded.drop H.pq.privateKeySize).take H.seedSize) with
  | none => .error (.invalidPrivateKey "the seed yields no scalar")
  | some (scalar, ownElement) =>
    match MlkemKem.privateKey H.M (expanded.take H.pq.privateKeySize) with
    | .error e => .error e
    | .ok (pqSecret, pqPublic, pqBytes) =>
      .ok (⟨pqSecret, scalar, ownElement⟩, ⟨pqPublic, ownElement⟩, pqBytes ++ ownElement)

/-- `Hybrid_kem.combine`. -/
def combine (pqSecret groupSecret groupCiphertext element : Bytes) : Bytes :=
  H.kdf (pqSecret ++ groupSecret ++ groupCiphertext ++ element ++ H.label)

/-- The `attempt` loop of `Hybrid_kem.encap`. `draw made` is the
`(32 + Nseed)`-byte output of the generator's `made`-th call, and `remaining`
OCaml's counter. -/
def attempt (draw : Nat → Bytes) (pub : Public H) (made remaining : Nat) :
    Except Err (Bytes × Bytes) :=
    let randomness := draw made
    match H.G.randomScalar ((randomness.drop 32).take H.seedSize) with
    | none =>
      if remaining > 1 then attempt draw pub (made + 1) (remaining - 1)
      else .error (.internalError "no ephemeral scalar could be sampled")
    | some (ephemeral, groupCiphertext) =>
      match H.G.sharedSecret ephemeral pub.element with
      | .error reason => .error (.invalidPublicKey reason)
      | .ok groupSecret =>
        let (pqSecret, pqCiphertext) :=
          MlkemKem.encap H.M (H.coins (randomness.take 32)) pub.pq
        .ok (combine H pqSecret groupSecret groupCiphertext pub.element,
          pqCiphertext ++ groupCiphertext)
termination_by remaining
decreasing_by omega

/-- `Hybrid_kem.encap`: `attempt 8`. -/
def encap (draw : Nat → Bytes) (pub : Public H) : Except Err (Bytes × Bytes) :=
  attempt H draw pub 0 8

/-- `Hybrid_kem.decap`. -/
def decap (sec : Secret H) (encapsulatedKey : Bytes) : Except Err Bytes :=
  if encapsulatedKey.length ≠ H.kem.encapsulatedKeySize then
    .error (.invalidEncapsulation "wrong encoded length")
  else
    let groupCiphertext :=
      (encapsulatedKey.drop H.pq.encapsulatedKeySize).take H.elementSize
    match H.G.sharedSecret sec.scalar groupCiphertext with
    | .error reason => .error (.invalidEncapsulation reason)
    | .ok groupSecret =>
      match MlkemKem.decap H.M sec.pq (encapsulatedKey.take H.pq.encapsulatedKeySize) with
      | .error e => .error e
      | .ok pqSecret => .ok (combine H pqSecret groupSecret groupCiphertext sec.ownElement)

/-- `public_key` fails only with `Invalid_public_key`. -/
theorem publicKey_error (bytes : Bytes) (e : Err) (h : publicKey H bytes = .error e) :
    ∃ r, e = .invalidPublicKey r := by
  unfold publicKey MlkemKem.publicKey at h
  cases h1 : H.M.ekOfOctets (bytes.take H.pq.publicKeySize) with
  | error r => simp [h1, bind, Except.bind] at h; exact ⟨r, h.symm⟩
  | ok ek =>
    cases h2 : H.G.checkElement ((bytes.drop H.pq.publicKeySize).take H.elementSize) with
    | error r => simp [h1, h2, bind, Except.bind] at h; exact ⟨r, h.symm⟩
    | ok u => simp [h1, h2, bind, Except.bind, pure, Except.pure] at h

end HybridKem

/-- The primitives of every KEM of the registry: one Diffie-Hellman group, one
ML-KEM parameter set and one hybrid per identifier (only the right kind is ever
used for a given identifier), and the labeled KDF. -/
structure Prims where
  kdf : KemKdf
  G : KemId → DhGroup
  M : KemId → MlKem
  H : KemId → HybridPrims

variable (P : Prims)

/-! ## Keys (lines 419-590) -/

/-- `public_material` (lines 422-426): nothing for a DHKEM, whose key is used as
bytes, the parsed encapsulation key for ML-KEM, and `Hybrid_kem.public` for a
hybrid. -/
inductive PublicMaterial (kem : KemId) where
  | dhPublic
  | mlkem (ek : (P.M kem).EK)
  | hybrid (pub : HybridKem.Public (P.H kem))

/-- `Public_key.t` (line 482). -/
structure PublicKey where
  kem : KemId
  bytes : Bytes
  material : PublicMaterial P kem

/-- `kem_secret` (lines 496-504). -/
inductive Secret (kem : KemId) where
  | dh (sk : (P.G kem).SK)
  | mlkem (dk : (P.M kem).DK)
  | hybrid (sec : HybridKem.Secret (P.H kem))

/-- `Private_key.t` (lines 561-566). -/
structure PrivateKey where
  kem : KemId
  bytes : Bytes
  secret : Secret P kem
  publicKey : PublicKey P

/-- Mirror of `Public_key.of_bytes` with `parse_public_bytes` (lines 428-490). -/
def publicKeyOfBytes (kem : KemId) (bytes : Bytes) : Except Err (PublicKey P) :=
  if kem.isDh then
    match (P.G kem).deserialize bytes with
    | .error reason => .error (.invalidPublicKey reason)
    | .ok _ => .ok { kem, bytes, material := .dhPublic }
  else if kem.isHybrid then
    if bytes.length ≠ kem.publicKeySize then .error (.invalidPublicKey "wrong encoded length")
    else
      match HybridKem.publicKey (P.H kem) bytes with
      | .error e => .error e
      | .ok pub => .ok { kem, bytes, material := .hybrid pub }
  else
    match (P.M kem).ekOfOctets bytes with
    | .error reason => .error (.invalidPublicKey reason)
    | .ok ek => .ok { kem, bytes, material := .mlkem ek }

/-- The public key `Public_key.of_bytes ~kem bytes` returns for a DHKEM when
parsing succeeds. -/
def dhPublicKey (kem : KemId) (bytes : Bytes) : PublicKey P :=
  { kem, bytes, material := .dhPublic }

/-- The private key `Private_key.of_bytes` returns for a DHKEM secret `sk`
(lines 509-515, 568-585): its public half is the library's encoding of
`pk(sk)`, reparsed by `Public_key.of_bytes` (see `publicKeyOfBytes_publicOctets`). -/
def dhPrivateKey (kem : KemId) (bytes : Bytes) (sk : (P.G kem).SK) : PrivateKey P :=
  { kem, bytes, secret := .dh sk, publicKey := dhPublicKey P kem ((P.G kem).publicOctets sk) }

/-- The private key `Private_key.of_bytes` returns for an ML-KEM seed whose
expanded decapsulation key is `dk` (lines 516-521, 568-585). -/
def mlkemPrivateKey (kem : KemId) (seed : Bytes) (dk : (P.M kem).DK) : PrivateKey P :=
  { kem, bytes := seed, secret := .mlkem dk,
    publicKey := { kem, bytes := (P.M kem).ekToOctets ((P.M kem).ekOfDk dk),
                   material := .mlkem ((P.M kem).ekOfDk dk) } }


/-- Mirror of `Private_key.of_bytes` for an ML-KEM identifier (lines 568-585
with the `mlkem` branch of `secret_and_public`); the length check of line 569
is part of `dkOfSeed`. -/
def mlkemPrivateKeyOfBytes (kem : KemId) (seed : Bytes) : Except Err (PrivateKey P) :=
  match MlkemKem.privateKey (P.M kem) seed with
  | .error e => .error e
  | .ok (secret, pub, bytes) =>
    .ok { kem, bytes := seed, secret := .mlkem secret,
          publicKey := { kem, bytes, material := .mlkem pub } }

/-! ## The KEM mirrors (lines 744-870) -/

/-- Mirror of `dh` (lines 744-769). -/
def dh (sk : PrivateKey P) (pk : PublicKey P) : Except Err Bytes :=
  if sk.kem ≠ pk.kem then .error .keyMismatch
  else
    match sk.secret with
    | .dh s =>
      match (P.G sk.kem).exchange s pk.bytes with
      | .ok v => .ok v
      | .error reason => .error (.invalidPublicKey reason)
    | .mlkem _ =>
      .error (.invalidPrivateKey "ML-KEM keys cannot perform a Diffie-Hellman exchange")
    | .hybrid _ =>
      .error (.invalidPrivateKey "hybrid KEM keys cannot perform a Diffie-Hellman exchange")

/-- Mirror of `extract_and_expand` (lines 771-774). -/
def extractAndExpand (kem : KemId) (dh kemContext : Bytes) : Bytes :=
  let eaePrk := P.kdf.labeledExtract kem [] (ascii "eae_prk") dh
  P.kdf.labeledExpand kem eaePrk (ascii "shared_secret") kemContext kem.secretSize

/-- Mirror of `encap_with` (lines 780-798). -/
def encapWith (ephemeral : PrivateKey P) (sender : Option (PrivateKey P))
    (recipient : PublicKey P) : Except Err (Bytes × Bytes) := do
  let kem := recipient.kem
  let ephemeralDh ← dh P ephemeral recipient
  let (staticDh, senderPublic) ←
    match sender with
    | none => pure ([], [])
    | some sender => do
      let staticDh ← dh P sender recipient
      pure (staticDh, sender.publicKey.bytes)
  let encapsulatedKey := ephemeral.publicKey.bytes
  let kemContext := encapsulatedKey ++ recipient.bytes ++ senderPublic
  pure (extractAndExpand P kem (ephemeralDh ++ staticDh) kemContext, encapsulatedKey)

/-- Mirror of `mlkem_without_sender` (lines 804-806). -/
def mlkemWithoutSender {α : Type} : Option α → Except Err Unit
  | none => .ok ()
  | some _ => .error .unsupportedMode

/-- Mirror of `encap` (lines 808-822). The generator's effects are explicit:
`generate kem` is what `generate_key_pair ~rng kem` returns (its private half),
`coins kem` is the randomness `Mlkem_kem.encap ~random` draws, and
`draw kem i` the `i`-th draw of `Hybrid_kem.encap`. -/
def encap (generate : KemId → Except Err (PrivateKey P))
    (coins : (kem : KemId) → (P.M kem).Coins) (draw : KemId → Nat → Bytes)
    (sender : Option (PrivateKey P)) (recipient : PublicKey P) :
    Except Err (Bytes × Bytes) :=
  match recipient.material with
  | .dhPublic => do
    let ephemeral ← generate recipient.kem
    encapWith P ephemeral sender recipient
  | .mlkem pub => do
    mlkemWithoutSender sender
    pure (MlkemKem.encap (P.M recipient.kem) (coins recipient.kem) pub)
  | .hybrid pub => do
    mlkemWithoutSender sender
    HybridKem.encap (P.H recipient.kem) (draw recipient.kem) pub

/-- Mirror of `dh_decap` (lines 824-855). -/
def dhDecap (recipient : PrivateKey P) (sender : Option (PublicKey P))
    (encapsulatedKey : Bytes) : Except Err Bytes := do
  let kem := recipient.kem
  let encapsulated ←
    match publicKeyOfBytes P kem encapsulatedKey with
    | .ok key => .ok key
    | .error (.invalidPublicKey reason) => .error (.invalidEncapsulation reason)
    | .error error => .error error
  let ephemeralDh ←
    match dh P recipient encapsulated with
    | .error (.invalidPublicKey reason) => .error (.invalidEncapsulation reason)
    | result => result
  let (staticDh, senderPublic) ←
    match sender with
    | none => pure ([], [])
    | some sender => do
      let staticDh ← dh P recipient sender
      pure (staticDh, sender.bytes)
  let kemContext := encapsulatedKey ++ recipient.publicKey.bytes ++ senderPublic
  pure (extractAndExpand P kem (ephemeralDh ++ staticDh) kemContext)

/-- Mirror of `decap` (lines 857-870). -/
def decap (recipient : PrivateKey P) (sender : Option (PublicKey P))
    (encapsulatedKey : Bytes) : Except Err Bytes :=
  match recipient.secret with
  | .dh _ => dhDecap P recipient sender encapsulatedKey
  | .mlkem secret => do
    mlkemWithoutSender sender
    MlkemKem.decap (P.M recipient.kem) secret encapsulatedKey
  | .hybrid secret => do
    mlkemWithoutSender sender
    HybridKem.decap (P.H recipient.kem) secret encapsulatedKey

/-! ## RFC 9180 Section 4.1, transcribed -/

namespace Rfc

variable (K : KemKdf) (kem : KemId) (G : DhGroup)

/-- `Nsecret`, from the registry table (RFC 9180 Table 2). -/
def Nsecret : Nat := (kemTable kem).nsecret

/-- `LabeledExtract(salt, label, ikm)` with the KEM's `suite_id`. -/
def LabeledExtract (salt label ikm : Bytes) : Bytes := K.labeledExtract kem salt label ikm

/-- `LabeledExpand(prk, label, info, L)` with the KEM's `suite_id`. -/
def LabeledExpand (prk label info : Bytes) (L : Nat) : Bytes := K.labeledExpand kem prk label info L

/-- `DeserializePublicKey`; a `DeserializeError` is `none`. -/
def DeserializePublicKey (enc : Bytes) : Option G.PK := (G.deserialize enc).toOption

/-- ```
def ExtractAndExpand(dh, kem_context):
  eae_prk = LabeledExtract("", "eae_prk", dh)
  shared_secret = LabeledExpand(eae_prk, "shared_secret",
                                kem_context, Nsecret)
  return shared_secret
``` -/
def ExtractAndExpand (dh kem_context : Bytes) : Bytes :=
  let eae_prk := LabeledExtract K kem (ascii "") (ascii "eae_prk") dh
  let shared_secret :=
    LabeledExpand K kem eae_prk (ascii "shared_secret") kem_context (Nsecret kem)
  shared_secret

/-- ```
def Encap(pkR):
  skE, pkE = GenerateKeyPair()
  dh = DH(skE, pkR)
  enc = SerializePublicKey(pkE)

  pkRm = SerializePublicKey(pkR)
  kem_context = concat(enc, pkRm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret, enc
```
`GenerateKeyPair()` is randomized; its output `(skE, pk(skE))` is an argument. -/
def Encap (skE : G.SK) (pkR : G.PK) : Option (Bytes × Bytes) := do
  let pkE := G.pk skE
  let dh ← G.dh skE pkR
  let enc := G.serialize pkE
  let pkRm := G.serialize pkR
  let kem_context := enc ++ pkRm
  let shared_secret := ExtractAndExpand K kem dh kem_context
  return (shared_secret, enc)

/-- ```
def Decap(enc, skR):
  pkE = DeserializePublicKey(enc)
  dh = DH(skR, pkE)

  pkRm = SerializePublicKey(pk(skR))
  kem_context = concat(enc, pkRm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret
``` -/
def Decap (enc : Bytes) (skR : G.SK) : Option Bytes := do
  let pkE ← DeserializePublicKey G enc
  let dh ← G.dh skR pkE
  let pkRm := G.serialize (G.pk skR)
  let kem_context := enc ++ pkRm
  let shared_secret := ExtractAndExpand K kem dh kem_context
  return shared_secret

/-- ```
def AuthEncap(pkR, skS):
  skE, pkE = GenerateKeyPair()
  dh = concat(DH(skE, pkR), DH(skS, pkR))
  enc = SerializePublicKey(pkE)

  pkRm = SerializePublicKey(pkR)
  pkSm = SerializePublicKey(pk(skS))
  kem_context = concat(enc, pkRm, pkSm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret, enc
``` -/
def AuthEncap (skE : G.SK) (pkR : G.PK) (skS : G.SK) : Option (Bytes × Bytes) := do
  let pkE := G.pk skE
  let dhE ← G.dh skE pkR
  let dhS ← G.dh skS pkR
  let dh := dhE ++ dhS
  let enc := G.serialize pkE
  let pkRm := G.serialize pkR
  let pkSm := G.serialize (G.pk skS)
  let kem_context := enc ++ pkRm ++ pkSm
  let shared_secret := ExtractAndExpand K kem dh kem_context
  return (shared_secret, enc)

/-- ```
def AuthDecap(enc, skR, pkS):
  pkE = DeserializePublicKey(enc)
  dh = concat(DH(skR, pkE), DH(skR, pkS))

  pkRm = SerializePublicKey(pk(skR))
  pkSm = SerializePublicKey(pkS)
  kem_context = concat(enc, pkRm, pkSm)

  shared_secret = ExtractAndExpand(dh, kem_context)
  return shared_secret
``` -/
def AuthDecap (enc : Bytes) (skR : G.SK) (pkS : G.PK) : Option Bytes := do
  let pkE ← DeserializePublicKey G enc
  let dhE ← G.dh skR pkE
  let dhS ← G.dh skR pkS
  let dh := dhE ++ dhS
  let pkRm := G.serialize (G.pk skR)
  let pkSm := G.serialize pkS
  let kem_context := enc ++ pkRm ++ pkSm
  let shared_secret := ExtractAndExpand K kem dh kem_context
  return shared_secret

/-- A variant of `Decap` that puts `SerializePublicKey(DeserializePublicKey(enc))`
rather than `enc` into `kem_context`. It is *not* the RFC's text; it is here to
state what the canonical-encoding assumption buys. -/
def DecapReserialized (enc : Bytes) (skR : G.SK) : Option Bytes := do
  let pkE ← DeserializePublicKey G enc
  let dh ← G.dh skR pkE
  let pkRm := G.serialize (G.pk skR)
  let kem_context := G.serialize pkE ++ pkRm
  return ExtractAndExpand K kem dh kem_context

/-- With canonical encodings the two formulations of `Decap` coincide. -/
theorem Decap_eq_reserialized (hcanon : G.CanonicalEncoding) (enc : Bytes) (skR : G.SK) :
    Decap K kem G enc skR = DecapReserialized K kem G enc skR := by
  unfold Decap DecapReserialized DeserializePublicKey
  cases h : G.deserialize enc with
  | error _ => rfl
  | ok p => simp [Except.toOption, hcanon enc p h]

end Rfc

/-! ## draft-ietf-hpke-pq-05 Section 3, transcribed -/

namespace Draft

variable (M : MlKem)

/-- `Encap(pkR)`: "corresponds to the function ML-KEM.Encaps in [FIPS203],
where an ML-KEM encapsulation key check failure causes an HPKE EncapError".
`SerializePublicKey` and `DeserializePublicKey` are the identity, so `pkR` is
the encapsulation key's bytes; `Encaps`'s randomness is an argument. -/
def Encap (pkR : Bytes) (coins : M.Coins) : Option (Bytes × Bytes) := do
  let ek ← (M.ekOfOctets pkR).toOption
  let (c, K) := M.encaps ek coins
  return (M.ssToOctets K, M.ctToOctets c)

/-- ```
def Decap(enc, skR):
    (expanded_dk, _ek) = expandDecapsKey(skR)
    return ML-KEM.Decaps(expanded_dk, enc)
```
where a ciphertext check failure is a `DecapError`. -/
def Decap (enc : Bytes) (skR : Bytes) : Option Bytes := do
  let expanded_dk ← (M.dkOfSeed skR).toOption
  let c ← (M.ctOfOctets enc).toOption
  return M.ssToOctets (M.decaps expanded_dk c)

end Draft

/-! ## Helper lemmas -/

theorem toOption_eq_some {ε α : Type} {x : Except ε α} {a : α} :
    x.toOption = some a ↔ x = .ok a := by
  cases x <;> simp [Except.toOption]

theorem toOption_eq_none {ε α : Type} {x : Except ε α} :
    x.toOption = none ↔ ∃ e, x = .error e := by
  cases x <;> simp [Except.toOption]

theorem secretSize_eq_Nsecret (kem : KemId) : kem.secretSize = Rfc.Nsecret kem := by
  cases kem <;> rfl

/-- The mirror's `extract_and_expand` is the RFC's `ExtractAndExpand`, `Nsecret`
included (`Kem.secret_size` agrees with Table 2). -/
theorem extractAndExpand_eq (kem : KemId) (dh kemContext : Bytes) :
    extractAndExpand P kem dh kemContext = Rfc.ExtractAndExpand P.kdf kem dh kemContext := by
  simp [extractAndExpand, Rfc.ExtractAndExpand, Rfc.LabeledExtract, Rfc.LabeledExpand,
    ascii_empty, secretSize_eq_Nsecret]

theorem dh_dhPrivateKey (kem : KemId) (b : Bytes) (sk : (P.G kem).SK) (pk : PublicKey P)
    (hk : pk.kem = kem) :
    dh P (dhPrivateKey P kem b sk) pk =
      match (P.G kem).exchange sk pk.bytes with
      | .ok v => .ok v
      | .error reason => .error (.invalidPublicKey reason) := by
  simp [dh, dhPrivateKey, hk]

theorem deserialize_publicOctets (kem : KemId)
    (hR : (P.G kem).SerializeRoundTrip) (hO : (P.G kem).PublicOctetsSerialize)
    (sk : (P.G kem).SK) :
    (P.G kem).deserialize ((P.G kem).publicOctets sk) = .ok ((P.G kem).pk sk) := by
  rw [hO]; exact hR _

/-- `secret_and_public` reparses the library's public encoding; under the
round-trip assumptions that parse succeeds and yields the key's public half. -/
theorem publicKeyOfBytes_publicOctets (kem : KemId) (hdh : kem.isDh = true)
    (hR : (P.G kem).SerializeRoundTrip) (hO : (P.G kem).PublicOctetsSerialize)
    (b : Bytes) (sk : (P.G kem).SK) :
    publicKeyOfBytes P kem ((P.G kem).publicOctets sk) = .ok (dhPrivateKey P kem b sk).publicKey := by
  simp [publicKeyOfBytes, hdh, deserialize_publicOctets P kem hR hO, dhPrivateKey, dhPublicKey]

/-- `parse_public_bytes` fails only with `Invalid_public_key`, so the
`| Error error -> Error error` branch of `dh_decap` (line 831) is dead code. -/
theorem publicKeyOfBytes_error (kem : KemId) (b : Bytes) (e : Err)
    (h : publicKeyOfBytes P kem b = .error e) : ∃ r, e = .invalidPublicKey r := by
  unfold publicKeyOfBytes at h
  by_cases hd : kem.isDh = true
  · rw [ite_eq_left hd] at h
    split at h <;> cases h; exact ⟨_, rfl⟩
  · rw [ite_eq_right hd] at h
    by_cases hh : kem.isHybrid = true
    · rw [ite_eq_left hh] at h
      by_cases hl : b.length ≠ kem.publicKeySize
      · rw [ite_eq_left hl] at h; cases h; exact ⟨_, rfl⟩
      · rw [ite_eq_right hl] at h
        cases hp : HybridKem.publicKey (P.H kem) b with
        | error e' =>
          rw [hp] at h; cases h
          exact HybridKem.publicKey_error (P.H kem) b _ hp
        | ok pub => rw [hp] at h; cases h
    · rw [ite_eq_right hh] at h
      split at h <;> cases h; exact ⟨_, rfl⟩

/-! ## 1. Mirrors equal the RFC -/

/-- `encap_with ~ephemeral ~sender:None` is RFC 9180 `Encap` with `skE` the
ephemeral secret. The recipient key given as `rb` (its bytes, which is what
`Public_key.t` keeps) must be the canonical encoding of the parsed `pkR`. -/
theorem encapWith_none_eq_Encap (kem : KemId)
    (hX : (P.G kem).ExchangeIsDh) (hO : (P.G kem).PublicOctetsSerialize)
    (eb : Bytes) (skE : (P.G kem).SK) (rb : Bytes) (pR : (P.G kem).PK)
    (hparse : (P.G kem).deserialize rb = .ok pR) (hcanon : (P.G kem).serialize pR = rb) :
    (encapWith P (dhPrivateKey P kem eb skE) none (dhPublicKey P kem rb)).toOption
      = Rfc.Encap P.kdf kem (P.G kem) skE pR := by
  have hx := hX skE rb pR hparse
  cases h : (P.G kem).exchange skE rb with
  | error r =>
    rw [h] at hx
    simp only [Except.toOption] at hx
    simp [encapWith, Rfc.Encap, dh, dhPrivateKey, dhPublicKey, h, ← hx, bind, Except.bind,
      Except.toOption]
  | ok v =>
    rw [h] at hx
    simp only [Except.toOption] at hx
    simp [encapWith, Rfc.Encap, dh, dhPrivateKey, dhPublicKey, h, ← hx, bind, Except.bind,
      pure, Except.pure, hO skE, hcanon, extractAndExpand_eq, Except.toOption]

/-- `encap_with ~ephemeral ~sender:(Some skS)` is RFC 9180 `AuthEncap`. -/
theorem encapWith_some_eq_AuthEncap (kem : KemId)
    (hX : (P.G kem).ExchangeIsDh) (hO : (P.G kem).PublicOctetsSerialize)
    (eb sb : Bytes) (skE skS : (P.G kem).SK) (rb : Bytes) (pR : (P.G kem).PK)
    (hparse : (P.G kem).deserialize rb = .ok pR) (hcanon : (P.G kem).serialize pR = rb) :
    (encapWith P (dhPrivateKey P kem eb skE) (some (dhPrivateKey P kem sb skS))
        (dhPublicKey P kem rb)).toOption
      = Rfc.AuthEncap P.kdf kem (P.G kem) skE pR skS := by
  have hxE := hX skE rb pR hparse
  have hxS := hX skS rb pR hparse
  cases h : (P.G kem).exchange skE rb with
  | error r =>
    rw [h] at hxE
    simp only [Except.toOption] at hxE
    simp [encapWith, Rfc.AuthEncap, dh, dhPrivateKey, dhPublicKey, h, ← hxE, bind,
      Except.bind, Except.toOption]
  | ok v =>
    rw [h] at hxE
    simp only [Except.toOption] at hxE
    cases h' : (P.G kem).exchange skS rb with
    | error r =>
      rw [h'] at hxS
      simp only [Except.toOption] at hxS
      simp [encapWith, Rfc.AuthEncap, dh, dhPrivateKey, dhPublicKey, h, h', ← hxE, ← hxS,
        bind, Except.bind, Except.toOption]
    | ok w =>
      rw [h'] at hxS
      simp only [Except.toOption] at hxS
      simp [encapWith, Rfc.AuthEncap, dh, dhPrivateKey, dhPublicKey, h, h', ← hxE, ← hxS,
        bind, Except.bind, pure, Except.pure, hO skE, hO skS, hcanon, extractAndExpand_eq,
        Except.toOption]

/-- `dh_decap ~sender:None` is RFC 9180 `Decap`. No assumption about the parser
is needed: both put the received `enc` itself into `kem_context`. -/
theorem dhDecap_none_eq_Decap (kem : KemId) (hdh : kem.isDh = true)
    (hX : (P.G kem).ExchangeIsDh) (hO : (P.G kem).PublicOctetsSerialize)
    (rb : Bytes) (skR : (P.G kem).SK) (enc : Bytes) :
    (dhDecap P (dhPrivateKey P kem rb skR) none enc).toOption
      = Rfc.Decap P.kdf kem (P.G kem) enc skR := by
  cases hp : (P.G kem).deserialize enc with
  | error r =>
    simp [dhDecap, Rfc.Decap, Rfc.DeserializePublicKey, publicKeyOfBytes, hdh, hp,
      dhPrivateKey, Except.toOption, bind, Except.bind]
  | ok pE =>
    have hx := hX skR enc pE hp
    cases h : (P.G kem).exchange skR enc with
    | error r =>
      rw [h] at hx
      simp only [Except.toOption] at hx
      simp [dhDecap, Rfc.Decap, Rfc.DeserializePublicKey, publicKeyOfBytes, hdh, hp,
        dhPrivateKey, dhPublicKey, dh, h, ← hx, Except.toOption, bind, Except.bind]
    | ok v =>
      rw [h] at hx
      simp only [Except.toOption] at hx
      simp [dhDecap, Rfc.Decap, Rfc.DeserializePublicKey, publicKeyOfBytes, hdh, hp,
        dhPrivateKey, dhPublicKey, dh, h, ← hx, Except.toOption, bind, Except.bind, pure,
        Except.pure, hO skR, extractAndExpand_eq]

/-- `dh_decap ~sender:(Some pkS)` is RFC 9180 `AuthDecap`, for a sender key
given as the canonical encoding `sb` of `pkS`. -/
theorem dhDecap_some_eq_AuthDecap (kem : KemId) (hdh : kem.isDh = true)
    (hX : (P.G kem).ExchangeIsDh) (hO : (P.G kem).PublicOctetsSerialize)
    (rb : Bytes) (skR : (P.G kem).SK) (sb : Bytes) (pS : (P.G kem).PK)
    (hparseS : (P.G kem).deserialize sb = .ok pS) (hcanonS : (P.G kem).serialize pS = sb)
    (enc : Bytes) :
    (dhDecap P (dhPrivateKey P kem rb skR) (some (dhPublicKey P kem sb)) enc).toOption
      = Rfc.AuthDecap P.kdf kem (P.G kem) enc skR pS := by
  have hxS := hX skR sb pS hparseS
  cases hp : (P.G kem).deserialize enc with
  | error r =>
    simp [dhDecap, Rfc.AuthDecap, Rfc.DeserializePublicKey, publicKeyOfBytes, hdh, hp,
      dhPrivateKey, Except.toOption, bind, Except.bind]
  | ok pE =>
    have hx := hX skR enc pE hp
    cases h : (P.G kem).exchange skR enc with
    | error r =>
      rw [h] at hx
      simp only [Except.toOption] at hx
      simp [dhDecap, Rfc.AuthDecap, Rfc.DeserializePublicKey, publicKeyOfBytes, hdh, hp,
        dhPrivateKey, dhPublicKey, dh, h, ← hx, Except.toOption, bind, Except.bind]
    | ok v =>
      rw [h] at hx
      simp only [Except.toOption] at hx
      cases h' : (P.G kem).exchange skR sb with
      | error r =>
        rw [h'] at hxS
        simp only [Except.toOption] at hxS
        simp [dhDecap, Rfc.AuthDecap, Rfc.DeserializePublicKey, publicKeyOfBytes, hdh, hp,
          dhPrivateKey, dhPublicKey, dh, h, h', ← hxS, Except.toOption, bind, Except.bind]
      | ok w =>
        rw [h'] at hxS
        simp only [Except.toOption] at hxS
        simp [dhDecap, Rfc.AuthDecap, Rfc.DeserializePublicKey, publicKeyOfBytes, hdh, hp,
          dhPrivateKey, dhPublicKey, dh, h, h', ← hx, ← hxS, Except.toOption, bind,
          Except.bind, pure, Except.pure, hO skR, hcanonS, extractAndExpand_eq]

/-- Under the canonical-encoding assumption, any accepted encoding of the
recipient key may be used: `encap_with` is `Encap` for every `rb` that parses. -/
theorem encapWith_none_eq_Encap_of_canonical (kem : KemId)
    (hX : (P.G kem).ExchangeIsDh) (hO : (P.G kem).PublicOctetsSerialize)
    (hcanon : (P.G kem).CanonicalEncoding)
    (eb : Bytes) (skE : (P.G kem).SK) (rb : Bytes) (pR : (P.G kem).PK)
    (hparse : (P.G kem).deserialize rb = .ok pR) :
    (encapWith P (dhPrivateKey P kem eb skE) none (dhPublicKey P kem rb)).toOption
      = Rfc.Encap P.kdf kem (P.G kem) skE pR :=
  encapWith_none_eq_Encap P kem hX hO eb skE rb pR hparse (hcanon rb pR hparse)

/-- ... likewise `AuthEncap` ... -/
theorem encapWith_some_eq_AuthEncap_of_canonical (kem : KemId)
    (hX : (P.G kem).ExchangeIsDh) (hO : (P.G kem).PublicOctetsSerialize)
    (hcanon : (P.G kem).CanonicalEncoding)
    (eb sb : Bytes) (skE skS : (P.G kem).SK) (rb : Bytes) (pR : (P.G kem).PK)
    (hparse : (P.G kem).deserialize rb = .ok pR) :
    (encapWith P (dhPrivateKey P kem eb skE) (some (dhPrivateKey P kem sb skS))
        (dhPublicKey P kem rb)).toOption
      = Rfc.AuthEncap P.kdf kem (P.G kem) skE pR skS :=
  encapWith_some_eq_AuthEncap P kem hX hO eb sb skE skS rb pR hparse (hcanon rb pR hparse)

/-- ... and `dh_decap` is `AuthDecap` for every accepted sender encoding. -/
theorem dhDecap_some_eq_AuthDecap_of_canonical (kem : KemId) (hdh : kem.isDh = true)
    (hX : (P.G kem).ExchangeIsDh) (hO : (P.G kem).PublicOctetsSerialize)
    (hcanon : (P.G kem).CanonicalEncoding)
    (rb : Bytes) (skR : (P.G kem).SK) (sb : Bytes) (pS : (P.G kem).PK)
    (hparseS : (P.G kem).deserialize sb = .ok pS) (enc : Bytes) :
    (dhDecap P (dhPrivateKey P kem rb skR) (some (dhPublicKey P kem sb)) enc).toOption
      = Rfc.AuthDecap P.kdf kem (P.G kem) enc skR pS :=
  dhDecap_some_eq_AuthDecap P kem hdh hX hO rb skR sb pS hparseS (hcanon sb pS hparseS) enc

/-! ### The canonical-encoding assumption cannot be dropped

A one-point group whose parser accepts two encodings of its only key, with a
KDF that exposes `kem_context`: the mirror's `encap_with`, which uses the
caller's recipient bytes, then differs from `Encap`, which re-serializes. -/

namespace Counterexample

/-- One key, serialized as `[0]`, but `[1]` is accepted too. -/
def grp : DhGroup where
  SK := Unit
  PK := Unit
  pk _ := ()
  serialize _ := [0]
  deserialize _ := .ok ()
  dh _ _ := some []
  exchange _ _ := .ok []
  publicOctets _ := [0]

def mlkem : MlKem where
  DK := Unit
  EK := Unit
  CT := Unit
  SS := Unit
  Coins := Unit
  dkOfSeed _ := .ok ()
  ekOfDk _ := ()
  ekOfOctets _ := .ok ()
  ekToOctets _ := []
  ctOfOctets _ := .ok ()
  ctToOctets _ := []
  ssToOctets _ := []
  encaps _ _ := ((), ())
  decaps _ _ := ()

/-- `LabeledExpand` returns its `info`, i.e. the `kem_context`. -/
def prims : Prims where
  kdf := { labeledExtract := fun _ _ _ _ => [], labeledExpand := fun _ _ _ info _ => info }
  G := fun _ => grp
  M := fun _ => mlkem
  H := fun _ =>
    { kem := .mlkem768X25519, pq := .mlkem768, M := mlkem,
      G := { Scalar := Unit, randomScalar := fun _ => none, checkElement := fun _ => .ok (),
             sharedSecret := fun _ _ => .ok [] },
      seedSize := 0, elementSize := 0, prg := fun _ _ => [], kdf := id, coins := fun _ => (),
      label := [] }

end Counterexample

/-- Every assumption but canonicality holds in the counterexample, and there the
mirror of `encap_with` is not `Encap`. -/
theorem canonical_encoding_needed :
    ¬ (Counterexample.prims.G .x25519).CanonicalEncoding ∧
    (Counterexample.prims.G .x25519).ExchangeIsDh ∧
    (Counterexample.prims.G .x25519).PublicOctetsSerialize ∧
    (Counterexample.prims.G .x25519).SerializeRoundTrip ∧
    (Counterexample.prims.G .x25519).DhCommutes ∧
    (encapWith Counterexample.prims (dhPrivateKey Counterexample.prims .x25519 [] ())
        none (dhPublicKey Counterexample.prims .x25519 [1])).toOption
      ≠ Rfc.Encap Counterexample.prims.kdf .x25519 (Counterexample.prims.G .x25519) () () := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := h [1] () rfl
    simp [Counterexample.prims, Counterexample.grp] at this
  · intro _ _ _ _; rfl
  · intro _; rfl
  · intro _; rfl
  · intro _ _; rfl
  · simp [encapWith, Rfc.Encap, dh, dhPrivateKey, dhPublicKey, Counterexample.prims,
      Counterexample.grp, extractAndExpand, Rfc.ExtractAndExpand, Rfc.LabeledExpand,
      bind, Except.bind, pure, Except.pure, Except.toOption]

/-! ## 2. Correctness: decapsulation recovers the encapsulated secret -/

/-- Base mode: what `encap_with ~sender:None` produces for a recipient's public
key, `decap` with the recipient's private key turns back into the same shared
secret. -/
theorem decap_encapWith (kem : KemId) (hdh : kem.isDh = true)
    (hC : (P.G kem).DhCommutes) (hR : (P.G kem).SerializeRoundTrip)
    (hX : (P.G kem).ExchangeIsDh) (hO : (P.G kem).PublicOctetsSerialize)
    (eb rb : Bytes) (skE skR : (P.G kem).SK) {ss enc : Bytes}
    (h : encapWith P (dhPrivateKey P kem eb skE) none (dhPrivateKey P kem rb skR).publicKey
      = .ok (ss, enc)) :
    decap P (dhPrivateKey P kem rb skR) none enc = .ok ss := by
  have hpR := deserialize_publicOctets P kem hR hO skR
  have hpE := deserialize_publicOctets P kem hR hO skE
  have hx1 := hX skE _ _ hpR
  have hx2 := hX skR _ _ hpE
  rw [hC skR skE, ← hx1] at hx2
  cases h1 : (P.G kem).exchange skE ((P.G kem).publicOctets skR) with
  | error r =>
    simp [encapWith, dh, dhPrivateKey, dhPublicKey, h1, bind, Except.bind] at h
  | ok v =>
    rw [h1] at hx2
    have h2 := toOption_eq_some.mp hx2
    simp [encapWith, dh, dhPrivateKey, dhPublicKey, h1, bind, Except.bind, pure,
      Except.pure] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [decap, dhDecap, dhPrivateKey, dhPublicKey, publicKeyOfBytes, hdh, hpE, dh, h2,
      bind, Except.bind, pure, Except.pure]

/-- Auth mode: the receiver, given the sender's public key, recovers the secret
that `encap_with ~sender:(Some skS)` produced. -/
theorem decap_encapWith_auth (kem : KemId) (hdh : kem.isDh = true)
    (hC : (P.G kem).DhCommutes) (hR : (P.G kem).SerializeRoundTrip)
    (hX : (P.G kem).ExchangeIsDh) (hO : (P.G kem).PublicOctetsSerialize)
    (eb rb sb : Bytes) (skE skR skS : (P.G kem).SK) {ss enc : Bytes}
    (h : encapWith P (dhPrivateKey P kem eb skE) (some (dhPrivateKey P kem sb skS))
      (dhPrivateKey P kem rb skR).publicKey = .ok (ss, enc)) :
    decap P (dhPrivateKey P kem rb skR) (some (dhPrivateKey P kem sb skS).publicKey) enc
      = .ok ss := by
  have hpR := deserialize_publicOctets P kem hR hO skR
  have hpE := deserialize_publicOctets P kem hR hO skE
  have hpS := deserialize_publicOctets P kem hR hO skS
  have hxE := hX skE _ _ hpR
  have hxRE := hX skR _ _ hpE
  have hxS := hX skS _ _ hpR
  have hxRS := hX skR _ _ hpS
  rw [hC skR skE, ← hxE] at hxRE
  rw [hC skR skS, ← hxS] at hxRS
  cases h1 : (P.G kem).exchange skE ((P.G kem).publicOctets skR) with
  | error r =>
    simp [encapWith, dh, dhPrivateKey, dhPublicKey, h1, bind, Except.bind] at h
  | ok v =>
    rw [h1] at hxRE
    have h2 := toOption_eq_some.mp hxRE
    cases h3 : (P.G kem).exchange skS ((P.G kem).publicOctets skR) with
    | error r =>
      simp [encapWith, dh, dhPrivateKey, dhPublicKey, h1, h3, bind, Except.bind] at h
    | ok w =>
      rw [h3] at hxRS
      have h4 := toOption_eq_some.mp hxRS
      simp [encapWith, dh, dhPrivateKey, dhPublicKey, h1, h3, bind, Except.bind, pure,
        Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [decap, dhDecap, dhPrivateKey, dhPublicKey, publicKeyOfBytes, hdh, hpE, dh, h2, h4,
        bind, Except.bind, pure, Except.pure]

/-- The full DHKEM round trip through `encap`: if the generator yields keys as
`Private_key.of_bytes` builds them, `decap` recovers `encap`'s secret. -/
theorem decap_encap_dh (kem : KemId) (hdh : kem.isDh = true)
    (hC : (P.G kem).DhCommutes) (hR : (P.G kem).SerializeRoundTrip)
    (hX : (P.G kem).ExchangeIsDh) (hO : (P.G kem).PublicOctetsSerialize)
    (generate : KemId → Except Err (PrivateKey P)) (coins : (k : KemId) → (P.M k).Coins)
    (draw : KemId → Nat → Bytes)
    (hgen : ∀ e, generate kem = .ok e → ∃ eb skE, e = dhPrivateKey P kem eb skE)
    (rb : Bytes) (skR : (P.G kem).SK) {ss enc : Bytes}
    (h : encap P generate coins draw none (dhPrivateKey P kem rb skR).publicKey = .ok (ss, enc)) :
    decap P (dhPrivateKey P kem rb skR) none enc = .ok ss := by
  simp only [encap, dhPrivateKey, dhPublicKey] at h
  cases hg : generate kem with
  | error e => simp [hg, bind, Except.bind] at h
  | ok e =>
    obtain ⟨eb, skE, rfl⟩ := hgen e hg
    simp only [hg, bind, Except.bind] at h
    exact decap_encapWith P kem hdh hC hR hX hO eb rb skE skR h

/-- Same, authenticated: the receiver uses the sender's public key. -/
theorem decap_encap_dh_auth (kem : KemId) (hdh : kem.isDh = true)
    (hC : (P.G kem).DhCommutes) (hR : (P.G kem).SerializeRoundTrip)
    (hX : (P.G kem).ExchangeIsDh) (hO : (P.G kem).PublicOctetsSerialize)
    (generate : KemId → Except Err (PrivateKey P)) (coins : (k : KemId) → (P.M k).Coins)
    (draw : KemId → Nat → Bytes)
    (hgen : ∀ e, generate kem = .ok e → ∃ eb skE, e = dhPrivateKey P kem eb skE)
    (rb sb : Bytes) (skR skS : (P.G kem).SK) {ss enc : Bytes}
    (h : encap P generate coins draw (some (dhPrivateKey P kem sb skS))
      (dhPrivateKey P kem rb skR).publicKey = .ok (ss, enc)) :
    decap P (dhPrivateKey P kem rb skR) (some (dhPrivateKey P kem sb skS).publicKey) enc
      = .ok ss := by
  have hrecip : (dhPrivateKey P kem rb skR).publicKey = dhPublicKey P kem ((P.G kem).publicOctets skR) := rfl
  rw [hrecip] at h
  simp only [encap, dhPublicKey] at h
  cases hg : generate kem with
  | error e => simp [hg, bind, Except.bind] at h
  | ok e =>
    obtain ⟨eb, skE, rfl⟩ := hgen e hg
    simp only [hg, bind, Except.bind] at h
    exact decap_encapWith_auth P kem hdh hC hR hX hO eb rb sb skE skR skS h

/-! ## 3. ML-KEM -/

/-- The `Mlkem_kem` wrapper round-trips under FIPS 203 correctness. -/
theorem MlkemKem.decap_encap (M : MlKem) (hC : M.Correct) (hCt : M.CiphertextRoundTrip)
    (dk : M.DK) (coins : M.Coins) :
    MlkemKem.decap M dk (MlkemKem.encap M coins (M.ekOfDk dk)).2
      = .ok (MlkemKem.encap M coins (M.ekOfDk dk)).1 := by
  simp [MlkemKem.decap, MlkemKem.encap, hCt _, hC dk coins]

/-- `Private_key.of_bytes` on an ML-KEM seed builds `mlkemPrivateKey`. -/
theorem mlkemPrivateKeyOfBytes_ok (kem : KemId) (seed : Bytes) (dk : (P.M kem).DK)
    (h : (P.M kem).dkOfSeed seed = .ok dk) :
    mlkemPrivateKeyOfBytes P kem seed = .ok (mlkemPrivateKey P kem seed dk) := by
  simp [mlkemPrivateKeyOfBytes, MlkemKem.privateKey, h, mlkemPrivateKey]

/-- The ML-KEM round trip through the dispatching `encap` and `decap`. -/
theorem decap_encap_mlkem (kem : KemId)
    (hC : (P.M kem).Correct) (hCt : (P.M kem).CiphertextRoundTrip)
    (generate : KemId → Except Err (PrivateKey P)) (coins : (k : KemId) → (P.M k).Coins)
    (draw : KemId → Nat → Bytes)
    (seed : Bytes) (dk : (P.M kem).DK) {ss enc : Bytes}
    (h : encap P generate coins draw none (mlkemPrivateKey P kem seed dk).publicKey = .ok (ss, enc)) :
    decap P (mlkemPrivateKey P kem seed dk) none enc = .ok ss := by
  simp [encap, mlkemPrivateKey, mlkemWithoutSender, bind, Except.bind, pure, Except.pure] at h
  obtain ⟨rfl, rfl⟩ := h
  have := MlkemKem.decap_encap (P.M kem) hC hCt dk (coins kem)
  simp [MlkemKem.encap] at this
  simp [decap, mlkemPrivateKey, mlkemWithoutSender, bind, Except.bind, this]

/-- ML-KEM `encap` never draws an ephemeral key pair: it does not call the
generator (Mlkem material). -/
theorem encap_mlkem_ignores_generate (generate₁ generate₂ : KemId → Except Err (PrivateKey P))
    (coins : (k : KemId) → (P.M k).Coins) (draw : KemId → Nat → Bytes)
    (sender : Option (PrivateKey P))
    (kem : KemId) (bytes : Bytes) (ek : (P.M kem).EK) :
    encap P generate₁ coins draw sender { kem, bytes, material := .mlkem ek }
      = encap P generate₂ coins draw sender { kem, bytes, material := .mlkem ek } := rfl

/-- A sender key is never silently dropped: `encap` with a sender on ML-KEM
material is `Unsupported_mode`. -/
theorem encap_mlkem_sender (generate : KemId → Except Err (PrivateKey P))
    (coins : (k : KemId) → (P.M k).Coins) (draw : KemId → Nat → Bytes) (s : PrivateKey P)
    (kem : KemId) (bytes : Bytes) (ek : (P.M kem).EK) :
    encap P generate coins draw (some s) { kem, bytes, material := .mlkem ek }
      = .error .unsupportedMode := rfl

/-- ... nor by `decap`. -/
theorem decap_mlkem_sender (s : PublicKey P) (kem : KemId) (bytes : Bytes)
    (dk : (P.M kem).DK) (pub : PublicKey P) (enc : Bytes) :
    decap P { kem, bytes, secret := .mlkem dk, publicKey := pub } (some s) enc
      = .error .unsupportedMode := rfl

/-- The same two facts for any key value, whatever its record fields. -/
theorem encap_sender_mlkem_material (generate : KemId → Except Err (PrivateKey P))
    (coins : (k : KemId) → (P.M k).Coins) (draw : KemId → Nat → Bytes) (s : PrivateKey P) (recipient : PublicKey P)
    (ek : (P.M recipient.kem).EK) (h : recipient.material = .mlkem ek) :
    encap P generate coins draw (some s) recipient = .error .unsupportedMode := by
  unfold encap; rw [h]; rfl

theorem decap_sender_mlkem_secret (s : PublicKey P) (recipient : PrivateKey P)
    (dk : (P.M recipient.kem).DK) (h : recipient.secret = .mlkem dk) (enc : Bytes) :
    decap P recipient (some s) enc = .error .unsupportedMode := by
  unfold decap; rw [h]; rfl

/-- Parsing a recipient key and running `encap` on it is the draft's `Encap`. -/
theorem encap_mlkem_eq_Draft (kem : KemId) (hml : kem.isDh = false)
    (hhy : kem.isHybrid = false)
    (generate : KemId → Except Err (PrivateKey P)) (coins : (k : KemId) → (P.M k).Coins)
    (draw : KemId → Nat → Bytes)
    (pkR : Bytes) :
    ((publicKeyOfBytes P kem pkR).bind (encap P generate coins draw none)).toOption
      = Draft.Encap (P.M kem) pkR (coins kem) := by
  unfold publicKeyOfBytes Draft.Encap
  simp only [hml, hhy]
  cases h : (P.M kem).ekOfOctets pkR with
  | error r => simp [Except.bind, Except.toOption]
  | ok ek =>
    simp [Except.bind, Except.toOption, encap, mlkemWithoutSender, MlkemKem.encap,
      bind, pure, Except.pure]

/-- Parsing a recipient seed and running `decap` is the draft's `Decap`. -/
theorem decap_mlkem_eq_Draft (kem : KemId) (seed enc : Bytes) :
    ((mlkemPrivateKeyOfBytes P kem seed).bind (fun R => decap P R none enc)).toOption
      = Draft.Decap (P.M kem) enc seed := by
  unfold mlkemPrivateKeyOfBytes MlkemKem.privateKey Draft.Decap
  cases h : (P.M kem).dkOfSeed seed with
  | error r => simp [Except.bind, Except.toOption]
  | ok dk =>
    cases hc : (P.M kem).ctOfOctets enc with
    | error r =>
      simp [Except.bind, Except.toOption, decap, mlkemWithoutSender, MlkemKem.decap, hc,
        bind]
    | ok c =>
      simp [Except.bind, Except.toOption, decap, mlkemWithoutSender, MlkemKem.decap, hc,
        bind]

/-! ## 4. Error mapping in `dh_decap` -/

/-- A parse failure of the encapsulation is `Invalid_encapsulation`, carrying
the parser's reason. -/
theorem dhDecap_parse_error (kem : KemId) (hdh : kem.isDh = true) (rb : Bytes)
    (skR : (P.G kem).SK) (sender : Option (PublicKey P)) (enc : Bytes) (r : String)
    (h : (P.G kem).deserialize enc = .error r) :
    dhDecap P (dhPrivateKey P kem rb skR) sender enc = .error (.invalidEncapsulation r) := by
  simp [dhDecap, publicKeyOfBytes, dhPrivateKey, hdh, h, bind, Except.bind]

/-- A failure of the exchange of the recipient key with the encapsulation (for
example a low-order X25519 point) is `Invalid_encapsulation`. -/
theorem dhDecap_ephemeral_error (kem : KemId) (hdh : kem.isDh = true) (rb : Bytes)
    (skR : (P.G kem).SK) (sender : Option (PublicKey P)) (enc : Bytes) (pE : (P.G kem).PK)
    (r : String) (hp : (P.G kem).deserialize enc = .ok pE)
    (h : (P.G kem).exchange skR enc = .error r) :
    dhDecap P (dhPrivateKey P kem rb skR) sender enc = .error (.invalidEncapsulation r) := by
  simp [dhDecap, publicKeyOfBytes, dhPrivateKey, dhPublicKey, dh, hdh, hp, h, bind,
    Except.bind]

/-- A failure of the static exchange with the sender's key stays
`Invalid_public_key` (the `setup_auth_receiver` contract). -/
theorem dhDecap_static_error (kem : KemId) (hdh : kem.isDh = true) (rb : Bytes)
    (skR : (P.G kem).SK) (enc : Bytes) (pE : (P.G kem).PK) (v : Bytes)
    (hp : (P.G kem).deserialize enc = .ok pE) (he : (P.G kem).exchange skR enc = .ok v)
    (S : PublicKey P) (hS : S.kem = kem) (r : String)
    (h : (P.G kem).exchange skR S.bytes = .error r) :
    dhDecap P (dhPrivateKey P kem rb skR) (some S) enc = .error (.invalidPublicKey r) := by
  simp [dhDecap, publicKeyOfBytes, dhPrivateKey, dhPublicKey, dh, hdh, hp, he, h, hS, bind,
    Except.bind]

/-- Every error of `dh_decap` (sender key of the recipient's KEM, as
`setup_receiver` ensures) is `Invalid_encapsulation`, from the parse or the
ephemeral exchange, or `Invalid_public_key` from the static exchange with a
sender key. In particular it is never `Key_mismatch` or `Unsupported_mode`,
the two errors `normalized_open` passes through. -/
theorem dhDecap_error_cases (kem : KemId) (hdh : kem.isDh = true) (rb : Bytes)
    (skR : (P.G kem).SK) (sender : Option (PublicKey P)) (enc : Bytes)
    (hS : ∀ S ∈ sender, S.kem = kem) (e : Err)
    (h : dhDecap P (dhPrivateKey P kem rb skR) sender enc = .error e) :
    (∃ r, e = .invalidEncapsulation r ∧
      ((P.G kem).deserialize enc = .error r ∨ (P.G kem).exchange skR enc = .error r)) ∨
    (∃ S r, sender = some S ∧ e = .invalidPublicKey r ∧ (P.G kem).exchange skR S.bytes = .error r) := by
  cases hp : (P.G kem).deserialize enc with
  | error r =>
    rw [dhDecap_parse_error P kem hdh rb skR sender enc r hp] at h
    cases h
    exact .inl ⟨r, rfl, .inl rfl⟩
  | ok pE =>
    cases he : (P.G kem).exchange skR enc with
    | error r =>
      rw [dhDecap_ephemeral_error P kem hdh rb skR sender enc pE r hp he] at h
      cases h
      exact .inl ⟨r, rfl, .inr rfl⟩
    | ok v =>
      cases sender with
      | none =>
        simp [dhDecap, publicKeyOfBytes, dhPrivateKey, dhPublicKey, dh, hdh, hp, he, bind,
          Except.bind, pure, Except.pure] at h
      | some S =>
        have hSk : S.kem = kem := hS S rfl
        cases hs : (P.G kem).exchange skR S.bytes with
        | error r =>
          rw [dhDecap_static_error P kem hdh rb skR enc pE v hp he S hSk r hs] at h
          cases h
          exact .inr ⟨S, r, rfl, rfl, hs⟩
        | ok w =>
          simp [dhDecap, publicKeyOfBytes, dhPrivateKey, dhPublicKey, dh, hdh, hp, he, hs, hSk,
            bind, Except.bind, pure, Except.pure] at h

/-- The ML-KEM branch of `decap` fails only with `Unsupported_mode` (a sender
key) or `Invalid_encapsulation` (a ciphertext of the wrong length). -/
theorem decap_mlkem_error_cases (kem : KemId) (seed : Bytes) (dk : (P.M kem).DK)
    (sender : Option (PublicKey P)) (enc : Bytes) (e : Err)
    (h : decap P (mlkemPrivateKey P kem seed dk) sender enc = .error e) :
    (sender.isSome ∧ e = .unsupportedMode) ∨
    (sender = none ∧ ∃ r, e = .invalidEncapsulation r ∧ (P.M kem).ctOfOctets enc = .error r) := by
  cases sender with
  | some S =>
    rw [decap_sender_mlkem_secret P S _ dk rfl] at h
    cases h; exact .inl ⟨rfl, rfl⟩
  | none =>
    cases hc : (P.M kem).ctOfOctets enc with
    | error r =>
      simp [decap, mlkemPrivateKey, mlkemWithoutSender, MlkemKem.decap, hc, bind,
        Except.bind] at h
      exact .inr ⟨rfl, r, h.symm, rfl⟩
    | ok c =>
      simp [decap, mlkemPrivateKey, mlkemWithoutSender, MlkemKem.decap, hc, bind,
        Except.bind] at h

/-- `dh` with an ML-KEM secret is `Invalid_private_key` (when the KEMs agree),
and `Key_mismatch` whenever they differ. -/
theorem dh_keyMismatch (sk : PrivateKey P) (pk : PublicKey P) (h : sk.kem ≠ pk.kem) :
    dh P sk pk = .error .keyMismatch := by
  simp [dh, h]

theorem dh_mlkem (sk : PrivateKey P) (pk : PublicKey P) (h : sk.kem = pk.kem)
    (dk : (P.M sk.kem).DK) (hs : sk.secret = .mlkem dk) :
    dh P sk pk = .error (.invalidPrivateKey "ML-KEM keys cannot perform a Diffie-Hellman exchange") := by
  simp [dh, h, hs]

/-- With the sender key of the recipient's KEM (what `setup_receiver`'s checks
guarantee), a Diffie-Hellman `decap` never fails with one of the two errors
that `normalized_open` passes through unchanged. -/
theorem decap_dh_not_caller_error (kem : KemId) (hdh : kem.isDh = true) (rb : Bytes)
    (skR : (P.G kem).SK) (sender : Option (PublicKey P)) (enc : Bytes)
    (hS : ∀ S ∈ sender, S.kem = kem) (e : Err)
    (h : decap P (dhPrivateKey P kem rb skR) sender enc = .error e) :
    e ≠ .keyMismatch ∧ e ≠ .unsupportedMode := by
  rcases dhDecap_error_cases P kem hdh rb skR sender enc hS e h with
    ⟨r, rfl, _⟩ | ⟨S, r, _, rfl, _⟩ <;> exact ⟨nofun, nofun⟩

/-- Without a sender key (what `setup_receiver`'s mode check guarantees for
ML-KEM), neither does an ML-KEM `decap`. -/
theorem decap_mlkem_not_caller_error (kem : KemId) (seed : Bytes) (dk : (P.M kem).DK)
    (enc : Bytes) (e : Err) (h : decap P (mlkemPrivateKey P kem seed dk) none enc = .error e) :
    e ≠ .keyMismatch ∧ e ≠ .unsupportedMode := by
  rcases decap_mlkem_error_cases P kem seed dk none enc e h with
    ⟨h, _⟩ | ⟨_, r, rfl, _⟩
  · cases h
  · exact ⟨nofun, nofun⟩

/-! ## 5. PQ/T hybrid KEMs

`Hybrid_kem` against the CG framework of draft-irtf-cfrg-hybrid-kems
(Section 5.4, with the subroutines of Section 5.1), as
draft-irtf-cfrg-concrete-hybrid-kems instantiates it and draft-ietf-hpke-pq-05
Section 4 adopts it for HPKE. -/

namespace HybridKem

variable (H : HybridPrims)

/-- **Assumption** on SHAKE256: `prg seed n` is `n` bytes long. -/
def PrgLength : Prop := ∀ (seed : Bytes) (n : Nat), (H.prg seed n).length = n

/-- **Assumption** on the ML-KEM library: a ciphertext is `Nct` bytes long. -/
def CiphertextLength : Prop := ∀ c : H.M.CT, (H.M.ctToOctets c).length = H.pq.encapsulatedKeySize

/-- The hybrid's `Nct` is the ML-KEM `Nct` plus `Nelem`, which the registry
proves for the three instances (`hybrid_sizes`). -/
def SizesAgree : Prop := H.kem.encapsulatedKeySize = H.pq.encapsulatedKeySize + H.elementSize

/-! ### The specification -/

namespace CG

/-- `split(N1, N2, x)`; calling it on a string of another length "is an error",
here `none`. -/
def split (n1 n2 : Nat) (x : Bytes) : Option (Bytes × Bytes) :=
  if x.length = n1 + n2 then some (x.take n1, x.drop n1) else none

/-- ```
def expandDecapsKeyG(seed):
    seed_full = PRG(seed)
    (seed_PQ, seed_T) = split(KEM_PQ.Nseed, Group_T.Nseed, seed_full)

    (dk_PQ, ek_PQ) = KEM_PQ.DeriveKeyPair(seed_PQ)
    dk_T = Group_T.RandomScalar(seed_T)
    ek_T = Group_T.Exp(Group_T.g, dk_T)

    return (ek_PQ, ek_T, dk_PQ, dk_T)
``` -/
def expandDecapsKeyG (seed : Bytes) : Option (H.M.EK × Bytes × H.M.DK × H.G.Scalar) := do
  let seed_full := H.prg seed (H.pq.privateKeySize + H.seedSize)
  let (seed_PQ, seed_T) ← split H.pq.privateKeySize H.seedSize seed_full
  let dk_PQ ← (H.M.dkOfSeed seed_PQ).toOption
  let ek_PQ := H.M.ekOfDk dk_PQ
  let (dk_T, ek_T) ← H.G.randomScalar seed_T
  return (ek_PQ, ek_T, dk_PQ, dk_T)

/-- ```
def DeriveKeyPair(seed):
    (ek_PQ, ek_T, dk_PQ, dk_T) = expandDecapsKeyG(seed)
    return (seed, concat(ek_PQ, ek_T))
``` -/
def DeriveKeyPair (seed : Bytes) : Option (Bytes × Bytes) := do
  let (ek_PQ, ek_T, _, _) ← expandDecapsKeyG H seed
  return (seed, H.M.ekToOctets ek_PQ ++ ek_T)

/-- `C2PRICombiner(ss_PQ, ss_T, ct_T, ek_T, label)`. -/
def C2PRICombiner (ss_PQ ss_T ct_T ek_T label : Bytes) : Bytes :=
  H.kdf (ss_PQ ++ ss_T ++ ct_T ++ ek_T ++ label)

/-- ```
def Encaps(ek):
    (ek_PQ, ek_T) = split(KEM_PQ.Nek, Group_T.Nelem, ek)
    (ss_PQ, ss_T, ct_PQ, ct_T) = prepareEncapsG(ek_PQ, ek_T)
    ss_H = C2PRICombiner(ss_PQ, ss_T, ct_T, ek_T, Label)
    ct_H = concat(ct_PQ, ct_T)
    return (ss_H, ct_H)

def prepareEncapsG(ek_PQ, ek_T):
    (ss_PQ, ct_PQ) = KEM_PQ.Encaps(ek_PQ)
    sk_E = Group_T.RandomScalar(random(Group_T.Nseed))
    ct_T = Group_T.Exp(Group_T.g, sk_E)
    ss_T = Group_T.ElementToSharedSecret(Group_T.Exp(ek_T, sk_E))
    return (ss_PQ, ss_T, ct_PQ, ct_T)
```
with its randomness as arguments: `KEM_PQ.Encaps`'s, and `random(Nseed)`.
`KEM_PQ.Encaps` includes the FIPS 203 input check, and `Exp` fails on an
invalid element. -/
def Encaps (ek : Bytes) (coins : H.M.Coins) (seedE : Bytes) : Option (Bytes × Bytes) := do
  let (ek_PQ, ek_T) ← split H.pq.publicKeySize H.elementSize ek
  let ekPQ ← (H.M.ekOfOctets ek_PQ).toOption
  let (c, K) := H.M.encaps ekPQ coins
  let (sk_E, ct_T) ← H.G.randomScalar seedE
  let ss_T ← (H.G.sharedSecret sk_E ek_T).toOption
  return (C2PRICombiner H (H.M.ssToOctets K) ss_T ct_T ek_T H.label, H.M.ctToOctets c ++ ct_T)

/-- ```
def Decaps(dk, ct):
    (ct_PQ, ct_T) = split(KEM_PQ.Nct, Group_T.Nelem, ct)
    (ek_PQ, ek_T, dk_PQ, dk_T) = expandDecapsKeyG(dk)
    (ss_PQ, ss_T) = prepareDecapsG(ct_PQ, ct_T, dk_PQ, dk_T)
    ss_H = C2PRICombiner(ss_PQ, ss_T, ct_T, ek_T, Label)
    return ss_H

def prepareDecapsG(ct_PQ, ct_T, dk_PQ, dk_T):
    ss_PQ = KEM_PQ.Decaps(dk_PQ, ct_PQ)
    ss_T = Group_T.ElementToSharedSecret(Group_T.Exp(ct_T, dk_T))
    return (ss_PQ, ss_T)
``` -/
def Decaps (dk ct : Bytes) : Option Bytes := do
  let (ct_PQ, ct_T) ← split H.pq.encapsulatedKeySize H.elementSize ct
  let (_, ek_T, dk_PQ, dk_T) ← expandDecapsKeyG H dk
  let c ← (H.M.ctOfOctets ct_PQ).toOption
  let ss_T ← (H.G.sharedSecret dk_T ct_T).toOption
  return C2PRICombiner H (H.M.ssToOctets (H.M.decaps dk_PQ c)) ss_T ct_T ek_T H.label

end CG

/-! ### The mirror is the specification -/

private theorem split_prg (n s : Nat) (x : Bytes) (hl : x.length = n + s) :
    CG.split n s x = some (x.take n, (x.drop n).take s) := by
  unfold CG.split
  rw [ite_eq_left hl]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  rw [List.take_of_length_le (by rw [List.length_drop]; omega)]

set_option linter.unusedSimpArgs false in
/-- `private_key` is `DeriveKeyPair`: it succeeds exactly when the draft's
derivation does, with the same encapsulation key. -/
theorem privateKey_eq_DeriveKeyPair (hP : PrgLength H) (seed : Bytes) :
    (privateKey H seed).toOption.map (fun x => x.2.2) = (CG.DeriveKeyPair H seed).map Prod.snd := by
  dsimp only [privateKey, CG.DeriveKeyPair, CG.expandDecapsKeyG]
  have hlen := hP seed (H.pq.privateKeySize + H.seedSize)
  generalize H.prg seed (H.pq.privateKeySize + H.seedSize) = x at hlen ⊢
  rw [split_prg _ _ x hlen]
  cases hs : H.G.randomScalar ((x.drop H.pq.privateKeySize).take H.seedSize) <;>
  cases hd : H.M.dkOfSeed (x.take H.pq.privateKeySize) <;>
  simp [hs, hd, MlkemKem.privateKey, Except.toOption, bind, Option.bind, pure]

set_option linter.unusedSimpArgs false in
/-- `decap` on the key `private_key` makes of a seed is `Decaps`. -/
theorem decap_eq_Decaps (hP : PrgLength H) (hS : SizesAgree H) (dk ct : Bytes) :
    ((privateKey H dk).bind fun x => decap H x.1 ct).toOption = CG.Decaps H dk ct := by
  dsimp only [privateKey, CG.Decaps, CG.expandDecapsKeyG]
  have hlen := hP dk (H.pq.privateKeySize + H.seedSize)
  generalize H.prg dk (H.pq.privateKeySize + H.seedSize) = x at hlen ⊢
  rw [split_prg _ _ x hlen]
  by_cases hl : ct.length = H.pq.encapsulatedKeySize + H.elementSize
  · rw [split_prg _ _ ct hl]
    cases hs : H.G.randomScalar ((x.drop H.pq.privateKeySize).take H.seedSize) with
    | none =>
      cases hd : H.M.dkOfSeed (x.take H.pq.privateKeySize) <;>
      simp [hs, hd, Except.bind, Except.toOption, bind, Option.bind]
    | some p =>
      obtain ⟨scalar, e⟩ := p
      cases hd : H.M.dkOfSeed (x.take H.pq.privateKeySize) with
      | error r => simp [hs, hd, MlkemKem.privateKey, Except.bind, Except.toOption, bind, Option.bind]
      | ok dkPQ =>
        simp only [hs, hd, MlkemKem.privateKey, Except.bind, Except.toOption, bind, Option.bind]
        unfold decap
        rw [hS, ite_eq_right (by omega)]
        dsimp only
        cases hg : H.G.sharedSecret scalar
            ((ct.drop H.pq.encapsulatedKeySize).take H.elementSize) <;>
        cases hc : H.M.ctOfOctets (ct.take H.pq.encapsulatedKeySize) <;>
        simp [hs, hc, hg, MlkemKem.decap, combine, CG.C2PRICombiner, pure]
  · have hsplit : CG.split H.pq.encapsulatedKeySize H.elementSize ct = none := by
      simp [CG.split, hl]
    rw [hsplit]
    cases hs : H.G.randomScalar ((x.drop H.pq.privateKeySize).take H.seedSize) with
    | none =>
      cases hd : H.M.dkOfSeed (x.take H.pq.privateKeySize) <;>
      simp [hs, hd, Except.bind, Except.toOption, bind, Option.bind]
    | some p =>
      obtain ⟨scalar, e⟩ := p
      cases hd : H.M.dkOfSeed (x.take H.pq.privateKeySize) with
      | error r => simp [hs, hd, MlkemKem.privateKey, Except.bind, Except.toOption, bind, Option.bind]
      | ok dkPQ =>
        simp only [hs, hd, MlkemKem.privateKey, Except.bind, Except.toOption, bind, Option.bind]
        unfold decap
        rw [hS, ite_eq_left (by omega)]

/-! ### The retry loop of `encap` -/

/-- One attempt of `encap` on the randomness of one draw: `none` if its group
seed holds no scalar (the loop then draws again), else the attempt's result. -/
def step (randomness : Bytes) (pub : Public H) : Option (Except Err (Bytes × Bytes)) :=
  match H.G.randomScalar ((randomness.drop 32).take H.seedSize) with
  | none => none
  | some (ephemeral, groupCiphertext) =>
    some (match H.G.sharedSecret ephemeral pub.element with
      | .error reason => .error (.invalidPublicKey reason)
      | .ok groupSecret =>
        let (pqSecret, pqCiphertext) :=
          MlkemKem.encap H.M (H.coins (randomness.take 32)) pub.pq
        .ok (combine H pqSecret groupSecret groupCiphertext pub.element,
          pqCiphertext ++ groupCiphertext))

/-- The error of an encapsulation whose every draw failed. -/
def exhausted : Except Err (Bytes × Bytes) :=
  .error (.internalError "no ephemeral scalar could be sampled")

private theorem attempt_eq (draw : Nat → Bytes) (pub : Public H) :
    ∀ remaining made, attempt H draw pub made (remaining + 1)
      = ((List.range (remaining + 1)).findSome? fun i => step H (draw (made + i)) pub).getD
          (exhausted) := by
  intro remaining
  induction remaining with
  | zero =>
    intro made
    rw [attempt]
    simp only [Nat.zero_add, List.range_one, List.findSome?_cons, List.findSome?_nil,
      Nat.add_zero]
    unfold step
    cases H.G.randomScalar (((draw made).drop 32).take H.seedSize) <;> rfl
  | succ r ih =>
    intro made
    rw [attempt, List.range_succ_eq_map, List.findSome?_cons]
    simp only [Nat.add_zero]
    unfold step
    cases hs : H.G.randomScalar (((draw made).drop 32).take H.seedSize) with
    | some p => rfl
    | none =>
      simp only [ite_eq_left (show r + 1 + 1 > 1 by omega), Nat.add_sub_cancel]
      rw [ih (made + 1), List.findSome?_map]
      congr 2
      funext i
      rw [Function.comp_apply, show made + (i + 1) = made + 1 + i by omega]
      rfl

/-- `encap` returns the result of the first of its eight draws whose group seed
holds a scalar, or `Internal_error` if none of them does. -/
theorem encap_eq_first (draw : Nat → Bytes) (pub : Public H) :
    encap H draw pub
      = ((List.range 8).findSome? fun i => step H (draw i) pub).getD (exhausted) := by
  unfold encap
  rw [attempt_eq H draw pub 7 0]
  simp

/-- When all eight draws hold no scalar (for P-256 a chance below `2^-512`),
`encap` fails with `Internal_error`. -/
theorem encap_exhausted (draw : Nat → Bytes) (pub : Public H)
    (h : ∀ i < 8, H.G.randomScalar (((draw i).drop 32).take H.seedSize) = none) :
    encap H draw pub = exhausted := by
  rw [encap_eq_first]
  have : (List.range 8).findSome? (fun i => step H (draw i) pub) = none := by
    rw [List.findSome?_eq_none_iff]
    intro i hi
    have := h i (List.mem_range.mp hi)
    simp [step, this]
  rw [this]; rfl

/-- `encap` succeeds only as some draw's attempt does. -/
theorem encap_ok_step {draw : Nat → Bytes} {pub : Public H} {r : Bytes × Bytes}
    (h : encap H draw pub = .ok r) : ∃ i < 8, step H (draw i) pub = some (.ok r) := by
  rw [encap_eq_first] at h
  cases hf : (List.range 8).findSome? (fun i => step H (draw i) pub) with
  | none => rw [hf] at h; cases h
  | some x =>
    rw [hf] at h
    simp only [Option.getD_some] at h
    subst h
    obtain ⟨i, hi, hx⟩ := List.exists_of_findSome?_eq_some hf
    exact ⟨i, List.mem_range.mp hi, hx⟩

/-- `encap` fails only with `Invalid_public_key` (an element the exchange
refuses, such as a low-order X25519 value) or `Internal_error`. -/
theorem encap_error (draw : Nat → Bytes) (pub : Public H) (e : Err)
    (h : encap H draw pub = .error e) :
    (∃ r, e = .invalidPublicKey r) ∨ (∃ r, e = .internalError r) := by
  rw [encap_eq_first] at h
  cases hf : (List.range 8).findSome? (fun i => step H (draw i) pub) with
  | none => rw [hf] at h; cases h; exact .inr ⟨_, rfl⟩
  | some x =>
    rw [hf] at h
    simp only [Option.getD_some] at h
    subst h
    obtain ⟨i, _, hx⟩ := List.exists_of_findSome?_eq_some hf
    unfold step at hx
    split at hx
    · cases hx
    · split at hx <;> simp at hx
      exact .inl ⟨_, hx.symm⟩

/-- On a draw whose seed holds a scalar, parsing a public key and running
`encap` is `Encaps` of the CG framework, with that draw's randomness laid out
as `EncapsDerand` takes it: 32 bytes for ML-KEM, then the group seed. The
public-key check adds nothing the exchange would accept. -/
theorem encap_eq_Encaps (hC : H.G.CheckElementSound) (ek : Bytes)
    (hl : ek.length = H.pq.publicKeySize + H.elementSize) (draw : Nat → Bytes)
    (hfirst : (H.G.randomScalar (((draw 0).drop 32).take H.seedSize)).isSome) :
    ((publicKey H ek).bind (encap H draw)).toOption
      = CG.Encaps H ek (H.coins ((draw 0).take 32)) (((draw 0).drop 32).take H.seedSize) := by
  unfold CG.Encaps
  rw [split_prg _ _ ek hl]
  obtain ⟨⟨eph, ct⟩, hs⟩ := Option.isSome_iff_exists.mp hfirst
  have hstep : encap H draw = fun pub => (step H (draw 0) pub).getD exhausted := by
    funext pub
    rw [encap_eq_first, List.range_succ_eq_map, List.findSome?_cons]
    simp [step, hs]
  rw [hstep]
  unfold publicKey MlkemKem.publicKey
  cases hk : H.M.ekOfOctets (ek.take H.pq.publicKeySize) with
  | error r => simp [hk, bind, Except.bind, Option.bind, Except.toOption]
  | ok ekPQ =>
    cases hg : H.G.sharedSecret eph ((ek.drop H.pq.publicKeySize).take H.elementSize) with
    | error r =>
      cases hc : H.G.checkElement ((ek.drop H.pq.publicKeySize).take H.elementSize) <;>
      simp [hk, hs, hg, hc, step, bind, Except.bind, Option.bind, Except.toOption, pure,
        Except.pure]
    | ok gs =>
      have hc := hC eph _ gs hg
      simp [hk, hs, hg, hc, step, bind, Except.bind, Option.bind, Except.toOption, pure,
        Except.pure, MlkemKem.encap, combine, CG.C2PRICombiner]

/-! ### Correctness and error contracts -/

/-- **Correctness.** What `encap` produces for the public half of a key that
`private_key` derived from a seed, `decap` with its secret half turns back into
the same shared secret. -/
theorem decap_encap (hS : SizesAgree H) (hMC : H.M.Correct) (hCt : H.M.CiphertextRoundTrip)
    (hCL : CiphertextLength H) (hG : H.G.Commutes) (hE : H.G.ElementLength H.elementSize)
    {seed bytes : Bytes} {sec : Secret H} {pub : Public H}
    (hk : privateKey H seed = .ok (sec, pub, bytes)) (draw : Nat → Bytes) {ss enc : Bytes}
    (h : encap H draw pub = .ok (ss, enc)) :
    decap H sec enc = .ok ss := by
  obtain ⟨i, _, hi⟩ := encap_ok_step H h
  unfold privateKey at hk
  dsimp only at hk
  split at hk
  · cases hk
  · rename_i scalar own hs
    split at hk
    · cases hk
    · rename_i dk ekPQ pqBytes hpk
      simp only [Except.ok.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      simp only [MlkemKem.privateKey] at hpk
      split at hpk
      · cases hpk
      · rename_i dk' hdk
        simp only [Except.ok.injEq, Prod.mk.injEq] at hpk
        obtain ⟨rfl, rfl, rfl⟩ := hpk
        unfold step at hi
        split at hi
        · cases hi
        · rename_i eph ct hse
          dsimp only at hi
          split at hi
          · simp at hi
          · rename_i gs hgs
            simp only [MlkemKem.encap, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hi
            obtain ⟨rfl, rfl⟩ := hi
            have hct : ct.length = H.elementSize := hE _ _ _ hse
            have hpqc := hCL (H.M.encaps (H.M.ekOfDk dk') (H.coins ((draw i).take 32))).1
            unfold decap
            rw [ite_eq_right (by rw [hS, List.length_append, hct, hpqc]; exact fun h => h rfl)]
            dsimp only
            rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
              List.nil_append, List.take_of_length_le (by omega)]
            rw [hG _ _ scalar eph own ct hs hse, hgs]
            simp only
            rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
            simp only [MlkemKem.decap, hCt _, hMC dk', combine]

/-- `decap` fails only with `Invalid_encapsulation`: a wrong length, an element
the exchange refuses, or an ML-KEM ciphertext the library refuses. -/
theorem decap_error (sec : Secret H) (enc : Bytes) (e : Err) (h : decap H sec enc = .error e) :
    ∃ r, e = .invalidEncapsulation r := by
  unfold decap at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · dsimp only at h
    split at h
    · cases h; exact ⟨_, rfl⟩
    · split at h
      · rename_i e' hd
        cases h
        unfold MlkemKem.decap at hd
        split at hd <;> cases hd
        exact ⟨_, rfl⟩
      · cases h

/-- Implicit rejection carries over: an encapsulation of the right length
whose element the exchange accepts and whose ML-KEM part the library parses
always decapsulates, whatever the ML-KEM part holds. -/
theorem decap_ok (sec : Secret H) (enc : Bytes) (hl : enc.length = H.kem.encapsulatedKeySize)
    (gs : Bytes)
    (hg : H.G.sharedSecret sec.scalar ((enc.drop H.pq.encapsulatedKeySize).take H.elementSize)
      = .ok gs)
    (c : H.M.CT) (hc : H.M.ctOfOctets (enc.take H.pq.encapsulatedKeySize) = .ok c) :
    ∃ ss, decap H sec enc = .ok ss := by
  unfold decap
  rw [ite_eq_right (fun h => h hl)]
  simp [hg, MlkemKem.decap, hc]

end HybridKem

/-! ## 6. The hybrids through the dispatching mirrors -/

/-- The private key `Private_key.of_bytes` returns for a hybrid seed, from what
`Hybrid_kem.private_key` returns for it (lines 516-521, 568-585). -/
def hybridPrivateKey (kem : KemId) (seed : Bytes) (sec : HybridKem.Secret (P.H kem))
    (pub : HybridKem.Public (P.H kem)) (bytes : Bytes) : PrivateKey P :=
  { kem, bytes := seed, secret := .hybrid sec,
    publicKey := { kem, bytes, material := .hybrid pub } }

/-- The hybrid round trip through the dispatching `encap` and `decap`. -/
theorem decap_encap_hybrid (kem : KemId)
    (hS : HybridKem.SizesAgree (P.H kem)) (hMC : (P.H kem).M.Correct)
    (hCt : (P.H kem).M.CiphertextRoundTrip) (hCL : HybridKem.CiphertextLength (P.H kem))
    (hG : (P.H kem).G.Commutes) (hE : (P.H kem).G.ElementLength (P.H kem).elementSize)
    (generate : KemId → Except Err (PrivateKey P)) (coins : (k : KemId) → (P.M k).Coins)
    (draw : KemId → Nat → Bytes) {seed bytes : Bytes} {sec : HybridKem.Secret (P.H kem)}
    {pub : HybridKem.Public (P.H kem)}
    (hk : HybridKem.privateKey (P.H kem) seed = .ok (sec, pub, bytes)) {ss enc : Bytes}
    (h : encap P generate coins draw none (hybridPrivateKey P kem seed sec pub bytes).publicKey
      = .ok (ss, enc)) :
    decap P (hybridPrivateKey P kem seed sec pub bytes) none enc = .ok ss := by
  simp only [encap, hybridPrivateKey, mlkemWithoutSender, bind, Except.bind] at h
  simp only [decap, hybridPrivateKey, mlkemWithoutSender, bind, Except.bind]
  exact HybridKem.decap_encap (P.H kem) hS hMC hCt hCL hG hE hk (draw kem) h

/-- A hybrid `encap` never draws an ephemeral key pair. -/
theorem encap_hybrid_ignores_generate (generate₁ generate₂ : KemId → Except Err (PrivateKey P))
    (coins : (k : KemId) → (P.M k).Coins) (draw : KemId → Nat → Bytes)
    (sender : Option (PrivateKey P)) (kem : KemId) (bytes : Bytes)
    (pub : HybridKem.Public (P.H kem)) :
    encap P generate₁ coins draw sender { kem, bytes, material := .hybrid pub }
      = encap P generate₂ coins draw sender { kem, bytes, material := .hybrid pub } := rfl

/-- A sender key is never silently dropped by a hybrid `encap` ... -/
theorem encap_hybrid_sender (generate : KemId → Except Err (PrivateKey P))
    (coins : (k : KemId) → (P.M k).Coins) (draw : KemId → Nat → Bytes) (s : PrivateKey P)
    (recipient : PublicKey P) (pub : HybridKem.Public (P.H recipient.kem))
    (h : recipient.material = .hybrid pub) :
    encap P generate coins draw (some s) recipient = .error .unsupportedMode := by
  unfold encap; rw [h]; rfl

/-- ... nor by a hybrid `decap`. -/
theorem decap_hybrid_sender (s : PublicKey P) (recipient : PrivateKey P)
    (sec : HybridKem.Secret (P.H recipient.kem)) (h : recipient.secret = .hybrid sec)
    (enc : Bytes) :
    decap P recipient (some s) enc = .error .unsupportedMode := by
  unfold decap; rw [h]; rfl

/-- Without a sender key, a hybrid `decap` fails only with
`Invalid_encapsulation`, never with one of the two errors `normalized_open`
passes through. -/
theorem decap_hybrid_not_caller_error (recipient : PrivateKey P)
    (sec : HybridKem.Secret (P.H recipient.kem)) (h : recipient.secret = .hybrid sec)
    (enc : Bytes) (e : Err) (he : decap P recipient none enc = .error e) :
    (∃ r, e = .invalidEncapsulation r) ∧ e ≠ .keyMismatch ∧ e ≠ .unsupportedMode := by
  unfold decap at he
  rw [h] at he
  simp only [mlkemWithoutSender, bind, Except.bind] at he
  obtain ⟨r, rfl⟩ := HybridKem.decap_error (P.H recipient.kem) sec enc e he
  exact ⟨⟨r, rfl⟩, nofun, nofun⟩

/-- `dh` with a hybrid secret is `Invalid_private_key`: `hpke.for_testing`
cannot choose an ephemeral key for a hybrid. -/
theorem dh_hybrid (sk : PrivateKey P) (pk : PublicKey P) (h : sk.kem = pk.kem)
    (sec : HybridKem.Secret (P.H sk.kem)) (hs : sk.secret = .hybrid sec) :
    dh P sk pk
      = .error (.invalidPrivateKey "hybrid KEM keys cannot perform a Diffie-Hellman exchange") := by
  simp [dh, h, hs]

end Kem
end Hpke
