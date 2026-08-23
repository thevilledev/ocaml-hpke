# Assurance and threat model

## Claim

This library aims to be a high-assurance **composition** of established OCaml
cryptographic primitives. The composition layer is tested against pinned RFC
vectors, adversarial cases, property tests, and fuzz targets. It is not
formally proved and has not yet received an independent cryptographic audit.

Side-channel properties of elliptic-curve, AES, ChaCha20-Poly1305, hash, and
HKDF operations come from their dependencies. This project does not strengthen
those implementations. Runtime behavior, the OCaml compiler, foreign code,
hardware, and the operating system remain within the trusted computing base.

OCaml's garbage collector copies and retains values unpredictably. The library
therefore cannot guarantee zeroization of private keys, PSKs, shared secrets,
AEAD keys, nonces, or exporter material. Secret types are abstract to reduce
accidental disclosure, not to promise erasure.

## Protected boundary

For a correctly selected suite, securely generated recipient key, secure
ephemeral randomness, and uncompromised dependencies, RFC 9180 provides message
confidentiality and integrity and an exporter known to the two HPKE roles. PSK
mode additionally depends on a high-entropy, independently provisioned PSK.

The implementation enforces the following local invariants:

- canonical uncompressed SEC1 NIST public keys and exact fixed lengths;
- curve/range validation delegated to Mirage Crypto after encoding checks;
- RFC rejection sampling for NIST deterministic key derivation;
- RFC 7748 clamping for serialized and deserialized X25519 private keys;
- rejection of X25519 low-order/all-zero exchanges by the primitive backend;
- exact RFC suite identifiers, labels, modes, and key schedules;
- role-separated, abstract stateful contexts;
- a full 96-bit big-endian sequence counter and failure before exhaustion;
- increment only after successful seal/open;
- an atomic busy guard that prevents concurrent nonce consumption;
- AEAD plaintext and RFC exporter-length bounds;
- normalized single-shot open failures for protocol boundaries.

## Out of scope

HPKE does **not** provide:

- message framing or an encoding for `(enc, ciphertext)`;
- replay prevention;
- tolerance or recovery for loss, duplication, or reordering;
- padding or plaintext-length hiding;
- ciphersuite negotiation or downgrade protection;
- identity, channel, transcript, or application-context binding unless the
  application supplies and verifies suitable `info`/AAD values;
- recipient-compromise forward secrecy;
- secure long-term key storage, RNG initialization, process isolation, or
  endpoint compromise protection.

Base mode does not authenticate the sender. PSK mode authentication is only as
strong as PSK generation, uniqueness, provisioning, and identity binding.

## Adversary model

Peer-controlled public keys, encapsulated keys, AAD, info, and ciphertexts are
expected and must yield typed results rather than unexpected exceptions.
Attackers may tamper with or truncate ciphertexts and submit invalid curve
points. Resource-exhaustion attacks through arbitrarily large allocations are
primarily the embedding protocol's responsibility; applications should enforce
their own much smaller framing limits before calling HPKE.

Local callers are trusted to select the intended versioned RFC module and
suite, protect private material, supply secure randomness, and impose message
ordering. A caller with direct process-memory access is outside the model.

## Standards evolution

`Hpke.Rfc9180` is permanently tied to RFC 9180 semantics. The implementation
does not speculate about one-stage KDF behavior in the successor draft. A
future standard receives a new module and can share internal primitives without
silently changing existing wire behavior.
