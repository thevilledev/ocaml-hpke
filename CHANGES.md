# Changelog

## Unreleased

Adds the post-quantum/traditional hybrid KEMs, and the successor draft of HPKE
with the SHAKE KDFs in a module of its own. `Kem.id` gains constructors, which
exhaustive matches must handle.

- Add `Kem.Mlkem768_p256` (MLKEM768-P256, `0x0050`), `Kem.Mlkem768_x25519`
  (MLKEM768-X25519, or X-Wing, `0x647a`), and `Kem.Mlkem1024_p384`
  (MLKEM1024-P384, `0x0051`), the hybrid KEMs of `draft-ietf-hpke-pq-05` as
  `draft-irtf-cfrg-concrete-hybrid-kems` defines them: ML-KEM and an
  elliptic-curve group, combined with SHA3-256 so that the shared secret holds
  as long as either half does. They work in the Base and PSK modes, where a
  suite with an HKDF runs the RFC 9180 key schedule unchanged, and like ML-KEM
  have no Auth or AuthPSK mode. A private key is a 32-byte seed, expanded with
  SHAKE256 into an ML-KEM seed and a scalar, and `derive_key_pair` derives it
  with SHAKE256 as for ML-KEM. A public key is the ML-KEM key followed by the
  group element, and both halves are validated when it is parsed, the X25519
  one when it is used. An encapsulated key is the ML-KEM ciphertext followed by
  an ephemeral element. A tampered ciphertext decapsulates to an unrelated
  secret, as for ML-KEM, but an element that is off the curve, or an X25519
  value of low order, is `Invalid_encapsulation`.
- The hybrid combiner is Digestif's SHA3-256 and the key expansion the
  SHAKE256 of `mlkem`, both existing dependencies, so the library still
  implements no primitive of its own and gains no dependency.
- Grow the pinned `draft-ietf-hpke-pq-05` corpus from three vectors to six:
  one for each hybrid, in full. The two hybrid vectors whose KDF this library
  lacks join the ML-KEM-1024 one as KEM-only vectors, for key derivation and
  encapsulation.
- `hpke.for_testing` refuses a hybrid suite as it does an ML-KEM one.
- Add `Hpke.Draft_hpke_04`, HPKE as `draft-ietf-hpke-hpke-04` specifies it,
  in a separate versioned module so that `Hpke.Rfc9180` keeps its wire
  behavior. It offers the Base and PSK modes over every KEM, with a KDF
  registry of its own: the RFC 9180 HKDFs, with which a suite is the RFC 9180
  suite of the same identifiers, and the one-stage SHAKE128 (`0x0010`) and
  SHAKE256 (`0x0011`) of `draft-ietf-hpke-pq-05`, with which the key schedule
  and exports run `LabeledDerive`. Keys, AEADs, PSKs and contexts are shared.
  `Draft_hpke_04.Kdf.derive` exposes the unlabeled `Derive` for layered
  protocols. TurboSHAKE128 and TurboSHAKE256 wait for `mlkem` to provide
  TurboSHAKE.
- The pinned `draft-ietf-hpke-pq-05` corpus gains the four SHAKE vectors in
  full, run through `Draft_hpke_04`, which also reproduces the six HKDF
  vectors and the 64 RFC 9180 Base and PSK vectors.
- Extend the Lean mirrors to the hybrids. `Hybrid_kem` is proved to be the CG
  framework's `DeriveKeyPair`, `Encaps` and `Decaps` of
  `draft-irtf-cfrg-hybrid-kems`, decapsulation to recover what was
  encapsulated, and the P-256 and P-384 scalar sampling to be the concrete
  draft's `RandomScalar`. The conformance vectors grow from 4442 checks to
  8843, all 2904 setup combinations of the eleven KEMs among them.

## 0.3.0 — 2026-09-25

Adds X448, the RFC 9180 Auth and AuthPSK modes, and the post-quantum ML-KEM
KEMs. Two changes can break an upgrade from 0.2.0: `Kem.id` and `Error.t` gain
constructors, which exhaustive matches must handle, and `hpke` is no longer
installable on 32-bit architectures.

- Add `Kem.X448`, DHKEM(X448, HKDF-SHA512), identifier `0x0021`, with 56-byte
  keys and a 64-byte shared secret. Key derivation and clamping follow the
  X25519 path with the X448 rules of RFC 7748, and a low-order public value is
  rejected when it is used. The new constructor breaks exhaustive matches on
  `Kem.id`, which is why this is not a patch release.
- Depend on [`curve448`](https://github.com/thevilledev/ocaml-curve448) for
  the X448 primitive. `hpke` depends on the plain `curve448` library, so the
  pure OCaml implementation links by default and an application selects the C
  one by adding `curve448.c` to its own libraries. `curve448` needs a 64-bit
  OCaml, so `hpke` is no longer installable on 32-bit architectures, whichever
  KEM an application uses.
- Add the RFC 9180 Auth and AuthPSK modes, which also authenticate the sender
  with a static KEM key pair: `Rfc9180.setup_auth_sender`,
  `setup_auth_receiver`, `setup_auth_psk_sender`, and
  `setup_auth_psk_receiver`, and the single-shot `seal_auth`, `open_auth`,
  `seal_auth_psk`, and `open_auth_psk`. The sender passes its `Private_key.t`
  and the recipient the sender's `Public_key.t`, both as `~sender`; a key of
  another KEM is a `Key_mismatch`. Sender authentication is not a signature:
  whoever holds the recipient's private key, and in AuthPSK mode the PSK as
  well, can seal as any sender. The additions are new functions only, so
  existing callers are unaffected.
- Add `setup_auth_sender` and `setup_auth_psk_sender` to `hpke.for_testing`.
- Grow the pinned RFC 9180 corpus from 48 to 128 cases, every vector of the
  same CFRG commit: the 16 X448 Base and PSK vectors, and the 64 Auth and
  AuthPSK vectors over P-256, P-521, X25519, and X448. The 48 existing cases
  are unchanged.
- Add `Kem.Mlkem512`, `Kem.Mlkem768`, and `Kem.Mlkem1024`, the post-quantum
  ML-KEM KEMs of FIPS 203 with identifiers `0x0040` to `0x0042`, as
  `draft-ietf-hpke-pq-05` specifies them. They work in the Base and PSK modes,
  where a suite with an HKDF runs the RFC 9180 key schedule unchanged. A
  private key is the 64-byte seed `d || z`, and `generate_key_pair` takes it
  from the generator as `ML-KEM.KeyGen` does. A public key must pass the
  modulus check of FIPS 203. Keys are parsed once and kept: parsing a private
  key runs key generation, and parsing a public key expands its matrix. An
  encapsulated key is an ML-KEM ciphertext, so `Kem.encapsulated_key_size` is
  no longer `Kem.public_key_size` for every KEM. One of the right length never
  fails to decapsulate: a forged one yields an unrelated secret (implicit
  rejection), and the failure surfaces as `Open_error` at the first open. The
  draft is not yet an RFC, and `derive_key_pair` for these KEMs follows it.
- Add `Kem.supports_auth` and `Error.Unsupported_mode`. ML-KEM has no
  authenticated encapsulation, so on an ML-KEM suite the Auth and AuthPSK
  functions return `Unsupported_mode` before they look at a key or draw
  randomness, and the single-shot opens leave it distinguishable, as they do
  `Key_mismatch`. The new constructor breaks exhaustive matches on `Error.t`.
- Depend on [`mlkem`](https://github.com/thevilledev/ocaml-pq) for the ML-KEM
  primitive, and for the SHAKE256 that deriving an ML-KEM key pair takes:
  `mlkem` exports the one ML-KEM itself runs on as `Mlkem.Fips202`, so the
  library still implements no primitive of its own.
- `hpke.for_testing` refuses an ML-KEM suite, which has no ephemeral key to
  choose: its Base and PSK senders return `Invalid_private_key`, and its Auth
  and AuthPSK senders `Unsupported_mode`, as the ordinary Auth and AuthPSK
  functions do. A generator that returns the fixed encapsulation randomness,
  passed as `~rng` to the ordinary setup functions, reproduces such vectors.
- Pin the `draft-ietf-hpke-pq-05` corpus: its three ML-KEM vectors that use an
  HKDF, replayed in full, and the fourth as far as the KEM goes.
- Parse private keys through one exhaustive match on the KEM. The previous
  wildcard would have let a new KEM skip clamping without a compiler warning.
- Release a context when an exception from a signal handler interrupts
  `Sender.seal` or `Receiver.open_` while it marks the context busy. Since
  0.1.0, `Fun.protect` allocated before installing its handler, and on an
  exception again before releasing the context, and an exception raised at
  either allocation left the context marked busy for good, so that every later
  call returned `Concurrent_use`.
- Check X25519 and X448 private-key clamping against literal bytes. The vector
  corpus cannot: it compares serializations that have both passed through the
  library's own clamp, and the primitives clamp again when they use a scalar.
- Never let an interrupted `Sender.seal` or `Receiver.open_` rewind a
  context's sequence number. Since 0.1.0, an exception raised by a signal
  handler, such as `Sys.Break` or a timeout, could stop the increment between
  two byte stores and leave the sequence 255 or more below the number just
  used. A caller that caught it and kept the context then sealed under nonces
  it had already used, and a receiver accepted replays. The increment now
  stores the carried byte first, so an interrupted one can at most skip
  sequence numbers.
- Parse the Diffie-Hellman secret once per private key, and not on every
  exchange. Parsing derives the public key, a scalar multiplication whose
  result every exchange discarded. X25519 and X448 have no shortcut for the
  base point, so there it cost as much as the exchange itself: setting up a
  receiver is up to twice as fast and setting up a sender up to half again as
  fast. The NIST curves multiply the base point from a table and gain a little
  over a tenth.
- Refuse an AES-GCM plaintext of 2^36 - 31 bytes as `Plaintext_too_long`.
  Since 0.1.0 the limit was RFC 5116's, one byte beyond NIST SP 800-38D (RFC
  5116 erratum 5219). mirage-crypto refuses that byte itself, so `Aead.seal`
  and `Rfc9180.Sender.seal` returned `Internal_error` for it, where the
  interface promises `Plaintext_too_long`. Every shorter plaintext seals as
  before.
- Keep the RFC 9180 wire behavior of the existing KEMs and modes unchanged
  from 0.2.0.

## 0.2.0 — 2026-09-18

- Export the suite's unlabeled primitives for protocols layered on HPKE, such
  as Oblivious HTTP (RFC 9458): `Kdf.extract` and `Kdf.expand` (plain RFC 5869
  HKDF) and the single-shot `Aead.seal` and `Aead.open_` under a key prepared
  by `Aead.key` and an explicit nonce. Wrong-sized keys, nonces, pseudorandom
  keys, and output lengths are reported as `Invalid_length`.
- Expand the AEAD key once per context, and not on every seal and open.
  Without hardware support, deriving the GHASH tables of an AES-GCM key costs
  more than sealing several kilobytes, so contexts that carry many messages
  are several times faster.
- Export the RFC 9180 parameters `Aead.key_size`, `Aead.nonce_size`,
  `Aead.tag_size`, `Kdf.hash_size`, and `Kem.secret_size`.
- Add the separate `hpke.for_testing` library, which sets up a Base or PSK
  sender from a caller-chosen ephemeral private key so that vectors which fix
  `skE` can be reproduced. It must never be linked outside a test suite.
- Retain the key-schedule intermediates in the pinned RFC 9180 corpus and use
  them, the published `skEm`, and every encryption record as known answers
  for the new entry points.
- Keep the existing API and RFC 9180 wire behavior unchanged from 0.1.1.

## 0.1.1 — 2026-08-29

- Expand known-answer coverage to all 48 supported Base and PSK combinations
  in the pinned RFC 9180 corpus, including representative 257-message
  sequences and the independent Go P-384 fixture.
- Broaden malformed-input, mismatch, concurrency, property, and Crowbar fuzz
  coverage across every supported KEM and AEAD.
- Test OCaml 4.14, 5.2, and 5.5 on Linux, OCaml 4.14 and 5.5 on macOS, declared
  dependency lower bounds, and isolated OPAM package installation.
- Accommodate OCaml 5.5's stricter GADT exhaustiveness analysis.
- Keep the public API and RFC 9180 wire behavior unchanged from 0.1.0.
- Remain an unaudited, non-production release intended for interoperability
  review.

## 0.1.0 — 2026-08-23

- Add RFC 9180 Base and PSK setup, stateful contexts, single-shot APIs, and
  export-only suites.
- Add P-256, P-384, P-521, and X25519 DHKEM; SHA-2 HKDFs; AES-GCM and
  ChaCha20-Poly1305.
- Add abstract validated keys, deterministic `DeriveKeyPair`, explicit-RNG key
  generation, and minimum-length PSK values.
- Add atomic context-use guards, 96-bit sequence counters, bounds checks, and
  normalized single-shot open errors.
- Add pinned RFC vectors, all-suite round trips, adversarial/state tests,
  QCheck properties, and Crowbar fuzz targets.
- Add a security policy and release-readiness checks.
