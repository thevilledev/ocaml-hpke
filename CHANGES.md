# Changelog

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
