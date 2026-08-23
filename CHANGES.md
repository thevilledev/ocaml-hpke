# Changelog

## 0.1.0-dev — 2026-08-23

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
