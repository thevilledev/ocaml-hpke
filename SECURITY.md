# Security policy

## Supported versions

No released version is currently supported for production use. The `0.1.x`
series is intended for interoperability review. Security fixes will be applied
to the latest `0.1.x` release until a stable policy is published with `1.0.0`.

## Reporting a vulnerability

Do not open a public issue for a suspected vulnerability. Use GitHub's private
[security-advisory reporting
flow](https://github.com/thevilledev/ocaml-hpke/security/advisories/new) for this
repository. Include the affected version or commit, suite and mode, a minimal
reproduction, and your assessment of confidentiality and nonce-reuse impact.
Maintainers should acknowledge a report within seven days and coordinate
disclosure after a fix is available.

## Operational cautions

- Initialize a cryptographically secure Mirage Crypto RNG and pass it
  explicitly. Deterministic or test RNGs must never be used in production.
- `Aead.seal` takes an explicit key and nonce and cannot prevent their reuse.
  Sealing twice under one `(key, nonce)` pair forfeits both confidentiality
  and authenticity. Prefer a context, which sequences nonces itself, and derive
  a fresh key or nonce for every single-shot call.
- A sender or receiver context is stateful. Serialize access at the application
  layer. `Concurrent_use` means no cryptography was performed by that call.
- Treat `Open_error` uniformly at protocol boundaries. Do not build an oracle
  by translating lower-level setup errors into distinguishable responses.
- Do not log private-key or PSK byte strings. The public API intentionally has
  no secret printers or equality helpers.
- OCaml garbage collection prevents guaranteed secret zeroization. Processes
  handling long-lived secrets should minimize retention and consider process
  isolation appropriate to their threat model.
