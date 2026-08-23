# Test-vector provenance

The hexadecimal fixtures embedded in `test/test_hpke.ml` are copied from
Appendix A of [RFC 9180](https://www.rfc-editor.org/rfc/rfc9180.html), whose
machine-readable source is pinned at CFRG commit
[`5f503c564da00b0687b3de75f1dfbdfc4079ad31`](https://github.com/cfrg/draft-irtf-cfrg-hpke/blob/5f503c564da00b0687b3de75f1dfbdfc4079ad31/test-vectors.json).

The included fixtures cover:

- A.1.1: X25519 / HKDF-SHA256 / AES-128-GCM, Base mode;
- A.1.2: X25519 / HKDF-SHA256 / AES-128-GCM, PSK mode;
- A.2.1: X25519 / HKDF-SHA256 / ChaCha20-Poly1305, Base mode.

The RFC vectors are also the overlapping Base/PSK vectors in
`draft-ietf-hpke-hpke-04`. That successor draft and its edge-case generator are
pinned at HPKE working-group commit
[`4abc37efc36a4295519964e366f650814b0f3cff`](https://github.com/hpkewg/hpke/tree/4abc37efc36a4295519964e366f650814b0f3cff).
Tests additionally pin its Appendix C.8 export-only vector and Appendix D
vectors for P-256 rejection sampling, empty inputs, embedded zero bytes, and
empty `info`. Local malformed-input tests cover invalid encodings, off-curve
points, invalid scalars, low-order X25519 values, tampering, and error
normalization.

The P-384 / HKDF-SHA384 / AES-256-GCM fixture was generated independently by
Go 1.26.5's standard-library `crypto/hpke` implementation. The small generator
is retained at `tools/differential/go/main.go`; it derives a fixed recipient
key, while its one-time random encapsulation and resulting ciphertext/exporter
outputs are pinned in the OCaml test.

The repository does not silently update vectors from a moving branch. Changes
to these fixtures must cite a standards revision and immutable source commit.
