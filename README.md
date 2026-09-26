# hpke

`hpke` is an idiomatic OCaml implementation of Hybrid Public Key Encryption
([RFC 9180](https://www.rfc-editor.org/rfc/rfc9180.html)). It exposes the
Base, PSK, Auth, and AuthPSK modes under the explicitly versioned
`Hpke.Rfc9180` module and delegates elliptic-curve, ML-KEM, hash, and AEAD
primitives to Mirage Crypto, `curve448`, `mlkem`, Digestif, and `kdf`.
Post-quantum ML-KEM and ML-KEM/elliptic-curve hybrid KEMs such as X-Wing are
supported.

The project aims to provide a maintained, packaged, and idiomatic OCaml HPKE
library.

See [SECURITY.md](SECURITY.md) before using it with sensitive data.

## Installation

```sh
opam install hpke
```

## Documentation

Usage, ciphersuites, the security model, and development notes:
[ville.dev/ocaml-hpke](https://ville.dev/ocaml-hpke/)

## Supported algorithms

| Component | Algorithms |
| --- | --- |
| KEM | P-256, P-384, P-521, X25519, X448 DHKEM; ML-KEM-512, ML-KEM-768, ML-KEM-1024; MLKEM768-P256, MLKEM768-X25519 (X-Wing), MLKEM1024-P384 |
| KDF | HKDF-SHA-256, HKDF-SHA-384, HKDF-SHA-512 |
| AEAD | AES-128-GCM, AES-256-GCM, ChaCha20-Poly1305, export-only |
| Modes | RFC 9180 Base, PSK, Auth, and AuthPSK; ML-KEM and the hybrids have the first two |

| Feature scope | Status |
| --- | --- |
| RFC 9180 Base, PSK, Auth, AuthPSK, export-only, and the algorithms above | Implemented |
| Post-quantum ML-KEM KEMs of `draft-ietf-hpke-pq`, in the Base and PSK modes | Implemented |
| Post-quantum/traditional hybrid KEMs of the same draft, in the Base and PSK modes | Implemented |
| SHA-3 KDFs of the same draft | Deferred |
| HPKE-bis or another successor standard | Deferred to a new versioned module |
| Application wire framing | Deferred to applications |

The deferred features are intentionally out of scope for now. They do not
change the wire behavior of `Hpke.Rfc9180`.

## X448 backends

X448 is provided by [`curve448`](https://github.com/thevilledev/ocaml-curve448),
which implements its arithmetic twice and lets the final executable choose.
`hpke` depends on the plain `curve448` library, so an application that says
nothing gets the pure OCaml implementation. To use the C implementation, which
is two to three times faster, name it next to `hpke`:

```dune
(executable
 (name server)
 (libraries hpke curve448.c))
```

Both behave identically. With ocamlfind instead of dune, the `curve448`
package holds only the interface, so link `curve448.ocaml` or `curve448.c`
explicitly. `curve448` needs a 64-bit OCaml, so `hpke` is no longer
installable on 32-bit architectures.

## ML-KEM

`Kem.Mlkem512`, `Kem.Mlkem768`, and `Kem.Mlkem1024` are the post-quantum KEMs
of [FIPS 203](https://csrc.nist.gov/pubs/fips/203/final), as
[`draft-ietf-hpke-pq`](https://datatracker.ietf.org/doc/draft-ietf-hpke-pq/)
defines them for HPKE, provided by the pure OCaml
[`mlkem`](https://github.com/thevilledev/ocaml-pq). They are a choice of KEM
and nothing else changes: with an HKDF they run the RFC 9180 key schedule as
it is.

```ocaml
let suite =
  Suite.create ~kem:Kem.Mlkem768 ~kdf:Kdf.Hkdf_sha256 ~aead:Aead.Aes_128_gcm
```

What differs from a Diffie-Hellman KEM:

- There is no Auth or AuthPSK mode. ML-KEM has no authenticated encapsulation,
  so those functions return `Unsupported_mode`, and `Kem.supports_auth` tells
  the two kinds of KEM apart. Use a PSK, or sign the encapsulated key and the
  ciphertext.
- A private key is the 64-byte seed that FIPS 203 generates a key pair from,
  and not the expanded decapsulation key. Parsing one runs key generation, and
  parsing a public key expands its matrix, so parse a key once and keep it.
- Keys and encapsulated keys are large, and an encapsulated key is not the size
  of a public key: 1,088 and 1,184 bytes for ML-KEM-768.
- An encapsulated key of the right length never fails to decapsulate. One that
  was tampered with gives the receiver a secret unrelated to the sender's
  (implicit rejection), so `setup_base_receiver` succeeds and the first
  `open_` returns `Open_error`.

The draft is not yet an RFC. Encodings are those of FIPS 203 and are not
expected to move, but `derive_key_pair` follows the draft, which derives the
seed with SHAKE256, and changes if the draft does. That SHAKE256 is `mlkem`'s
as well, the one ML-KEM itself runs on. The draft prefers ML-KEM-768 and
ML-KEM-1024 to ML-KEM-512. See [SECURITY.md](SECURITY.md) for the audit status
of `mlkem`.

## Hybrid KEMs

`Kem.Mlkem768_p256`, `Kem.Mlkem768_x25519`, and `Kem.Mlkem1024_p384` are the
post-quantum/traditional hybrid KEMs of `draft-ietf-hpke-pq`, MLKEM768-P256,
MLKEM768-X25519, and MLKEM1024-P384, as
[`draft-irtf-cfrg-concrete-hybrid-kems`](https://datatracker.ietf.org/doc/draft-irtf-cfrg-concrete-hybrid-kems/)
defines them. Each runs ML-KEM and an elliptic-curve Diffie-Hellman exchange
side by side and hashes both secrets together with SHA3-256, so a message stays
protected as long as either ML-KEM or the curve holds. `Kem.Mlkem768_x25519` is
[X-Wing](https://datatracker.ietf.org/doc/draft-connolly-cfrg-xwing-kem/),
identifier `0x647a`. Like ML-KEM they are a choice of KEM and nothing else
changes:

```ocaml
let suite =
  Suite.create ~kem:Kem.Mlkem768_x25519 ~kdf:Kdf.Hkdf_sha256
    ~aead:Aead.Chacha20_poly1305
```

They behave as ML-KEM does, with no Auth or AuthPSK mode, except in what
follows from the second half:

- A private key is a 32-byte seed. Parsing one expands it with SHAKE256 into an
  ML-KEM seed and a scalar and runs ML-KEM key generation, so parse a key once
  and keep it. `derive_key_pair` derives the seed with SHAKE256, as for ML-KEM.
- A public key is the ML-KEM encapsulation key followed by the group element,
  an uncompressed SEC1 point or an X25519 public value: 1,216 bytes for
  X-Wing. An encapsulated key is the ML-KEM ciphertext followed by an ephemeral
  element: 1,120 bytes for X-Wing.
- A tampered ML-KEM ciphertext decapsulates to an unrelated secret, as it does
  alone, but an element that is not on the curve, or an X25519 value of low
  order, is refused as `Invalid_encapsulation`. The concrete draft leaves the
  X25519 value unchecked; no honest peer produces one that is refused.

Neither draft is an RFC yet, and `derive_key_pair` changes if they do. The
three hybrids reproduce every vector of `draft-ietf-hpke-pq-05` that uses an
HKDF: see [test-vectors/PROVENANCE.md](test-vectors/PROVENANCE.md).

## Example

The caller owns RNG initialization and passes an explicit generator to every
operation that needs randomness:

```ocaml
open Hpke

let () =
  Mirage_crypto_rng_unix.initialize (module Mirage_crypto_rng.Fortuna);
  let rng = Mirage_crypto_rng.default_generator () in
  let suite =
    Suite.create ~kem:Kem.X25519 ~kdf:Kdf.Hkdf_sha256
      ~aead:Aead.Chacha20_poly1305
  in
  match generate_key_pair ~rng Kem.X25519 with
  | Error error -> Format.eprintf "key generation: %a@." Error.pp error
  | Ok (recipient_private, recipient_public) -> (
      match
        Rfc9180.seal_base ~rng suite ~recipient:recipient_public
          ~info:"application-v1" ~aad:"message-metadata"
          ~plaintext:"secret payload"
      with
      | Error error -> Format.eprintf "seal: %a@." Error.pp error
      | Ok ciphertext ->
          match
            Rfc9180.open_base suite ~recipient:recipient_private
              ~info:"application-v1" ~aad:"message-metadata" ~ciphertext
          with
          | Ok plaintext -> assert (String.equal plaintext "secret payload")
          | Error error -> Format.eprintf "open: %a@." Error.pp error)
```

`encapsulated_key` and `ciphertext` remain separate fields. The library does
not invent an application wire format.

PSKs are constructed with `Psk.create ~secret ~id`. Construction rejects
secrets shorter than 32 bytes and empty identifiers. This is only a length
check; it cannot establish that a secret has adequate entropy.

The Auth and AuthPSK modes also authenticate the sender with a static KEM key
pair. The sender passes its private key and the recipient the sender's public
key, both as `~sender`:

```ocaml
Rfc9180.seal_auth ~rng suite ~recipient:recipient_public
  ~sender:sender_private ~info ~aad ~plaintext

Rfc9180.open_auth suite ~recipient:recipient_private
  ~sender:sender_public ~info ~aad ~ciphertext
```

The message opens only as coming from the holder of that key, but this is not
a signature. Whoever holds the recipient's private key, and in AuthPSK mode the
PSK as well, can seal as any sender, so a recipient cannot prove to anyone else
who sent a message: see [SECURITY.md](SECURITY.md). The successor draft of HPKE drops both modes; they
stay in `Hpke.Rfc9180`, whose wire behavior does not change.

## Context rules

Sender contexts only seal and receiver contexts only open. Successful
operations consume exactly one nonce. Failed opens do not advance the sequence.
If two domains or threads attempt a state-changing operation on the same
context, one receives `Concurrent_use` before cryptography is performed. Do
not retry concurrent calls without application-level ordering: the caller must
know which operation consumed the next sequence number.

HPKE contexts do not recover from message loss or reordering. For protocol
boundaries, prefer the single-shot `open_base`, `open_psk`, `open_auth`, and
`open_auth_psk` functions; they normalize peer-controlled decapsulation and
authentication failures to `Open_error`.

## Building protocols on HPKE

Protocols layered on HPKE often derive further keys from an exported secret
with the suite's own KDF and AEAD; Oblivious HTTP
([RFC 9458](https://www.rfc-editor.org/rfc/rfc9458.html)) encrypts its
responses this way. The suite's unlabeled primitives are exposed so that a
consumer does not repeat the identifier-to-algorithm dispatch:

- `Kdf.extract` and `Kdf.expand` are plain RFC 5869 HKDF, without the labels
  that HPKE's own key schedule adds.
- `Aead.key` prepares a key, and `Aead.seal` and `Aead.open_` use it with an
  explicit nonce. Unlike a context they cannot prevent nonce reuse; that is the
  caller's responsibility. Preparing an AES-GCM key is costly where the
  hardware does not help, so prepare it once for everything sealed under it.
- `Aead.key_size`, `Aead.nonce_size`, `Aead.tag_size`, `Kdf.hash_size`, and
  `Kem.secret_size` report the RFC 9180 parameters Nk, Nn, Nt, Nh, and Nsecret.

The separate `hpke.for_testing` library sets up a sender from a caller-chosen
ephemeral private key. It exists to reproduce published vectors that fix that
key, and must never be linked outside a test suite: see
[SECURITY.md](SECURITY.md).

## Development

```sh
opam install . --deps-only --with-test --with-doc
dune build @all @doc
dune runtest
dune build --profile fuzz fuzz/fuzz_hpke.exe
_build/default/fuzz/fuzz_hpke.exe --repeat 1000
opam lint hpke.opam
```

Official test-vector provenance is pinned in
[test-vectors/PROVENANCE.md](test-vectors/PROVENANCE.md).

See the [development guide](https://ville.dev/ocaml-hpke/development.html) for
the project layout, CI matrix, and test-vector policy.

## Acknowledgments

This project acknowledges
[`FantomeBeignet/ohpke`](https://github.com/FantomeBeignet/ohpke), an earlier
OCaml HPKE experiment. That project is currently unmaintained; this library is
an independent implementation that builds on the prior exploration of HPKE in
OCaml.

## License

ISC. See [LICENSE](LICENSE).
