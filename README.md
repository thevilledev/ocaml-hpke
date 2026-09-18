# hpke

`hpke` is an idiomatic OCaml implementation of Hybrid Public Key Encryption
([RFC 9180](https://www.rfc-editor.org/rfc/rfc9180.html)). It exposes Base and
PSK modes under the explicitly versioned `Hpke.Rfc9180` module and delegates
elliptic-curve, hash, and AEAD primitives to Mirage Crypto, Digestif, and
`kdf`.

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
| KEM | P-256, P-384, P-521, X25519 DHKEM |
| KDF | HKDF-SHA-256, HKDF-SHA-384, HKDF-SHA-512 |
| AEAD | AES-128-GCM, AES-256-GCM, ChaCha20-Poly1305, export-only |
| Modes | RFC 9180 Base and PSK |

| Feature scope | Status |
| --- | --- |
| RFC 9180 Base, PSK, export-only, and the algorithms above | Implemented |
| Auth and AuthPSK modes | Deferred |
| X448 | Deferred pending a suitable maintained OCaml primitive |
| Post-quantum and hybrid KEMs | Deferred |
| HPKE-bis or another successor standard | Deferred to a new versioned module |
| Application wire framing | Deferred to applications |

The deferred features are intentionally outside the first OPAM release. They
do not change the wire behavior of `Hpke.Rfc9180`.

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

## Context rules

Sender contexts only seal and receiver contexts only open. Successful
operations consume exactly one nonce. Failed opens do not advance the sequence.
If two domains or threads attempt a state-changing operation on the same
context, one receives `Concurrent_use` before cryptography is performed. Do
not retry concurrent calls without application-level ordering: the caller must
know which operation consumed the next sequence number.

HPKE contexts do not recover from message loss or reordering. For protocol
boundaries, prefer the single-shot `open_base` and `open_psk` functions; they
normalize peer-controlled decapsulation and authentication failures to
`Open_error`.

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
