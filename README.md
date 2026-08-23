# hpke

`hpke` is an idiomatic OCaml implementation of Hybrid Public Key Encryption
([RFC 9180](https://www.rfc-editor.org/rfc/rfc9180.html)). It exposes Base and
PSK modes under the explicitly versioned `Hpke.Rfc9180` module and delegates
elliptic-curve, hash, and AEAD primitives to Mirage Crypto, Digestif, and
`kdf`.

The project aims to provide a maintained, packaged, and idiomatic OCaml HPKE
library.

> **Pre-release status:** `0.1.0-dev` is for interoperability review. It has not
> received an independent cryptographic audit. See [ASSURANCE.md](docs/ASSURANCE.md)
> and [SECURITY.md](SECURITY.md) before using it with sensitive data.

## Supported algorithms

| Component | Algorithms |
| --- | --- |
| KEM | P-256, P-384, P-521, X25519 DHKEM |
| KDF | HKDF-SHA-256, HKDF-SHA-384, HKDF-SHA-512 |
| AEAD | AES-128-GCM, AES-256-GCM, ChaCha20-Poly1305, export-only |
| Modes | RFC 9180 Base and PSK |

X448 is intentionally unsupported because there is no suitable maintained
primitive in the selected OCaml backend. Auth and AuthPSK are intentionally not
part of the initial surface. A successor standard can be added in a new
versioned module without changing `Hpke.Rfc9180` wire behavior.

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
[test-vectors/PROVENANCE.md](test-vectors/PROVENANCE.md). Release readiness is
tracked by [REVIEW_CHECKLIST.md](docs/REVIEW_CHECKLIST.md).

## Acknowledgments

This project acknowledges
[`FantomeBeignet/ohpke`](https://github.com/FantomeBeignet/ohpke), an earlier
OCaml HPKE experiment. That project is currently unmaintained; this library is
an independent implementation that builds on the prior exploration of HPKE in
OCaml.

## License

ISC. See [LICENSE](LICENSE).
