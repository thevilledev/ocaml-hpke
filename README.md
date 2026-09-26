# hpke

Hybrid Public Key Encryption ([RFC 9180](https://www.rfc-editor.org/rfc/rfc9180.html))
for OCaml. Encrypt to a recipient's public key; decrypt with their private key.

Requires 64-bit OCaml 4.14+ and Dune 3.12+. No release is supported for
production use yet. Read the [security policy](SECURITY.md).

## Run an example

In an initialized opam switch:

```sh
opam install hpke
mkdir hpke-example
cd hpke-example
```

Create `dune-project`:

```dune
(lang dune 3.12)
```

Create `dune`:

```dune
(executable
 (name main)
 (libraries hpke mirage-crypto-rng.unix))
```

Create `main.ml`:

```ocaml
open Hpke

let ( let* ) = Result.bind

let round_trip ~rng =
  let suite =
    Suite.create ~kem:Kem.X25519 ~kdf:Kdf.Hkdf_sha256
      ~aead:Aead.Chacha20_poly1305
  in
  let* private_key, public_key =
    generate_key_pair ~rng Kem.X25519
  in
  let info = "example-v1" and aad = "message-1" in
  let* ciphertext =
    Rfc9180.seal_base ~rng suite ~recipient:public_key ~info ~aad
      ~plaintext:"Hello, HPKE."
  in
  Rfc9180.open_base suite ~recipient:private_key ~info ~aad
    ~ciphertext

let () =
  Mirage_crypto_rng_unix.use_default ();
  let rng = Mirage_crypto_rng.default_generator () in
  match round_trip ~rng with
  | Ok plaintext -> print_endline plaintext
  | Error error ->
      Format.eprintf "%a@." Error.pp error;
      exit 1
```

Run it:

```sh
opam exec -- dune exec ./main.exe
```

Output: `Hello, HPKE.`

The example keeps both keys in one process. In an application, the sender
needs a trusted copy of the recipient's public key; only the recipient needs
the private key.

- `seal_base` returns two byte strings: `encapsulated_key` and `ciphertext`.
  Send both; your protocol defines their encoding.
- `info` identifies the protocol or purpose. `aad` is authenticated message
  metadata. Neither is encrypted or sent by the library; both must match
  exactly when opening.
- Base mode does not authenticate the sender. Use PSK, Auth, or AuthPSK when
  your protocol requires sender authentication.

## Choose an API

| Need | API |
| --- | --- |
| One independent message | `Rfc9180.seal_base` / `open_base` |
| A pre-shared secret | `seal_psk` / `open_psk`, with `Psk.create` |
| A sender key | `seal_auth` / `open_auth` (DHKEM only); AuthPSK also takes a PSK |
| Several ordered messages | `setup_*_sender` / `setup_*_receiver`, then `Sender.seal` / `Receiver.open_` |
| Derived keys without encryption | `Suite.export_only`, then context `export` |

The seal, open, setup, and context operations are under `Hpke.Rfc9180`.
Keep context operations serial and messages in order. Single-shot opens report
peer-controlled failures as `Open_error`.

## Algorithms and versions

- **KEM:** P-256, P-384, P-521, X25519, X448; ML-KEM-512, -768, -1024;
  MLKEM768-P256, MLKEM768-X25519 (X-Wing), MLKEM1024-P384.
- **KDF:** HKDF-SHA256, -SHA384, -SHA512. `Hpke.Draft_hpke_04` also has
  SHAKE128 and SHAKE256.
- **AEAD:** AES-128-GCM, AES-256-GCM, ChaCha20-Poly1305.

ML-KEM and hybrid KEMs support Base and PSK only. `Hpke.Draft_hpke_04`
implements the successor draft with those two modes; `Hpke.Rfc9180` keeps
its RFC wire behavior. Hybrid KEMs and `Draft_hpke_04` require 0.4.0-rc1;
see [installation options](https://ville.dev/ocaml-hpke/usage.html#install).

## Documentation

- [Usage](https://ville.dev/ocaml-hpke/usage.html): keys, modes, contexts, exports, errors.
- [Ciphersuites](https://ville.dev/ocaml-hpke/suites.html): identifiers, sizes, draft support.
- [API reference](lib/hpke.mli): signatures and error contracts.
- [Development](https://ville.dev/ocaml-hpke/development.html): builds, tests, contributions.
- [Changelog](CHANGES.md) and [test-vector sources](test-vectors/PROVENANCE.md).

To build this checkout in an initialized opam switch:

```sh
opam install . --deps-only --with-test --with-doc
opam exec -- dune build @all @doc
opam exec -- dune runtest
```

## License

[ISC](LICENSE). Independent implementation; prior OCaml work:
[FantomeBeignet/ohpke](https://github.com/FantomeBeignet/ohpke).
