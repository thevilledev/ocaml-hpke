(lang dune 3.12)
(name hpke)
(generate_opam_files false)
(source (github thevilledev/ocaml-hpke))
(license ISC)
(authors "Ville Vesilehto <ville@vesilehto.fi>")
(maintainers "Ville Vesilehto <ville@vesilehto.fi>")

(package
 (name hpke)
 (synopsis "Idiomatic RFC 9180 Hybrid Public Key Encryption for OCaml")
 (description
  "A misuse-resistant OCaml implementation of HPKE Base and PSK modes, built on Mirage Crypto primitives.")
 (tags
  (cryptography hpke rfc9180 "hybrid encryption")))
