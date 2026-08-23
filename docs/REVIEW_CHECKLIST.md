# External review checklist

`0.1.0` may be tagged only after every required item is checked and the result
is linked from the release notes. `1.0.0` additionally requires an independent
cryptographic review and API stabilization period.

## Cryptographic construction

- [ ] Compare every numeric identifier, label, input ordering, and output size
  with RFC 9180.
- [ ] Review NIST scalar orders, P-521 masking, rejection-loop bounds, SEC1
  validation, X25519 clamping, and low-order handling.
- [ ] Confirm KEM context ordering is `enc || pkR` for Base/PSK.
- [ ] Confirm PSK mode byte and PSK input validation.
- [ ] Confirm nonce XOR is big-endian, all 96 bits are retained, failure occurs
  before exhaustion, and failed opens do not advance state.
- [ ] Confirm AEAD and exporter limits match the selected primitive/KDF.

## API and misuse resistance

- [ ] No public raw secret constructors, secret printers, equality helpers,
  provider injection, state cloning, or unsafe test hooks.
- [ ] Export-only suites cannot type-check with `seal` or `open_`.
- [ ] Sender and receiver roles are distinct and contexts are abstract.
- [ ] Every peer-controlled path returns a typed result and fuzzing finds no
  unexpected exception.
- [ ] Single-shot open normalizes decapsulation and AEAD failures.
- [ ] Concurrent state-changing use returns `Concurrent_use` without invoking
  cryptography or incrementing the counter.

## Interoperability and operations

- [ ] Pinned official Base/PSK vectors and overlapping successor vectors pass.
- [ ] Independent differential fixtures cover all tuples missing from official
  vectors, especially P-384.
- [ ] Linux and macOS CI pass on OCaml 4.14 and representative OCaml 5 versions.
- [ ] QCheck properties and Crowbar smoke tests pass; longer fuzz campaigns
  report corpus duration and toolchain.
- [ ] `dune build @all @doc`, `dune runtest`, formatting, `opam lint`, and
  lower-bound dependency builds pass.
- [ ] Assurance boundaries, GC/zeroization limits, and protocol non-goals remain
  prominent in README and security documentation.
- [ ] A private vulnerability-reporting channel is configured.
- [ ] Prior `ohpke` work is credited, its maintainer has been contacted, and the
  `hpke` opam name is reconfirmed before submission.
