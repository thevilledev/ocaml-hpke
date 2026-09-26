# Formal verification

This directory holds machine-checked models of `lib/hpke.ml`. They are
checked against RFC 9180, draft-ietf-hpke-pq-05, draft-irtf-cfrg-hybrid-kems,
draft-irtf-cfrg-concrete-hybrid-kems, draft-ietf-hpke-hpke-04,
RFC 5869, RFC 7748, RFC 8439 and NIST SP 800-38D.

| Directory | Tool | What it does |
| --- | --- | --- |
| `lean/` | Lean 4.34, core library only | Proves the pure functions and the context state machines, for every input, counter width and number of domains. |
| `tla/` | TLA+, checked with TLC 2.19 | Model-checks the concurrent context step by step on OCaml 5 domains, with asynchronous exceptions, and a sender and receiver over a hostile network. Includes liveness. |
| `conformance/` | dune test | Replays the outputs of the Lean mirrors against `lib/hpke.ml` itself. |

The OCaml functions are transcribed into Lean as mirrors. A theorem about a
mirror says something about the library only if the mirror computes what the
OCaml computes. `conformance/` checks this on every `dune runtest`:

* `lean/Conformance.lean` evaluates the mirrors on edge cases and
  pseudo-random inputs and writes `conformance/vectors.txt`.
* `conformance/conformance.ml` compiles a copy of `lib/hpke.ml` without its
  interface, calls the real internal functions, and compares every line.
* It covers 13800 checks. Among them are all 2904 combinations of suite KEM,
  recipient KEM, sender KEM and mode, each run through the real sender and
  receiver setup functions with real keys, and all 2420 combinations of suite
  KEM, recipient KEM, KDF, mode and input length for `Draft_hpke_04`.

## What is proved

Every theorem depends only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). There is no `sorry`, `admit`, global
`axiom` or `native_decide`. The cryptographic primitives are hypotheses,
listed under [Trusted base](#trusted-base).

| Lean module | `lib/hpke.ml` | Main results |
| --- | --- | --- |
| `Bytes` | (foundation) | `I2OSP`/`OS2IP` are inverse and injective; XOR with a fixed pad is injective. |
| `Registry` | `Error`, `Kem`, `Kdf`, `Aead` | Every size and identifier equals RFC 9180 Tables 2, 3 and 5 and the draft-pq ML-KEM and hybrid tables. A hybrid's sizes are its ML-KEM part's plus its group's. `of_int` and `to_int` are inverse, and every unknown identifier is `Unsupported_algorithm`. |
| `Encoding` | `Util.i2osp2`, `Labeled_kdf` | `suite_id` and the KEM suite id are the RFC's and injective. `LabeledExtract`, `LabeledExpand` and `LabeledDerive` build exactly the specified inputs. The key-schedule context separates modes. The internal `I2OSP(·, 2)` never raises. RFC 9180's unchecked input-length limits exceed every OCaml string. |
| `Sequence` | `sequence_exhausted`, `increment_sequence`, `nonce` | The increment is `+1 mod 256^n`. Exhaustion holds exactly at `2^96 - 1`. The nonce is `ComputeNonce`. Distinct sequence numbers give distinct nonces. |
| `Atomicity` | `increment_sequence`, one byte store at a time | Finding 3. The fix computes the same increment on every input, and none of its intermediate states is below the new value. |
| `AeadLimits` | `Aead.plaintext_fits` and its callers | Finding 1, and the proof that `2^36 - 32` is exact for every AEAD and length. |
| `Scalar` | `curve_order`, `valid_nist_scalar`, `all_zero`, clamping, `derive_key_pair`, `generate_key_pair` | The curve orders equal OpenSSL's. `valid_nist_scalar b ↔ 0 < OS2IP(b) < n`, including `Eqaf.compare_be` modelled bit-exactly. Rejection sampling equals RFC 9180 §7.1.3. The hybrids' `random_scalar` is the concrete draft's `RandomScalar` and never yields a zero scalar. Clamping is RFC 7748's decodeScalar and idempotent. |
| `Keys` | `parse_public_bytes`, `Public_key`, `Private_key`, `dh` | Lengths are checked first. NIST keys, and the NIST elements of hybrid keys, must be uncompressed SEC1. A hybrid key's ML-KEM half passes the modulus check. A parsed key re-serializes to its input. `dh` returns `Key_mismatch` before any exchange. |
| `Kem` | `encap_with`, `dh_decap`, `encap`, `decap`, `Mlkem_kem`, `Hybrid_kem` | The code is RFC 9180's `Encap`, `Decap`, `AuthEncap` and `AuthDecap`, the draft's ML-KEM KEM, and the CG framework's `DeriveKeyPair`, `Encaps` and `Decaps` for the hybrids. Decapsulation recovers the encapsulated secret. The hybrids' `encap` uses the first of its eight draws that holds a scalar. A sender key on ML-KEM or a hybrid is `Unsupported_mode`, never dropped. The error mapping holds. |
| `Draft` | `Draft_hpke_04`: `Kdf`, `length_prefixed`, `one_stage_schedule`, the one-stage branch of `export`, `setup_*` | The KDF registry is that of draft-ietf-hpke-hpke-04 and draft-ietf-hpke-pq-05, and its HKDFs are RFC 9180's. The one-stage key schedule hands the KDF exactly `CombineSecrets_OneStage`'s input, which binds the mode, PSK, shared secret, PSK identifier and `info` unambiguously, and splits the output into the draft's key, nonce and exporter secret. An input over 65535 bytes is `Invalid_length`, and a one-stage export `Export_length_out_of_range` exactly outside `[0, 65535]`; neither raises. |
| `Setup` | `Psk`, `key_schedule`, `check_*`, `setup_*`, `normalized_open`, `Private` | Every typed mode passes `VerifyPSKInputs`. The key schedule is the RFC's, and sender and receiver agree. Every error contract in `hpke.mli` holds, and a computable table predicts every setup result. |
| `TLA` | (foundation) | Specifications, invariants, behaviours, and stuttering refinement. |
| `Context` | `with_busy`, `seal`, `open_ciphertext` | For any number of domains: mutual exclusion; no nonce reuse (the nonces used are exactly `ComputeNonce(0..k-1)`); the all-ones nonce is never used; and the implementation refines RFC 9180's atomic context. |
| `ContextAsync` | the same, with asynchronous exceptions | Finding 3 as a reachable trace of the real 12-byte context, and the proof that the fix never reuses a nonce. |
| `Channel` | sender and receiver over a Dolev-Yao network | The receiver accepts a prefix of what was sealed, in order and without replays. Failed opens never desynchronize the two sides. |

`tla/README.md` describes the TLA+ models, their TLC runs, and mutation checks
that confirm each property can catch a real bug.

## Findings

Each finding is fixed on its own branch off `main`.

1. **The AES-GCM plaintext limit is one byte too large.**
   * `plaintext_fits` accepts `2^36 - 31` bytes, RFC 5116's value, which
     erratum 5219 corrects to SP 800-38D's `2^36 - 32`.
   * mirage-crypto rejects that byte itself, so `Aead.seal` and
     `Sender.seal` return `Internal_error` where `hpke.mli` promises
     `Plaintext_too_long`. This was reproduced through the public API.
   * Lean: `AeadLimits.seal_contract_violated`, and `seal_contract_fixed` for
     the fix.
   * Branch `fix/aes-gcm-plaintext-limit`.
2. **The `hpke.for_testing` docs misstate the ML-KEM errors.**
   * The docs say that with an ML-KEM suite "these functions return
     `Invalid_private_key`". The Auth and AuthPSK functions return
     `Unsupported_mode`, even with keys of another KEM.
   * The code is right and already tested; the docs are wrong.
   * Lean: `Setup.withEphemeral_mlkem_suite`.
   * Branch `fix/for-testing-mlkem-docs`.
3. **An asynchronous exception can rewind the sequence number, and so reuse
   nonces.**
   * `increment` polls before each byte store. A signal handler that raises
     there, such as `Sys.Break` or a `SIGALRM` timeout, leaves `.. 00 ff` as
     `.. 00 00`.
   * If the caller survives the exception and keeps the context, the next
     seals reuse the nonces of the previous 255 messages, and a receiver
     accepts replays.
   * Evidence:
     * Lean: `Atomicity.increment_rolls_back_12`,
       `ContextAsync.shipped_reuses_nonce`.
     * TLC: `HpkeContext_async_incr.cfg`.
     * The arm64 code of OCaml 5.4.1.
     * A run of the real library that sealed duplicate ciphertexts.
   * The fix stores the carried byte first and clears the trailing bytes last.
     Lean proves that every intermediate state is at or above the new value
     (`Atomicity.fixed_never_below`) and that no nonce is ever reused
     (`ContextAsync.fixed_no_nonce_reuse`). TLC confirms it with asynchronous
     exceptions at every poll point (`HpkeContext_fix_seq_async_incr.cfg`,
     `HpkeContext_fixed_async.cfg`).
   * Branch `fix/sequence-async-exception`.
4. **An asynchronous exception can leave a context permanently busy.**
   * `with_busy` allocates between its compare-and-set and the handler
     `Fun.protect` installs. An exception at that poll point leaves `busy` set
     forever, and every later call returns `Concurrent_use`.
   * Safety holds; the context is unusable.
   * TLC: `HpkeContext_async_cas_stuck.cfg`, and
     `HpkeContext_async_release_stuck.cfg` for the backtrace allocation
     `Fun.protect` makes on its exception path before releasing.
   * The fix installs the handler directly after the compare-and-set and
     clears `busy` before anything allocates. TLC shows that `busy` is then
     always released (`HpkeContext_fix_busy_async.cfg`,
     `HpkeContext_fixed_async.cfg`).
   * Branch `fix/busy-async-exception`.

Also found, but not bugs:

* At the message limit the error can differ from the RFC pseudocode's
  (`Message_limit_reached` rather than the AEAD's error). The RFC's normative
  text only requires an error.
* `Eqaf.compare_be` orders strings of different lengths the opposite way to
  its documentation. hpke compares only equal lengths.
* `dh_decap` has an unreachable `Error error` branch.
* On 32-bit OCaml, concatenating inputs near the 16 MiB string limit would
  raise, but `curve448` already rules 32-bit out.

## Trusted base

The following are assumed, not proved:

* **Primitives.** The HKDF, AES-GCM, ChaCha20-Poly1305, SHAKE256, SHA3-256,
  ML-KEM and curve implementations of mirage-crypto, digestif, kdf, curve448
  and mlkem.
  * `Kem.lean` states what it needs as named hypotheses: DH commutativity
    (for the hybrids' nominal groups too), SHAKE256 and ciphertext lengths,
    canonical point encodings, FIPS 203 correctness, and parsers accepting
    what the serializers produce.
  * The AEAD is abstracted as INT-CTXT in `Channel` and the TLA+ models.
  * The mirage-crypto block-count checks are transcribed from its source, as
    are eqaf's `compare_be` and the NIST point checks. The conformance test
    exercises them where it can.
* **The mirrors.** They are hand-written transcriptions of the OCaml.
  `conformance/` checks them on concrete inputs, not symbolically.
  `Sys.max_string_length` and the placement of poll points (read from
  `ocamlopt -S` and `-dlinear` on OCaml 5.4.1, arm64) are also observations,
  not proofs.
* **The toolchain.** Lean's kernel, TLC, and the OCaml compiler.

Out of scope: `tools/` (the Python and Go scripts that regenerate test
vectors), `fuzz/`, and `website/`, which are not part of the library.

## Running

```sh
verification/check.sh
```

It needs elan with Lean 4.34.0, a JDK, and `tla2tools.jar`; set `JAVA` and
`TLA2TOOLS` to override the defaults. It builds the Lean proofs, rejects any
`sorry`, checks that `conformance/vectors.txt` is what the mirrors generate,
and runs every TLC configuration against its expected outcome. The
conformance test itself runs with the rest of the test suite:

```sh
dune runtest
```

After changing `lib/hpke.ml`, update the mirror it affects, then regenerate
the vectors:

```sh
cd verification/lean && lake env lean --run Conformance.lean > ../conformance/vectors.txt
```
