# TLA+ models of the RFC 9180 encryption context

These specifications model the stateful part of `lib/hpke.ml`: the sequence
number of an `Rfc9180` encryption context, the `busy` flag that guards it
against concurrent use from OCaml 5 domains, and a sender and receiver talking
over a hostile network. TLC checks all of them.

| File | What it models |
| --- | --- |
| `Rfc9180Context.tla` | The abstract RFC 9180 context (Section 5.2). Seal, Open and Export are each one atomic step. |
| `HpkeContext.tla` | The implementation as it runs on OCaml 5. Several domains call `seal`, `open_ciphertext` and `export` on one shared context, and each call is split into the atomic steps the OCaml code performs. The spec also contains the refinement mapping to `Rfc9180Context`. |
| `HpkeChannel.tla` | A sender context and a receiver context over a Dolev-Yao network. The adversary can drop, duplicate, reorder, replay and forge messages, and the AEAD is abstracted as INT-CTXT. |
| `*.cfg` | One file per TLC run. The header comment of each says what the run checks and whether it is expected to pass. |
| `check.sh` | Runs every configuration and compares each outcome with the expected one. |

## Rfc9180Context.tla

This spec models the RFC's pseudocode directly:
`ContextS.Seal`, `ContextR.Open`, `IncrementSeq`, and `Export`. The nonce is
represented by the sequence number it is computed from, and `MaxSeq` stands for
`(1 << 8*Nn) - 1`.

The call arguments are part of the model, so the error a call returns can be
checked:

* A plaintext is either `"fits"` or `"long"`.
* A ciphertext is either the sequence number it was sealed under, `Forged`, or
  `Malformed`. A ciphertext authenticates only under its own nonce.

The AEAD may also fail internally, and an exception may abort any call. Neither
changes the state.

The state holds `seq`, the history of nonces used by successful seals
(`sealed`) and opens (`opened`), and the last event (`last`: operation,
argument, result, nonce).

`RfcErrorOrder = TRUE` demands the exact error the pseudocode raises at
`seq = MaxSeq`. The pseudocode calls the AEAD before `IncrementSeq`, so there
the AEAD's own failure wins over `MessageLimitReached`. `RfcErrorOrder = FALSE`
demands only what the RFC's prose requires: the call MUST fail with an error.

The spec checks these properties:

* `NoncesConsumedInOrder`: successes consume exactly the nonces `0 .. seq-1`,
  in order and each once.
* `NeverUsesAllOnesNonce`
* `LimitErrorOnlyAtLimit`
* `FailsAtLimit`
* `FailureKeepsSeq`
* `SeqMonotone`

## HpkeContext.tla

This spec gives every step its own `pc` label. The table describes the shipped
code. The next section covers the fixed code, which two constants select.

| `pc` | OCaml code (`lib/hpke.ml`) |
| --- | --- |
| `cas` | `Atomic.compare_and_set state.busy false true` in `with_busy` (937-940). On failure the call returns `Error Concurrent_use` before any cryptography. |
| `gap` | The code between the CAS and the handler that `Fun.protect` installs. This covers allocating the `~finally` closure (940) and allocating `finally_no_exn` in `Stdlib.Fun.protect`. Both allocations are OCaml 5 poll points. |
| `limit` | `if sequence_exhausted state.sequence then Error Message_limit_reached` (944 / 957, 916-921) |
| `len` | `Aead.plaintext_fits` (946, 200-207) for seal. For open, the tag-size and `plaintext_fits` checks (959-966). |
| `nonce` | `nonce state` (931-935) reads `state.sequence`. |
| `aead` | `Aead.encrypt` / `Aead.decrypt` (231-258). The outcome is `Ok`, `Error` (a tag mismatch, or a caught `Invalid_argument` becoming `Internal_error` / `Open_error`), or an exception that escapes. |
| `incr` | `increment_sequence` (923-929). Each step is one call of the recursive `increment`, which handles one byte, so a carry takes several steps. |
| `finally`, `finally_exn` | `Fun.protect ~finally:(fun () -> Atomic.set state.busy false)`. This runs on a normal return and on an exception, which it then re-raises. |
| `export` | `export` (904-914). It touches neither `busy` nor the sequence. |

### Shipped code and fixed code

Two constants choose between the shipped code and the fixes for F1 and F2:

| Constant | Shipped | Fix | What the fix changes in the model |
| --- | --- | --- | --- |
| `IncrementOrder` | `"lsb_first"` | `"carry_first"` (branch `fix/sequence-async-exception`) | `incr` becomes one read-only scan: `carry` finds the digit that absorbs the carry. Next comes `incr_store`, the single store that increments that digit. Then `incr_fill` clears the trailing digits, which `Bytes.fill` does. |
| `BusyRelease` | `"fun_protect"` | `"direct"` (branch `fix/busy-async-exception`) | There is no `gap`: a successful CAS leads straight to `limit`. `finally` and `finally_exn` release `busy` before anything allocates. |

Every configuration that existed before the fixes sets `IncrementOrder =
"lsb_first"`, `BusyRelease = "fun_protect"` and `AsyncExnBeforeRelease = FALSE`.
Their runs are therefore unchanged, with the same states and the same results.

With the carry-first increment, an asynchronous exception can arrive at these
points in the model:

* during the scan, where `carry` polls on each call, or at the closure
  allocation before it;
* between the scan and the store;
* between the store and the fill;
* between two trailing digits.

The real code has no poll point after the scan. On OCaml 5.4.1 arm64, `-dlinear`
and the disassembly of `Bytes.fill` show none, and `Bytes.fill` clears all the
digits in one `noalloc` C call. The last three points are therefore
conservative. An interruption before the store leaves the sequence unchanged.
An interruption after it leaves the sequence at or above the new value. The
sequence may skip ahead, which burns nonces, but it never goes back.

The sequence is modelled as `SeqWidth` digits in base `SeqBase`, most
significant first, just as `state.sequence` is 12 big-endian bytes in base 256.
`MaxSeq = SeqBase^SeqWidth - 1`, and `sequence_exhausted` means every digit is
`SeqBase - 1`.

`Ops` restricts which calls domains make. The API's types already restrict a
`Sender.t` to `seal`/`export` and a `Receiver.t` to `open_`/`export`. The main
configurations let one context do all three, which is a superset of the
possible behaviours.

The model treats each access to the plain (non-atomic) `Bytes` sequence as an
atomic step. This is sound because every access happens while `busy` is held
(`MutualExclusion`). The `busy` CAS and `Atomic.set` then order successive
owners, so the program has no data race on the sequence, and OCaml 5's memory
model guarantees sequential consistency for data-race-free programs.

### Properties

| Name | Kind | Meaning |
| --- | --- | --- |
| `MutualExclusion` | invariant | At most one domain is between its successful CAS and its release. |
| `BusyIffOwner` | invariant | `busy` is set exactly while some domain is inside `with_busy`. |
| `NotStuck` | invariant | It never happens that `busy` is set while no domain is inside `with_busy`. |
| `NoNonceReuse` | invariant | Successful seals use pairwise distinct nonces, and so do successful opens. |
| `SeqCountsSuccesses` | invariant | Outside an increment, the sequence equals the number of successful calls, so it never wraps or skips. |
| `NeverUsesAllOnesNonce` | invariant | No success uses nonce `MaxSeq`, and the AEAD is never invoked with it. |
| `LimitErrorOnlyAtLimit` | invariant | `Message_limit_reached` is returned only when the sequence is exhausted. |
| `UsedNoncesBelowSeq` | invariant | Every nonce already used is below the abstract `seq`, so the sequence can never come back to one. |
| `Refinement` | property | `Spec => Abs!Spec`, where `Abs` is the refinement mapping below. |
| `RelaxedRefinement` | property | Refinement of the abstract context extended with `BurnNonces`: a call interrupted by an asynchronous exception fails and may move `seq` ahead by any amount, but never back. |
| `SeqNeverDecreases` | property | The abstract sequence number never goes down. |
| `CallsReturn` | liveness | Under weak fairness, `pc[d] # "idle" ~> pc[d] = "idle"`. |
| `BusyReleased` | liveness | `busy ~> ~busy` |
| `NeverBlocked` | property | Every domain inside a call has an enabled step. |
| `StuckIsPermanent` | property | `[][Stuck => Stuck']_vars` |

Weak fairness is `\A d : WF_vars(Step(d))`, where `Step(d)` covers every step of
a call after it starts. Starting a call (`Invoke`) belongs to the environment
and has no fairness.

### Refinement mapping

| Abstract | Implementation |
| --- | --- |
| `seq` | `SeqAbs`: normally the number `digits` encodes. While a domain has read its nonce but not reached its linearization point (`Pending`: in the middle of `increment_sequence`), it is the nonce that domain read. |
| `sealed`, `opened` | The ghost histories, appended at the linearization point |
| `last` | `lastEv`, with results renamed: `PlaintextTooLong` and `InternalError` become `SealError`, and `Exn` and `AsyncExn` become `Exn` |
| `MaxSeq` | `SeqBase^SeqWidth - 1` |

The linearization point is the step at which the result is decided:

* the failing `limit`, `len` or `aead` step;
* the last step of `increment_sequence` on success;
* the `export` step;
* the step that delivers an asynchronous exception, when that is enabled.

A `Concurrent_use` return changes no abstract state, so it maps to a
stuttering step.

### Optional behaviours

All of these default to off.

* `AsyncExnAtCas` lets an asynchronous exception (`Sys.Break` from a signal
  handler, `Out_of_memory`, a raising `Gc.Memprof` or `Gc.finalise` callback)
  arrive in `gap`.
* `AsyncExnInIncrement` lets one arrive inside `increment_sequence`. For
  `"lsb_first"`, that is the poll point in the prologue of `increment`. For
  `"carry_first"`, it is any of the points listed above.
* `AsyncExnBeforeRelease` lets an exception be raised on the exception path of
  the shipped `Fun.protect`, before `~finally` runs. At that point
  `Printexc.get_raw_backtrace` allocates the backtrace. That allocation is a C
  call. OCaml 5 does not run signal handlers or other asynchronous callbacks
  inside allocations made from C, so only an `Out_of_memory` from the
  allocation itself fits this window. Modelling any exception there is
  conservative. The direct release frees `busy` before it fetches the
  backtrace, so this flag has no effect on it.
* `Mutation` switches in deliberately broken variants: `no_cas`,
  `incr_before_aead`, `check_after_incr`, `release_before_incr` and
  `no_fun_protect`. These only show that the properties can catch real bugs;
  the default `"none"` is the code as written.

## HpkeChannel.tla

A ciphertext object is the triple `[n, a, m]` it was sealed from. The receiver
accepts `(aad, c)` only if all of these hold:

* `c` is an exact copy of a ciphertext the sender released;
* `c.n` equals the receiver's `seq`;
* `c.a = aad`.

This is INT-CTXT. The adversary knows every ciphertext ever sent and may deliver
any of them, or any forgery, with any aad, any number of times, in any order,
or never. That covers drops, duplicates, reordering, replay and injection. As
in the implementation, a failed open leaves the receiver's `seq` unchanged.
`DeliverNext` is the honest in-order delivery, and it is the only action with
fairness.

Each context is used by one domain here. `HpkeContext` shows that concurrent
calls linearize to these atomic steps.

The spec checks these properties:

* `AcceptedIsPrefixOfSealed`: the receiver's (seq, aad, plaintext) log is a
  prefix of the sender's, so messages arrive in order, with no gaps or
  duplicates.
* `RecvSeqLeSendSeq`
* `SeqsCountSuccesses`
* `NoDesync`: after any number of failures, the next in-order ciphertext is
  still accepted.
* `FailedOpenKeepsSeq`
* `EventuallyAccepted`: under fair in-order delivery, every sealed message is
  eventually accepted.

The mutation `advance_on_failure` makes a rejected open advance the receiver,
and `ignore_aad` makes the AEAD ignore the aad.

## Running

Requirements: Java and `tla2tools.jar`. These results were produced with
TLC 2.19.

```sh
JAVA=/opt/homebrew/opt/openjdk/bin/java
TLA=~/.local/share/tlaplus/tla2tools.jar
cd verification/tla

# parse
$JAVA -cp $TLA tla2sany.SANY Rfc9180Context.tla
$JAVA -cp $TLA tla2sany.SANY HpkeContext.tla
$JAVA -cp $TLA tla2sany.SANY HpkeChannel.tla

# one run: <cfg> with its module (Rfc9180Context, HpkeContext or HpkeChannel)
$JAVA -XX:+UseParallelGC -cp $TLA tlc2.TLC -workers auto \
  -metadir "${TMPDIR:-/tmp}/tlc-HpkeContext" \
  -config HpkeContext.cfg HpkeContext.tla

# everything, compared with the expected outcomes
JAVA=$JAVA TLA2TOOLS=$TLA ./check.sh
```

Deadlock checking stays on in every run: no run passes `-deadlock`. An idle
domain can always start a call, and the adversary can always deliver, so a
reported deadlock would mean a broken model. `-metadir` keeps TLC's state
files out of the repository.

## Results

These numbers come from TLC 2.19 with `-workers auto` on an Apple Silicon
laptop, while another TLC job was also running, so the times are only
indicative. States are distinct states. In every configuration, `SeqBase = 2`.

The rows for the fixed code (`HpkeContext_fix*`) come from a later run of the
whole suite, made under heavier load. In that run the other configurations
found the same numbers of states, and `HpkeContext_3dom` took 12 min.

### Runs expected to pass

| Config | Setup | What is checked | States | Time |
| --- | --- | --- | ---: | ---: |
| `Rfc9180Context.cfg` | `MaxSeq = 3`, `RfcErrorOrder = TRUE` | 4 invariants and 3 action properties | 301 | <1 s |
| `HpkeContext.cfg` | 2 domains, 2 digits (`MaxSeq = 3`), all ops, `FairSpec` | All 8 invariants, `Refinement`, `SeqNeverDecreases`, `CallsReturn`, `BusyReleased`, `NeverBlocked` and `StuckIsPermanent` | 151,220 | 17 s |
| `HpkeContext_3dom.cfg` | 3 domains, `MaxSeq = 3`, all ops, `FairSpec` | The same checks as `HpkeContext.cfg` | 2,164,800 | 5 min 52 s |
| `HpkeContext_wide.cfg` | 2 domains, 3 digits (`MaxSeq = 7`), all ops | All 8 invariants, `Refinement`, `SeqNeverDecreases` and `StuckIsPermanent` (no liveness) | 7,900,116 | 1 min 43 s |
| `HpkeContext_async_cas.cfg` | The `HpkeContext.cfg` setup plus `AsyncExnAtCas` | Every invariant except `BusyIffOwner` and `NotStuck`, plus `Refinement`, `SeqNeverDecreases`, `CallsReturn`, `NeverBlocked` and `StuckIsPermanent` | 166,220 | 14 s |
| `HpkeContext_fixed.cfg` | Both fixes, no asynchronous exceptions, otherwise as `HpkeContext.cfg` | Everything `HpkeContext.cfg` checks, plus `UsedNoncesBelowSeq` | 122,860 | 12 s |
| `HpkeContext_fixed_async.cfg` | Both fixes, with `AsyncExnAtCas`, `AsyncExnInIncrement` and `AsyncExnBeforeRelease`, 2 domains, `FairSpec` | `MutualExclusion`, `BusyIffOwner`, `NotStuck`, `NoNonceReuse`, `UsedNoncesBelowSeq`, `NeverUsesAllOnesNonce`, `LimitErrorOnlyAtLimit`, `RelaxedRefinement`, `SeqNeverDecreases`, `CallsReturn`, `BusyReleased`, `NeverBlocked` and `StuckIsPermanent` | 141,340 | 15 s |
| `HpkeContext_fixed_async_wide.cfg` | As `HpkeContext_fixed_async.cfg` with 3 digits (`MaxSeq = 7`), `Spec` | The same invariants, plus `RelaxedRefinement`, `SeqNeverDecreases` and `StuckIsPermanent` (no liveness) | 10,573,220 | 2 min 16 s |
| `HpkeContext_fix_seq_async_incr.cfg` | F1 fix only, with `AsyncExnInIncrement` and `Spec` | The same invariants, plus `RelaxedRefinement` and `SeqNeverDecreases`. Compare `HpkeContext_async_incr.cfg`. | 180,540 | 3 s |
| `HpkeContext_fix_busy_async.cfg` | F2 fix only, with `AsyncExnAtCas`, `AsyncExnBeforeRelease` and `FairSpec` | Everything `HpkeContext.cfg` checks, including the exact `Refinement`. Compare the two `*_stuck` runs. | 118,100 | 12 s |
| `HpkeChannel.cfg` | `MaxSeq = 5`, 2 aads, 3 messages, `FairSpec` | 5 invariants, `FailedOpenKeepsSeq` and `EventuallyAccepted` | 54,121 | 9 s |

### Runs expected to fail: findings and observations

| Config | Setup | Violated | Trace |
| --- | --- | --- | --- |
| `HpkeContext_rfc_order.cfg` | `RfcErrorOrder = TRUE` | `Refinement` | 33 states (F3) |
| `HpkeContext_async_cas_stuck.cfg` | `AsyncExnAtCas` | `BusyReleased` | Lasso of 10 states (F2) |
| `HpkeContext_async_incr.cfg` | `AsyncExnInIncrement`, seal | `NoNonceReuse` | 28 states (F1) |
| `HpkeContext_async_incr_open.cfg` | `AsyncExnInIncrement`, open | `NoNonceReuse` | 28 states (F1, replay) |
| `HpkeContext_async_incr_relaxed.cfg` | `AsyncExnInIncrement`, seal | `RelaxedRefinement` | 19 states. The torn increment moves `seq` from 1 back to 0, which even the relaxed spec forbids (F1). |
| `HpkeContext_async_release_stuck.cfg` | `AsyncExnBeforeRelease` | `BusyReleased` | Lasso of 15 states. The AEAD raises, and a second exception on `Fun.protect`'s exception path skips `~finally` (F2). |
| `HpkeContext_fixed_async_skips.cfg` | Both fixes, all asynchronous exceptions, seal | `SeqCountsSuccesses` | 19 states. At seq 1 the store makes the digits `<<1, 1>>`, and the fill is interrupted. `seq` jumps to 3 and nonce 2 is burned. This is expected: nonces are skipped, never reused. |

### Mutation checks

These use deliberately broken code, and each run must fail.

| Config | Broken variant | Violated | Trace |
| --- | --- | --- | --- |
| `HpkeContext_mut_no_cas.cfg` | No busy flag | `NoNonceReuse` | 18 states. Both domains read seq 0 and seal under nonce 0. |
| `HpkeContext_mut_incr_before_aead.cfg` | `increment_sequence` runs before the AEAD call | `Refinement` | 9 states. A forged open at seq 0 returns `Open_error` but moves seq to 1. |
| `HpkeContext_mut_check_after_incr.cfg` | The exhaustion check runs after the increment | `NeverUsesAllOnesNonce` | 34 states. The seal at seq 2 burns nonce 2 and returns `MessageLimitReached`, and the next seal runs the AEAD under nonce 3 = `MaxSeq`. Checked against `NoNonceReuse` instead, it gives `sealed = <<0, 1, 3, 0>>`: the sequence wraps and nonce 0 is reused. |
| `HpkeContext_mut_release_before_incr.cfg` | `busy` is released before the increment | `NoNonceReuse` | 20 states. A second domain acquires `busy` while the first is still incrementing, and both seal under nonce 0. |
| `HpkeContext_mut_no_fun_protect.cfg` | `busy` is released only on a normal return | `BusyReleased` | Lasso of 11 states. The AEAD raises, `busy` stays set, and every later CAS fails. |
| `HpkeChannel_mut_advance_on_failure.cfg` | A rejected open advances the receiver | `NoDesync` | 3 states |
| `HpkeChannel_mut_advance_on_failure_liveness.cfg` | The same | `EventuallyAccepted` | Lasso of 12 states. Forged deliveries push the receiver past message 1 forever. 558,252 states, 26 s. |
| `HpkeChannel_mut_ignore_aad.cfg` | The AEAD ignores the aad | `AcceptedIsPrefixOfSealed` | 3 states. Message 1, sealed with `a1`, is accepted with `a2`. |

TLC stops at the first violation, so the failing runs explore only part of the
state space. Each finishes in about 3 s or less, except where the table notes
otherwise.

## Findings

With `Mutation = "none"` and no asynchronous exceptions, every property
holds. In that setting:

* The busy flag gives mutual exclusion.
* No nonce is reused, and the sequence never wraps or skips.
* A failed call leaves the sequence unchanged.
* Every call returns, and `busy` is always eventually released.
* The implementation refines the abstract RFC 9180 context.

Composed over a hostile network, the receiver accepts exactly a prefix of the
sender's messages, and a failed open never desynchronizes the two sides.

The findings below concern asynchronous exceptions and the exact RFC error
codes.

### F1. An asynchronous exception can tear `increment_sequence` and rewind the sequence

This can lead to nonce reuse on a sender and replay acceptance on a receiver.

**Why it happens.** `increment` is a recursive function, and `ocamlopt` 5.4.1
places a poll point in its prologue (`-dlinear` shows `poll call`). When a
carry crosses a byte boundary, which happens once every 256 messages, byte `i`
has already been set to `0x00` when `increment (index - 1)` polls.

At a poll point, OCaml runs pending signal handlers and `Gc.Memprof` and
finaliser callbacks. If one of them raises, for example:

* `Sys.Break` after `Sys.catch_break true`,
* a raising `Unix.alarm` timeout handler,
* a raising `Gc.Memprof` or `Gc.finalise` callback,

then the exception leaves `increment` in the middle of the carry. `Fun.protect`
still releases `busy`, but `state.sequence` is left at `..XX 00` instead of
`..XX+1 00`, which is 255 lower. A longer carry chain can leave it lower still.

**Consequences.** Suppose the caller catches the exception and keeps using the
context:

* A sender re-uses the nonces of the previous 255 messages. For AES-GCM and
  ChaCha20-Poly1305 this reuses the keystream and exposes the authentication
  key.
* A receiver accepts replays of the previous 255 ciphertexts.

**TLC evidence.**

* `HpkeContext_async_incr.cfg` violates `NoNonceReuse`. In the trace:
  1. The first seal uses nonce 0.
  2. The second seal uses nonce 1, and its AEAD call succeeds.
  3. `increment` sets the low digit from 1 to 0 and carries.
  4. An `AsyncExn` arrives at the prologue poll.
  5. `finally_exn` releases `busy`. The digits are now `<<0, 0>>`.
  6. The next seal uses nonce 0 again, so `sealed = <<0, 0>>`.
* `HpkeContext_async_incr_open.cfg` shows the receiver accepting ciphertext 0
  twice (`opened = <<0, 0>>`).

**Empirical evidence.** These runs used scratch programs outside the
repository, compiled natively with OCaml 5.4.1:

* A verbatim copy of `increment_sequence` started from `0x..00ff`. A SIGALRM
  handler raised every 100 µs. In 3 s, 2,923 of 18,715 interrupted calls left
  the sequence at `0x..0000`.
* The real library was also tested: the installed `hpke` v0.2.0, whose context
  code (`sequence_exhausted` to `open_ciphertext`) is identical to this
  revision. The program sealed a fixed plaintext in a loop while a SIGALRM
  handler raised every 50 µs. In 20 s, 14,025 successful seals returned a
  ciphertext equal to an earlier one from the same context. The first was seal
  #8960, which matched seal #8705, 255 seals earlier.

**Fix: carry first** (branch `fix/sequence-async-exception`).

```ocaml
let increment_sequence sequence =
  let rec carry index =
    if index = 0 || Bytes.get_uint8 sequence index < 0xff then index
    else carry (index - 1)
  in
  let index = carry (Bytes.length sequence - 1) in
  Bytes.set_uint8 sequence index ((Bytes.get_uint8 sequence index + 1) land 0xff);
  Bytes.fill sequence (index + 1) (Bytes.length sequence - index - 1) '\000'
```

All the poll points come before the first write: the closure allocation and the
prologue of each `carry` call. After the scan there is one store, then
`Bytes.fill`, and neither has a poll point.

The model (`IncrementOrder = "carry_first"`) still allows an exception after
the store and between the cleared digits. Even then, an interrupted increment
leaves the sequence at or above the new value. TLC shows:

* `HpkeContext_fix_seq_async_incr.cfg` (the F1 fix alone) and
  `HpkeContext_fixed_async.cfg` (both fixes) pass these under
  `AsyncExnInIncrement`:
  * `NoNonceReuse`
  * `UsedNoncesBelowSeq`
  * `SeqNeverDecreases`
  * `RelaxedRefinement`

  Under the same flag, the shipped increment fails `NoNonceReuse`
  (`HpkeContext_async_incr.cfg`) and `RelaxedRefinement`
  (`HpkeContext_async_incr_relaxed.cfg`). `HpkeContext_fixed_async_wide.cfg`
  repeats the safety checks with carries that span two digits.
* Without asynchronous exceptions, the fix changes nothing observable.
  `HpkeContext_fixed.cfg` passes the exact `Refinement`, `SeqCountsSuccesses`
  and the liveness properties.
* In the model, an increment interrupted after its store burns nonces
  (`HpkeContext_fixed_async_skips.cfg`). If the carry crossed m trailing
  `0xff` bytes, the skip is 256^m - 1 nonces. Near the very end, the sequence
  can land on all-ones, and the context then reports `Message_limit_reached`
  early. Skipped nonces are never used.

  The real code has no poll point after the store, so this cannot happen
  there: an interrupted increment either never starts or completes.

### F2. An asynchronous exception between the CAS and `Fun.protect` leaves `busy` set forever

**Why it happens.** After a successful `Atomic.compare_and_set`, `with_busy`
allocates the `~finally` closure, and `Fun.protect` allocates `finally_no_exn`,
before its handler is in place. Both allocations are poll points.

**Consequences.** An asynchronous exception there escapes with `busy = true`,
and nothing ever resets it. From then on, every `seal` and `open_` on that
context returns `Concurrent_use`. `export` still works because it never looks
at `busy`.

Safety is not affected. `HpkeContext_async_cas.cfg` passes `NoNonceReuse`,
`Refinement`, `CallsReturn` and `StuckIsPermanent`.
`HpkeContext_async_cas_stuck.cfg` violates `BusyReleased`. Its lasso has one
domain take `AsyncExn` in `gap`, and from then on every CAS fails, forever.

**Empirical evidence.** In a verbatim copy of `with_busy` with an empty
operation, all 11,516 interrupted calls left `busy = true`. With the real
library, 4,355 contexts became permanently unusable in the 20 s run above.

The shipped `Fun.protect` has a second, narrower window. On its exception
path, `Printexc.get_raw_backtrace` allocates the backtrace before `~finally`
runs. The allocation is made from C, so signal handlers do not run there, but
an `Out_of_memory` can escape at that point with `busy` still set. The model
covers this window with `AsyncExnBeforeRelease`, and
`HpkeContext_async_release_stuck.cfg` fails `BusyReleased` in the same way.

**Fix: direct release** (branch `fix/busy-async-exception`).

```ocaml
let with_busy state operation =
  if not (Atomic.compare_and_set state.busy false true) then Error Error.Concurrent_use
  else match operation () with
    | result -> Atomic.set state.busy false; result
    | exception exn ->
        Atomic.set state.busy false;
        Printexc.raise_with_backtrace exn (Printexc.get_raw_backtrace ())
```

`-dlinear` shows `push trap` directly after the `noalloc` CAS. Both exits
release `busy` with a `noalloc` `caml_atomic_exchange_field` before anything
allocates. The backtrace is fetched only after the release.

In the model (`BusyRelease = "direct"`), a successful CAS leads straight into
the body, and both `finally` steps release first. TLC shows:

* `HpkeContext_fix_busy_async.cfg` (the F2 fix alone, with `AsyncExnAtCas` and
  `AsyncExnBeforeRelease`) passes `BusyReleased`, `NotStuck`, `BusyIffOwner`,
  the exact `Refinement` and the other checks of `HpkeContext.cfg`.
* `HpkeContext_fixed_async.cfg` passes the same liveness checks with both
  fixes and every asynchronous exception enabled.
* The shipped code fails `BusyReleased` under the same flags
  (`HpkeContext_async_cas_stuck.cfg` and `HpkeContext_async_release_stuck.cfg`).

Both fixes rely on where native code currently places poll points. OCaml has no
primitive for masking asynchronous exceptions.

### F3. At the message limit, the error differs from the RFC pseudocode

This deviation is benign and allowed by the RFC. At `seq = MaxSeq`, the
implementation checks `sequence_exhausted` first and returns
`Message_limit_reached`. The pseudocode runs the AEAD first, so it reports the
AEAD's failure:

* Opening a ciphertext that does not authenticate under nonce `MaxSeq`, for
  example a replay of message 0, gives `OpenError` in the RFC and
  `Message_limit_reached` here.
* Sealing a plaintext over the AEAD limit gives the AEAD's error in the RFC and
  `Message_limit_reached` here.

The RFC's normative text only requires that the call "MUST fail with an error",
which holds. Refinement passes with `RfcErrorOrder = FALSE` and fails with
`TRUE` (`HpkeContext_rfc_order.cfg`). In that trace, three seals succeed and a
seal of a `"long"` plaintext then returns `MessageLimitReached`. An open-only
variant of the configuration gives the same result for a replay of ciphertext 0.

### F4. The implementation never runs the AEAD under the all-ones nonce

This is stricter than the pseudocode. The RFC's Seal computes a ciphertext
under nonce `MaxSeq` and then discards it, and its Open decrypts under nonce
`MaxSeq`. The implementation refuses before calling the AEAD.

Both allow exactly `MaxSeq` messages, with nonces `0 .. MaxSeq-1`.
`NeverUsesAllOnesNonce` checks this. On open failure below the limit, the
implementation matches the RFC: `seq` is unchanged (`Refinement`,
`FailureKeepsSeq`, and `NoDesync` in the channel).

### Poll points that are harmless

Some other poll points inside `Fun.protect` do not cause problems:

* the loop in `sequence_exhausted`;
* `String.init` in `nonce`;
* the allocation of `Ok ciphertext` after the increment.

An exception at any of these releases `busy` and leaves the sequence either
unchanged or fully incremented. In the last case, the ciphertext is lost but
its nonce is burned. After `work ()` returns normally, `Fun.protect` reaches
`Atomic.set` without passing a poll point. Its exception path allocates the
raw backtrace first, as described under F2.

The poll-point analysis applies to native code (`ocamlopt` 5.4.1, arm64,
without flambda). Bytecode was not examined.

## Abstractions and limits

* The AEAD is abstract (INT-CTXT). Confidentiality and the key schedule are not
  modelled.
* The sequence is 2 or 3 binary digits instead of 12 bytes. The carry logic is
  the same as `increment_sequence`'s, byte for byte, for both the shipped and
  the carry-first code. The carry-first model allows more interruption points
  than the real code has.
* Safety, refinement and liveness were checked with two and three domains.
  Without liveness, three domains take 35 s.
* Calls that fail the CAS (`Concurrent_use`) are not in the abstract spec.
  They change no state.
