------------------------------ MODULE HpkeContext ------------------------------
(***************************************************************************)
(* The encryption context of lib/hpke.ml (module Rfc9180) as it executes   *)
(* on OCaml 5 domains: several domains call seal, open_ciphertext and      *)
(* export concurrently on ONE shared encryption_state. Each call is split  *)
(* into the atomic steps the OCaml code performs:                          *)
(*                                                                         *)
(*   with_busy (hpke.ml:937-940)                                           *)
(*     "cas"      Atomic.compare_and_set state.busy false true             *)
(*                (failure: return Error Concurrent_use, no cryptography)  *)
(*     "gap"      allocate the ~finally closure, enter Fun.protect         *)
(*                (an allocation, hence an OCaml 5 poll point, lies        *)
(*                between the CAS and the handler Fun.protect installs)    *)
(*   seal (942-953) / open_ciphertext (955-972), inside Fun.protect        *)
(*     "limit"    if sequence_exhausted state.sequence (916-921)           *)
(*                then Error Message_limit_reached                         *)
(*     "len"      plaintext_fits / ciphertext length checks                *)
(*     "nonce"    nonce state (931-935) reads state.sequence               *)
(*     "aead"     Aead.encrypt / Aead.decrypt (231-258): Ok, Error         *)
(*                (tag mismatch, or Invalid_argument caught), or an        *)
(*                exception that escapes                                   *)
(*     "incr"     increment_sequence (923-929), one byte per step: the     *)
(*                recursive `increment` has a poll point in its prologue   *)
(*   Fun.protect ~finally                                                  *)
(*     "finally"      Atomic.set state.busy false, then return             *)
(*     "finally_exn"  the same, then re-raise the exception                *)
(*                                                                         *)
(* Two constants select the fixed code instead of the shipped code:        *)
(*   IncrementOrder = "carry_first"  (branch fix/sequence-async-exception) *)
(*       `carry` finds the digit that absorbs the carry, reading only;     *)
(*       one store increments it ("incr_store"); Bytes.fill then clears    *)
(*       the trailing digits ("incr_fill"). An interruption can leave the  *)
(*       sequence ahead of the new value, never behind the old one.        *)
(*   BusyRelease = "direct"          (branch fix/busy-async-exception)     *)
(*       with_busy matches on operation () right after the CAS and        *)
(*       releases busy on both exits before anything allocates: there is  *)
(*       no "gap", and the exception path releases before any poll.       *)
(*   export (904-914)                                                      *)
(*     "export"   reads only the immutable exporter secret; touches        *)
(*                neither busy nor the sequence                            *)
(*                                                                         *)
(* The sequence is SeqWidth digits in base SeqBase, most significant       *)
(* first, exactly like the 12 big-endian bytes (base 256) of               *)
(* state.sequence. MaxSeq = SeqBase^SeqWidth - 1 plays (1 << 8*Nn) - 1.    *)
(*                                                                         *)
(* Ghost state: sealed/opened record the nonces of successful calls and    *)
(* lastEv the last observable result, both written at each call's          *)
(* linearization point. They feed the refinement mapping to               *)
(* Rfc9180Context (see Refinement below).                                  *)
(*                                                                         *)
(* Optional behaviours (all default off in HpkeContext.cfg):              *)
(*   AsyncExnAtCas        an asynchronous exception (Sys.Break from a      *)
(*                        signal handler, Out_of_memory, ...) delivered    *)
(*                        in "gap", i.e. after a successful CAS but before *)
(*                        Fun.protect guards the release                   *)
(*   AsyncExnInIncrement  an asynchronous exception delivered inside       *)
(*                        increment_sequence: at the poll in the prologue  *)
(*                        of `increment` (lsb_first), or, conservatively,  *)
(*                        before the store and between the digits cleared  *)
(*                        by Bytes.fill (carry_first)                      *)
(*   AsyncExnBeforeRelease  an exception raised on Fun.protect's exception *)
(*                        path before ~finally runs, where                 *)
(*                        Printexc.get_raw_backtrace allocates (shipped    *)
(*                        code only; "direct" releases first)              *)
(*   Mutation             a deliberately BROKEN variant of the code, used  *)
(*                        only to show that the properties have teeth:     *)
(*     "none"                 the code as written (default)                *)
(*     "no_cas"               no busy flag at all                          *)
(*     "incr_before_aead"     increment_sequence before the AEAD call      *)
(*     "check_after_incr"     exhaustion check after increment_sequence    *)
(*     "release_before_incr"  release busy, then increment_sequence        *)
(*     "no_fun_protect"       release busy only on normal return           *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Domains,              \* the OCaml domains sharing the context
    SeqBase,              \* 256 in the implementation
    SeqWidth,             \* Nn = 12 in the implementation
    Ops,                  \* the calls domains make: SUBSET {"seal","open","export"}
    AsyncExnAtCas,        \* BOOLEAN, see above
    AsyncExnInIncrement,  \* BOOLEAN, see above
    AsyncExnBeforeRelease, \* BOOLEAN, see above
    IncrementOrder,       \* "lsb_first" (shipped) or "carry_first" (fix)
    BusyRelease,          \* "fun_protect" (shipped) or "direct" (fix)
    RfcErrorOrder,        \* passed to Rfc9180Context
    Mutation              \* "none" unless demonstrating a broken variant

Mutations == {"none", "no_cas", "incr_before_aead", "check_after_incr",
              "release_before_incr", "no_fun_protect"}

ASSUME Domains # {}
ASSUME SeqBase \in Nat /\ SeqBase >= 2
ASSUME SeqWidth \in Nat /\ SeqWidth >= 1
ASSUME Ops \subseteq {"seal", "open", "export"} /\ Ops # {}
ASSUME AsyncExnAtCas \in BOOLEAN /\ AsyncExnInIncrement \in BOOLEAN
ASSUME AsyncExnBeforeRelease \in BOOLEAN
ASSUME IncrementOrder \in {"lsb_first", "carry_first"}
ASSUME BusyRelease \in {"fun_protect", "direct"}
ASSUME RfcErrorOrder \in BOOLEAN
ASSUME Mutation \in Mutations
\* The release_before_incr mutation is written for the shipped increment.
ASSUME Mutation = "release_before_incr" => IncrementOrder = "lsb_first"

MaxSeq == SeqBase ^ SeqWidth - 1

VARIABLES
    busy,    \* state.busy : bool Atomic.t
    digits,  \* state.sequence : bytes
    pc,      \* per domain: the next step of its current call
    op,      \* per domain: the call in progress
    input,   \* per domain: the call's argument, [pt |-> .., ct |-> ..]
    nonce,   \* per domain: the sequence value read by `nonce state`
    idx,     \* per domain: the `index` argument of `increment` (1-based);
             \* carry_first: the digit to store, then the digit to clear
    sealed,  \* ghost: nonces of successful seals
    opened,  \* ghost: nonces of successful opens
    lastEv   \* ghost: the last linearized result

vars == <<busy, digits, pc, op, input, nonce, idx, sealed, opened, lastEv>>

-----------------------------------------------------------------------------
(* Shared vocabulary with the abstract context. The definitions used here *)
(* do not mention its variables, so any expressions will do for them.     *)
R == INSTANCE Rfc9180Context
         WITH seq <- 0, sealed <- <<>>, opened <- <<>>, last <- 0

NoNonce   == R!NoNonce
Forged    == R!Forged
Malformed == R!Malformed
NoCt      == R!NoCt
NoPt      == R!NoPt
PtArgs    == R!PtArgs
CtArgs    == R!CtArgs
NoInput   == [pt |-> NoPt, ct |-> NoCt]

\* Results as the implementation returns them. The refinement mapping
\* translates them to the RFC's (AbsResult).
ImplResults ==
    {"none", "Ok", "MessageLimitReached", "PlaintextTooLong", "InternalError",
     "OpenError", "Exn", "AsyncExn", "ExportOk", "ExportError"}

AbsResult(r) ==
    CASE r \in {"PlaintextTooLong", "InternalError"} -> "SealError"
      [] r \in {"Exn", "AsyncExn"}                   -> "Exn"
      [] OTHER                                       -> r

-----------------------------------------------------------------------------
(* The byte sequence.                                                      *)

RECURSIVE ValueOf(_, _)
ValueOf(ds, i) == IF i = 0 THEN 0 ELSE ValueOf(ds, i - 1) * SeqBase + ds[i]

\* The sequence number that state.sequence currently encodes.
SeqNum == ValueOf(digits, SeqWidth)

\* sequence_exhausted: every byte is 0xff.
Exhausted == \A i \in 1 .. SeqWidth : digits[i] = SeqBase - 1

-----------------------------------------------------------------------------
(* Program counters.                                                       *)

\* Between a successful CAS and the release of busy.
CriticalPCs == {"gap", "limit", "len", "nonce", "aead", "incr", "incr_store",
                "incr_fill", "limit_after", "release", "finally", "finally_exn"}
InCritical(d) == pc[d] \in CriticalPCs

PCs == CriticalPCs \cup {"idle", "cas", "incr_unlocked", "export"}

\* A domain whose call has consumed its nonce but not yet reached its
\* linearization point: the abstract seq is still the nonce it read.
Pending(d) ==
    \/ pc[d] \in {"incr", "incr_store", "incr_fill", "incr_unlocked", "limit_after"}
    \/ Mutation = "incr_before_aead" /\ pc[d] = "aead"

-----------------------------------------------------------------------------
Init ==
    /\ busy = FALSE
    /\ digits = [i \in 1 .. SeqWidth |-> 0]
    /\ pc = [d \in Domains |-> "idle"]
    /\ op = [d \in Domains |-> "none"]
    /\ input = [d \in Domains |-> NoInput]
    /\ nonce = [d \in Domains |-> NoNonce]
    /\ idx = [d \in Domains |-> SeqWidth]
    /\ sealed = <<>>
    /\ opened = <<>>
    /\ lastEv = R!NoEvent

Goto(d, l) == pc' = [pc EXCEPT ![d] = l]

\* The first step of the body of seal / open_ciphertext.
BodyStart == IF Mutation = "check_after_incr" THEN "len" ELSE "limit"

\* Where a successful CAS leads: the shipped with_busy still has to enter
\* Fun.protect; the direct release has its handler in place already.
AfterCas == IF BusyRelease = "direct" THEN BodyStart ELSE "gap"

\* The call returns to its caller; the domain's locals are cleared.
Return(d) ==
    /\ pc' = [pc EXCEPT ![d] = "idle"]
    /\ op' = [op EXCEPT ![d] = "none"]
    /\ input' = [input EXCEPT ![d] = NoInput]
    /\ nonce' = [nonce EXCEPT ![d] = NoNonce]
    /\ idx' = [idx EXCEPT ![d] = SeqWidth]

\* The linearization point of a call: its result is decided.
Decide(d, r, n) == lastEv' = R!Ev(op[d], input[d].pt, input[d].ct, r, n)

RecordSuccess(d) ==
    IF op[d] = "seal"
    THEN sealed' = Append(sealed, nonce[d]) /\ UNCHANGED opened
    ELSE opened' = Append(opened, nonce[d]) /\ UNCHANGED sealed

\* The caller starts a call. This is the environment, so it has no fairness.
Invoke(d) ==
    /\ pc[d] = "idle"
    /\ \/ /\ "seal" \in Ops
          /\ \E p \in PtArgs : input' = [input EXCEPT ![d] = [pt |-> p, ct |-> NoCt]]
          /\ op' = [op EXCEPT ![d] = "seal"]
          /\ Goto(d, "cas")
       \/ /\ "open" \in Ops
          /\ \E c \in CtArgs : input' = [input EXCEPT ![d] = [pt |-> NoPt, ct |-> c]]
          /\ op' = [op EXCEPT ![d] = "open"]
          /\ Goto(d, "cas")
       \/ /\ "export" \in Ops
          /\ op' = [op EXCEPT ![d] = "export"]
          /\ Goto(d, "export")
          /\ UNCHANGED input
    /\ UNCHANGED <<busy, digits, nonce, idx, sealed, opened, lastEv>>

\* with_busy: if not (Atomic.compare_and_set state.busy false true)
\*            then Error Error.Concurrent_use else Fun.protect ...
\* (BusyRelease = "direct": ... else match operation () with ...)
Cas(d) ==
    /\ pc[d] = "cas"
    /\ IF Mutation = "no_cas"
       THEN Goto(d, AfterCas) /\ UNCHANGED <<busy, op, input, nonce, idx>>
       ELSE IF ~busy
       THEN busy' = TRUE /\ Goto(d, AfterCas) /\ UNCHANGED <<op, input, nonce, idx>>
       ELSE \* Concurrent_use: returns before any cryptography. The RFC has
            \* no such result; the abstract state does not change.
            Return(d) /\ UNCHANGED busy
    /\ UNCHANGED <<digits, sealed, opened, lastEv>>

\* From the CAS to the handler of Fun.protect (shipped code only).
Gap(d) ==
    /\ pc[d] = "gap"
    /\ \/ /\ Goto(d, BodyStart)
          /\ UNCHANGED <<op, input, nonce, idx, lastEv>>
       \/ \* An asynchronous exception escapes with_busy: nothing will ever
          \* run Atomic.set state.busy false.
          /\ AsyncExnAtCas
          /\ Decide(d, "AsyncExn", NoNonce)
          /\ Return(d)
    /\ UNCHANGED <<busy, digits, sealed, opened>>

\* if sequence_exhausted state.sequence then Error Message_limit_reached
Limit(d) ==
    /\ pc[d] = "limit"
    /\ IF Exhausted
       THEN Decide(d, "MessageLimitReached", NoNonce) /\ Goto(d, "finally")
       ELSE Goto(d, "len") /\ UNCHANGED lastEv
    /\ UNCHANGED <<busy, digits, op, input, nonce, idx, sealed, opened>>

\* seal: Aead.plaintext_fits; open: tag_size / plaintext_fits checks.
LengthCheck(d) ==
    /\ pc[d] = "len"
    /\ IF op[d] = "seal" /\ input[d].pt = "long"
       THEN Decide(d, "PlaintextTooLong", NoNonce) /\ Goto(d, "finally")
       ELSE IF op[d] = "open" /\ input[d].ct = Malformed
       THEN Decide(d, "OpenError", NoNonce) /\ Goto(d, "finally")
       ELSE Goto(d, "nonce") /\ UNCHANGED lastEv
    /\ UNCHANGED <<busy, digits, op, input, nonce, idx, sealed, opened>>

\* nonce state: base_nonce XOR state.sequence.
ReadNonce(d) ==
    /\ pc[d] = "nonce"
    /\ nonce' = [nonce EXCEPT ![d] = SeqNum]
    /\ idx' = [idx EXCEPT ![d] = SeqWidth]
    /\ Goto(d, IF Mutation = "incr_before_aead" THEN "incr" ELSE "aead")
    /\ UNCHANGED <<busy, digits, op, input, sealed, opened, lastEv>>

\* Aead.encrypt / Aead.decrypt under nonce[d].
Aead(d) ==
    LET authentic == op[d] = "seal" \/ input[d].ct = nonce[d]
        errorRes  == IF op[d] = "seal" THEN "InternalError" ELSE "OpenError"
    IN
    /\ pc[d] = "aead"
    /\ \/ \* Ok: the ciphertext (plaintext) is produced.
          /\ authentic
          /\ CASE Mutation = "incr_before_aead" ->
                    Decide(d, "Ok", nonce[d]) /\ RecordSuccess(d)
                    /\ Goto(d, "finally")
               [] Mutation = "release_before_incr" ->
                    Goto(d, "release") /\ UNCHANGED <<sealed, opened, lastEv>>
               [] OTHER ->
                    Goto(d, "incr") /\ UNCHANGED <<sealed, opened, lastEv>>
       \/ \* Error: tag mismatch, or Invalid_argument caught (seal:
          \* Internal_error, open: Open_error). let* skips the increment.
          /\ Decide(d, errorRes, NoNonce)
          /\ Goto(d, "finally")
          /\ UNCHANGED <<sealed, opened>>
       \/ \* Any other exception escapes to Fun.protect.
          /\ Decide(d, "Exn", NoNonce)
          /\ Goto(d, "finally_exn")
          /\ UNCHANGED <<sealed, opened>>
    /\ UNCHANGED <<busy, digits, op, input, nonce, idx>>

\* increment_sequence has returned: the call continues.
IncrDone(d) ==
    CASE Mutation = "incr_before_aead" ->
           Goto(d, "aead")
           /\ UNCHANGED <<op, input, nonce, idx, sealed, opened, lastEv>>
      [] Mutation = "check_after_incr" ->
           Goto(d, "limit_after")
           /\ UNCHANGED <<op, input, nonce, idx, sealed, opened, lastEv>>
      [] pc[d] = "incr_unlocked" ->
           Decide(d, "Ok", nonce[d]) /\ RecordSuccess(d) /\ Return(d)
      [] OTHER ->
           Decide(d, "Ok", nonce[d]) /\ RecordSuccess(d)
           /\ Goto(d, "finally")
           /\ UNCHANGED <<op, input, nonce, idx>>

\* A signal handler (or memprof/finaliser callback) raises inside
\* increment_sequence; the digits stay as they are.
IncrInterrupted(d) ==
    /\ AsyncExnInIncrement
    /\ pc[d] \in {"incr", "incr_store", "incr_fill"}
    /\ Decide(d, "AsyncExn", NoNonce)
    /\ Goto(d, "finally_exn")
    /\ UNCHANGED <<digits, op, input, nonce, idx, sealed, opened>>

\* IncrementOrder = "lsb_first" (shipped). One call of `increment index`
\* (idx[d] = index + 1), whose prologue polls:
\*   let value = Bytes.get_uint8 sequence index in
\*   Bytes.set_uint8 sequence index ((value + 1) land 0xff);
\*   if value = 0xff && index > 0 then increment (index - 1)
IncrLsbFirst(d) ==
    LET i == idx[d]
        v == digits[i]
    IN
    /\ IncrementOrder = "lsb_first"
    /\ pc[d] \in {"incr", "incr_unlocked"}
    /\ \/ IncrInterrupted(d)
       \/ /\ digits' = [digits EXCEPT ![i] = (v + 1) % SeqBase]
          /\ IF v = SeqBase - 1 /\ i > 1
             THEN \* Carry: the tail call increment (index - 1) comes next.
                  /\ idx' = [idx EXCEPT ![d] = i - 1]
                  /\ UNCHANGED <<pc, op, input, nonce, sealed, opened, lastEv>>
             ELSE IncrDone(d)
    /\ UNCHANGED busy

\* The index `carry` returns: the last digit below SeqBase - 1, or the
\* first digit if there is none.
CarryIndex ==
    LET below == {i \in 1 .. SeqWidth : digits[i] < SeqBase - 1}
    IN IF below = {} THEN 1 ELSE CHOOSE i \in below : \A j \in below : j <= i

\* IncrementOrder = "carry_first" (fix). `carry` only reads, so the scan is
\* one step; an exception during it (or during the closure allocation
\* before it) leaves the digits untouched.
\*   let rec carry index =
\*     if index = 0 || Bytes.get_uint8 sequence index < 0xff then index
\*     else carry (index - 1)
IncrCarryScan(d) ==
    /\ IncrementOrder = "carry_first"
    /\ pc[d] = "incr"
    /\ \/ IncrInterrupted(d)
       \/ /\ idx' = [idx EXCEPT ![d] = CarryIndex]
          /\ Goto(d, "incr_store")
          /\ UNCHANGED <<digits, op, input, nonce, sealed, opened, lastEv>>
    /\ UNCHANGED busy

\*   Bytes.set_uint8 sequence index ((Bytes.get_uint8 sequence index + 1) land 0xff)
\* The real code has no poll between the scan and this store, nor between
\* the store and Bytes.fill; the model allows an exception at both points.
IncrStore(d) ==
    LET k == idx[d] IN
    /\ pc[d] = "incr_store"
    /\ \/ IncrInterrupted(d)
       \/ /\ digits' = [digits EXCEPT ![k] = (digits[k] + 1) % SeqBase]
          /\ IF k = SeqWidth
             THEN IncrDone(d)
             ELSE /\ idx' = [idx EXCEPT ![d] = k + 1]
                  /\ Goto(d, "incr_fill")
                  /\ UNCHANGED <<op, input, nonce, sealed, opened, lastEv>>
    /\ UNCHANGED busy

\*   Bytes.fill sequence (index + 1) (Bytes.length sequence - index - 1) '\000'
\* is one noalloc C call. The model clears one digit per step and allows an
\* exception between them (conservative).
IncrFill(d) ==
    LET j == idx[d] IN
    /\ pc[d] = "incr_fill"
    /\ \/ IncrInterrupted(d)
       \/ /\ digits' = [digits EXCEPT ![j] = 0]
          /\ IF j = SeqWidth
             THEN IncrDone(d)
             ELSE /\ idx' = [idx EXCEPT ![d] = j + 1]
                  /\ UNCHANGED <<pc, op, input, nonce, sealed, opened, lastEv>>
    /\ UNCHANGED busy

Incr(d) == IncrLsbFirst(d) \/ IncrCarryScan(d) \/ IncrStore(d) \/ IncrFill(d)

\* MUTATION check_after_incr only: the exhaustion check runs on the
\* already incremented sequence.
LimitAfter(d) ==
    /\ pc[d] = "limit_after"
    /\ IF Exhausted
       THEN Decide(d, "MessageLimitReached", NoNonce) /\ UNCHANGED <<sealed, opened>>
       ELSE Decide(d, "Ok", nonce[d]) /\ RecordSuccess(d)
    /\ Goto(d, "finally")
    /\ UNCHANGED <<busy, digits, op, input, nonce, idx>>

\* MUTATION release_before_incr only: busy is released before the
\* sequence is incremented.
Release(d) ==
    /\ pc[d] = "release"
    /\ busy' = FALSE
    /\ Goto(d, "incr_unlocked")
    /\ UNCHANGED <<digits, op, input, nonce, idx, sealed, opened, lastEv>>

\* Fun.protect ~finally:(fun () -> Atomic.set state.busy false): runs on
\* normal return and on an exception (which it then re-raises).
\* BusyRelease = "direct": Atomic.set state.busy false on both exits of
\* the match, before anything allocates.
Finally(d) ==
    /\ pc[d] \in {"finally", "finally_exn"}
    /\ \/ /\ busy' = IF Mutation = "no_fun_protect" /\ pc[d] = "finally_exn"
                     THEN busy
                     ELSE FALSE
          /\ Return(d)
          /\ UNCHANGED <<digits, sealed, opened, lastEv>>
       \/ \* Shipped Fun.protect: `let work_bt = Printexc.get_raw_backtrace ()`
          \* allocates before ~finally runs. An exception there escapes with
          \* busy still set (the call's result stays an exception).
          /\ AsyncExnBeforeRelease
          /\ BusyRelease = "fun_protect"
          /\ pc[d] = "finally_exn"
          /\ Return(d)
          /\ UNCHANGED <<busy, digits, sealed, opened, lastEv>>

\* export: Labeled_kdf.expand on the exporter secret. No busy, no sequence.
ExportCall(d) ==
    /\ pc[d] = "export"
    /\ \E r \in {"ExportOk", "ExportError"} : Decide(d, r, NoNonce)
    /\ Return(d)
    /\ UNCHANGED <<busy, digits, sealed, opened>>

\* Everything a domain does once a call has started.
Step(d) ==
    \/ Cas(d) \/ Gap(d) \/ Limit(d) \/ LengthCheck(d) \/ ReadNonce(d) \/ Aead(d)
    \/ Incr(d) \/ LimitAfter(d) \/ Release(d) \/ Finally(d) \/ ExportCall(d)

Next == \E d \in Domains : Invoke(d) \/ Step(d)

Spec == Init /\ [][Next]_vars

\* Each domain keeps executing a call it has started (OCaml 5 domains are
\* preemptively scheduled system threads).
Fairness == \A d \in Domains : WF_vars(Step(d))

FairSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
(* Safety.                                                                 *)

TypeOK ==
    /\ busy \in BOOLEAN
    /\ digits \in [1 .. SeqWidth -> 0 .. SeqBase - 1]
    /\ pc \in [Domains -> PCs]
    /\ op \in [Domains -> {"none", "seal", "open", "export"}]
    /\ input \in [Domains -> [pt : PtArgs \cup {NoPt}, ct : CtArgs \cup {NoCt}]]
    /\ nonce \in [Domains -> 0 .. NoNonce]
    /\ idx \in [Domains -> 1 .. SeqWidth]
    /\ sealed \in Seq(0 .. MaxSeq)
    /\ opened \in Seq(0 .. MaxSeq)
    /\ lastEv \in [op : {"none", "seal", "open", "export"},
                   pt : PtArgs \cup {NoPt}, ct : CtArgs \cup {NoCt},
                   res : ImplResults, nonce : 0 .. NoNonce]

\* At most one domain between its successful CAS and its release of busy.
MutualExclusion ==
    \A d1, d2 \in Domains : d1 # d2 => ~(InCritical(d1) /\ InCritical(d2))

\* busy is set exactly while some domain is inside with_busy.
BusyIffOwner == busy <=> \E d \in Domains : InCritical(d)

\* The context is unusable: busy is set, but nobody will clear it.
Stuck == busy /\ \A d \in Domains : ~InCritical(d)
NotStuck == ~Stuck

Range(s) == {s[i] : i \in DOMAIN s}
Distinct(s) == \A i, j \in DOMAIN s : i # j => s[i] # s[j]

\* No two successful seals, and no two successful opens, use one nonce.
NoNonceReuse ==
    /\ Distinct(sealed)
    /\ Distinct(opened)
    /\ Range(sealed) \cap Range(opened) = {}

\* Outside an increment, the sequence counts the successful calls: it
\* never wraps and never skips.
SeqCountsSuccesses ==
    (\A d \in Domains : ~Pending(d)) => SeqNum = Len(sealed) + Len(opened)

\* The all-ones nonce is never released, and the AEAD is never even
\* invoked with it (stricter than the RFC pseudocode, whose Seal computes
\* and discards a ciphertext under it).
NeverUsesAllOnesNonce ==
    /\ MaxSeq \notin Range(sealed) \cup Range(opened)
    /\ \A d \in Domains : pc[d] = "aead" => nonce[d] # MaxSeq

\* Message_limit_reached is returned only when the sequence is exhausted.
LimitErrorOnlyAtLimit ==
    lastEv.res = "MessageLimitReached" => SeqNum = MaxSeq

-----------------------------------------------------------------------------
(* Refinement. The abstract seq is the sequence number, except while a     *)
(* domain is between consuming its nonce and its linearization point (in   *)
(* the middle of increment_sequence), when it is the nonce that domain     *)
(* read. Under MutualExclusion there is at most one such domain.           *)

SeqAbs ==
    IF \E d \in Domains : Pending(d)
    THEN nonce[CHOOSE d \in Domains : Pending(d)]
    ELSE SeqNum

Abs == INSTANCE Rfc9180Context
           WITH MaxSeq <- MaxSeq,
                RfcErrorOrder <- RfcErrorOrder,
                seq <- SeqAbs,
                sealed <- sealed,
                opened <- opened,
                last <- [lastEv EXCEPT !.res = AbsResult(lastEv.res)]

Refinement == Abs!Spec

SeqNeverDecreases == [][SeqAbs' >= SeqAbs]_vars

\* Every nonce already used lies below the next one (the abstract seq):
\* the sequence can never come back to a used nonce.
UsedNoncesBelowSeq == \A n \in Range(sealed) \cup Range(opened) : n < SeqAbs

\* The RFC context plus one transition for a call that an asynchronous
\* exception interrupts inside increment_sequence: the call fails, and seq
\* may move ahead by any amount (the nonces in between are burned, never
\* used), but never back. The carry-first increment refines this; the
\* shipped one does not, because it can move seq back.
BurnNonces ==
    /\ lastEv'.res = "AsyncExn"
    /\ SeqAbs' > SeqAbs
    /\ UNCHANGED <<sealed, opened>>

AbsVars == Abs!vars

RelaxedRefinement == Abs!Init /\ [][Abs!Next \/ BurnNonces]_AbsVars

-----------------------------------------------------------------------------
(* Liveness (check with FairSpec).                                         *)

\* Every started call returns (with a result or an exception).
CallsReturn == \A d \in Domains : pc[d] # "idle" ~> pc[d] = "idle"

\* busy is always eventually released.
BusyReleased == busy ~> ~busy

\* A domain inside a call can always take a step: nothing blocks.
NeverBlocked == [](\A d \in Domains : pc[d] # "idle" => ENABLED Step(d))

\* Once Stuck, always Stuck: every later seal/open fails the CAS.
StuckIsPermanent == [][Stuck => Stuck']_vars
=============================================================================
