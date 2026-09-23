--------------------------- MODULE Rfc9180Context ---------------------------
(***************************************************************************)
(* Abstract RFC 9180 encryption context (Section 5.2), one atomic step per *)
(* call.                                                                   *)
(*                                                                         *)
(*   def ContextS.Seal(aad, pt):                                           *)
(*     ct = Seal(self.key, self.ComputeNonce(self.seq), aad, pt)           *)
(*     self.IncrementSeq()                                                 *)
(*     return ct                                                           *)
(*   def ContextR.Open(aad, ct):                                           *)
(*     pt = Open(self.key, self.ComputeNonce(self.seq), aad, ct)           *)
(*     if pt == OpenError: raise OpenError                                 *)
(*     self.IncrementSeq()                                                 *)
(*     return pt                                                           *)
(*   def Context<ROLE>.IncrementSeq():                                     *)
(*     if self.seq >= (1 << (8*Nn)) - 1: raise MessageLimitReachedError    *)
(*     self.seq += 1                                                       *)
(*                                                                         *)
(* The nonce is modelled by the sequence number it is computed from        *)
(* (ComputeNonce is injective in seq). MaxSeq stands for (1 << 8*Nn) - 1.  *)
(*                                                                         *)
(* The AEAD is abstract. Seal of a plaintext that "fits" may succeed; a    *)
(* "long" one (beyond the AEAD's plaintext limit) always fails. A          *)
(* ciphertext argument of Open is the sequence number it was sealed under  *)
(* (INT-CTXT: it authenticates only under that nonce), or Forged (valid    *)
(* length, authenticates under no nonce), or Malformed (fails the length   *)
(* check). The primitive may also fail internally, and any call may be    *)
(* aborted by an exception (e.g. Out_of_memory); neither changes the state.*)
(*                                                                         *)
(* The state records the history of nonces used by successful seals and    *)
(* opens and the last observable event, including its arguments, so that  *)
(* a refinement check compares the results an implementation returns.     *)
(*                                                                         *)
(* RfcErrorOrder = TRUE demands the exact error the pseudocode raises at   *)
(* seq = MaxSeq (the AEAD runs first, so a failing AEAD call reports its   *)
(* own error there, not MessageLimitReached). RfcErrorOrder = FALSE only   *)
(* demands what the RFC's prose demands: "If ContextS.Seal() or            *)
(* ContextR.Open() would cause the seq field to overflow, then the         *)
(* implementation MUST fail with an error."                                *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    MaxSeq,         \* (1 << (8 * Nn)) - 1, abstracted to a small number
    RfcErrorOrder   \* see above

ASSUME MaxSeq \in Nat \ {0}
ASSUME RfcErrorOrder \in BOOLEAN

VARIABLES
    seq,     \* the context's sequence number
    sealed,  \* nonces (as sequence numbers) of successful seals, in order
    opened,  \* nonces (as sequence numbers) of successful opens, in order
    last     \* the last observable event

vars == <<seq, sealed, opened, last>>

-----------------------------------------------------------------------------
(* Arguments, results and events. All "none" markers are numbers above    *)
(* MaxSeq so that they never equal a sequence number.                      *)

NoNonce   == MaxSeq + 1
Forged    == MaxSeq + 1          \* authenticates under no nonce
Malformed == MaxSeq + 2          \* rejected by the length check
NoCt      == MaxSeq + 3          \* the event is not an open
CtArgs    == 0 .. Malformed      \* a genuine ciphertext for some seq, or junk
PtArgs    == {"fits", "long"}
NoPt      == "-"                 \* the event is not a seal

Results == {"none", "Ok", "MessageLimitReached", "SealError", "OpenError",
            "Exn", "ExportOk", "ExportError"}

Ev(o, p, c, r, n) == [op |-> o, pt |-> p, ct |-> c, res |-> r, nonce |-> n]

NoEvent == Ev("none", NoPt, NoCt, "none", NoNonce)

Events ==
    [op : {"none", "seal", "open", "export"}, pt : PtArgs \cup {NoPt},
     ct : CtArgs \cup {NoCt}, res : Results, nonce : 0 .. NoNonce]

\* INT-CTXT: a ciphertext authenticates under exactly the nonce it was
\* sealed with.
Accepts(ct) == ct = seq

-----------------------------------------------------------------------------
Init ==
    /\ seq = 0
    /\ sealed = <<>>
    /\ opened = <<>>
    /\ last = NoEvent

\* One ContextS.Seal(aad, pt) call.
Seal(pt) ==
    LET Fail(r) == /\ last' = Ev("seal", pt, NoCt, r, NoNonce)
                   /\ UNCHANGED <<seq, sealed, opened>>
    IN
    \/ \* AEAD Seal succeeds and IncrementSeq does not raise.
       /\ pt = "fits"
       /\ seq < MaxSeq
       /\ seq' = seq + 1
       /\ sealed' = Append(sealed, seq)
       /\ last' = Ev("seal", pt, NoCt, "Ok", seq)
       /\ UNCHANGED opened
    \/ \* AEAD Seal succeeds, then IncrementSeq raises; ct is discarded.
       /\ seq = MaxSeq
       /\ pt = "fits" \/ ~RfcErrorOrder
       /\ Fail("MessageLimitReached")
    \/ \* AEAD Seal fails (plaintext too long, or an internal error).
       Fail("SealError")
    \/ \* An exception aborts the call.
       Fail("Exn")

\* One ContextR.Open(aad, ct) call.
Open(ct) ==
    LET Fail(r) == /\ last' = Ev("open", NoPt, ct, r, NoNonce)
                   /\ UNCHANGED <<seq, sealed, opened>>
    IN
    \/ \* AEAD Open succeeds and IncrementSeq does not raise.
       /\ Accepts(ct)
       /\ seq < MaxSeq
       /\ seq' = seq + 1
       /\ opened' = Append(opened, seq)
       /\ last' = Ev("open", NoPt, ct, "Ok", seq)
       /\ UNCHANGED sealed
    \/ \* AEAD Open succeeds, then IncrementSeq raises.
       /\ seq = MaxSeq
       /\ Accepts(ct) \/ ~RfcErrorOrder
       /\ Fail("MessageLimitReached")
    \/ \* AEAD Open fails: rejected ciphertext, or an internal error.
       \* Failure does not advance seq.
       Fail("OpenError")
    \/ Fail("Exn")

\* Context.Export(exporter_context, L) never touches seq.
Export ==
    /\ \E r \in {"ExportOk", "ExportError"} :
          last' = Ev("export", NoPt, NoCt, r, NoNonce)
    /\ UNCHANGED <<seq, sealed, opened>>

Next ==
    \/ \E pt \in PtArgs : Seal(pt)
    \/ \E ct \in CtArgs : Open(ct)
    \/ Export

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties of the abstract context (checked in Rfc9180Context.cfg).     *)

TypeOK ==
    /\ seq \in 0 .. MaxSeq
    /\ sealed \in Seq(0 .. MaxSeq)
    /\ opened \in Seq(0 .. MaxSeq)
    /\ last \in Events

Range(s) == {s[i] : i \in DOMAIN s}
Distinct(s) == \A i, j \in DOMAIN s : i # j => s[i] # s[j]

\* Every success consumed exactly one nonce, all distinct, and exactly the
\* nonces 0 .. seq-1 have been consumed: seq never wraps.
NoncesConsumedInOrder ==
    /\ Distinct(sealed) /\ Distinct(opened)
    /\ Range(sealed) \cap Range(opened) = {}
    /\ Range(sealed) \cup Range(opened) = 0 .. seq - 1
    /\ \A i \in 1 .. Len(sealed) - 1 : sealed[i] < sealed[i + 1]
    /\ \A i \in 1 .. Len(opened) - 1 : opened[i] < opened[i + 1]

\* The all-ones nonce is never released.
NeverUsesAllOnesNonce == MaxSeq \notin Range(sealed) \cup Range(opened)

\* MessageLimitReached only at the limit.
LimitErrorOnlyAtLimit == last.res = "MessageLimitReached" => seq = MaxSeq

\* At the limit, every Seal and Open fails.
FailsAtLimit == [][seq = MaxSeq => last'.res # "Ok"]_vars

\* Failures and exports never change seq; successes add exactly one.
FailureKeepsSeq ==
    [][IF last'.res = "Ok" THEN seq' = seq + 1 ELSE seq' = seq]_vars

SeqMonotone == [][seq' >= seq]_seq
=============================================================================
