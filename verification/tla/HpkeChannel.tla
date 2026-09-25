------------------------------ MODULE HpkeChannel ------------------------------
(***************************************************************************)
(* A sender context and a receiver context (RFC 9180, Section 5.2, as      *)
(* implemented by Rfc9180.Sender.seal / Rfc9180.Receiver.open_) connected  *)
(* by a network the adversary controls (Dolev-Yao at the level of          *)
(* ciphertext objects).                                                    *)
(*                                                                         *)
(* A ciphertext object is the triple [n, a, m] it was sealed from: nonce   *)
(* (as sequence number), aad and plaintext. The abstract AEAD is INT-CTXT: *)
(* the receiver accepts (aad, c) only if c is an exact copy of a           *)
(* ciphertext the sender released, sealed under the receiver's current     *)
(* nonce and the same aad. Anything else is rejected.                      *)
(*                                                                         *)
(* The adversary knows every ciphertext ever sent (`sent`) and may deliver *)
(* any of them, or any forgery, with any aad, any number of times, in any  *)
(* order, or never: this covers drop, duplication, reordering, replay,     *)
(* and injection. There is no separate queue.                              *)
(*                                                                         *)
(* Each context is used by one domain here: HpkeContext.tla shows that    *)
(* concurrent calls on one context linearize to these atomic steps.        *)
(* As in lib/hpke.ml, an open that fails leaves the receiver's seq alone.  *)
(*                                                                         *)
(* Mutation (default "none") switches in a deliberately BROKEN receiver:   *)
(*   "advance_on_failure"  a rejected open still advances the receiver     *)
(*   "ignore_aad"          the AEAD does not authenticate the aad          *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    MaxSeq,    \* (1 << (8*Nn)) - 1, abstracted
    AADs,      \* associated data values
    Msgs,      \* plaintext values
    Mutation

ASSUME MaxSeq \in Nat \ {0}
ASSUME Mutation \in {"none", "advance_on_failure", "ignore_aad"}

VARIABLES
    sSeq,     \* the sender context's seq
    rSeq,     \* the receiver context's seq
    sentLog,  \* ciphertexts released by the sender, in order
    recvLog   \* what the receiver's caller got: [n, a, m] per accepted open

vars == <<sSeq, rSeq, sentLog, recvLog>>

\* Every ciphertext object the adversary can present: the sender's, and
\* every forgery of the same shape.
CtObjs == [n : 0 .. MaxSeq, a : AADs, m : Msgs]

Range(s) == {s[i] : i \in DOMAIN s}

\* The adversary's knowledge: every ciphertext ever sent.
sent == Range(sentLog)

-----------------------------------------------------------------------------
Init ==
    /\ sSeq = 0
    /\ rSeq = 0
    /\ sentLog = <<>>
    /\ recvLog = <<>>

\* Rfc9180.Sender.seal ~aad ~plaintext. At the limit it returns
\* Message_limit_reached and changes nothing (a stuttering step, so it is
\* not written out); likewise for AEAD failures.
Seal(a, m) ==
    /\ sSeq < MaxSeq
    /\ sentLog' = Append(sentLog, [n |-> sSeq, a |-> a, m |-> m])
    /\ sSeq' = sSeq + 1
    /\ UNCHANGED <<rSeq, recvLog>>

\* The abstract AEAD Open under the receiver's current nonce.
Authentic(a, c) ==
    /\ c \in sent
    /\ c.n = rSeq
    /\ c.a = a \/ Mutation = "ignore_aad"

\* Rfc9180.Receiver.open_ ~aad ~ciphertext:c, as delivered by the adversary.
Deliver(a, c) ==
    /\ IF rSeq < MaxSeq /\ Authentic(a, c)
       THEN /\ rSeq' = rSeq + 1
            /\ recvLog' = Append(recvLog, [n |-> rSeq, a |-> a, m |-> c.m])
       ELSE \* Message_limit_reached or Open_error.
            /\ rSeq' = IF Mutation = "advance_on_failure" /\ rSeq < MaxSeq
                       THEN rSeq + 1
                       ELSE rSeq
            /\ UNCHANGED recvLog
    /\ UNCHANGED <<sSeq, sentLog>>

\* The honest network delivers the next ciphertext in order.
DeliverNext ==
    \E i \in DOMAIN sentLog :
        /\ i = Len(recvLog) + 1
        /\ Deliver(sentLog[i].a, sentLog[i])

Next ==
    \/ \E a \in AADs, m \in Msgs : Seal(a, m)
    \/ \E a \in AADs, c \in CtObjs : Deliver(a, c)

Spec == Init /\ [][Next]_vars

\* Only the in-order delivery is fair; the adversary's actions and the
\* sender are not.
FairSpec == Spec /\ WF_vars(DeliverNext)

-----------------------------------------------------------------------------
(* Properties.                                                             *)

TypeOK ==
    /\ sSeq \in 0 .. MaxSeq
    /\ rSeq \in 0 .. MaxSeq
    /\ sentLog \in Seq(CtObjs)
    /\ recvLog \in Seq(CtObjs)

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ \A i \in 1 .. Len(s) : s[i] = t[i]

\* The receiver's caller gets exactly the sender's messages, with their
\* aad, in order, without gaps or duplicates.
AcceptedIsPrefixOfSealed == IsPrefix(recvLog, sentLog)

RecvSeqLeSendSeq == rSeq <= sSeq

\* Each context's seq counts its successful calls.
SeqsCountSuccesses == sSeq = Len(sentLog) /\ rSeq = Len(recvLog)

\* After any number of failed opens, the next ciphertext in order is still
\* accepted.
NoDesync ==
    Len(recvLog) < Len(sentLog) =>
        LET c == sentLog[Len(recvLog) + 1] IN rSeq < MaxSeq /\ Authentic(c.a, c)

\* A failed open leaves the receiver as it was.
FailedOpenKeepsSeq == [][recvLog' = recvLog => rSeq' = rSeq]_vars

\* Under fair in-order delivery every sealed message is accepted,
\* whatever else the adversary does.
EventuallyAccepted ==
    \A k \in 1 .. MaxSeq : Len(sentLog) >= k ~> Len(recvLog) >= k
=============================================================================
