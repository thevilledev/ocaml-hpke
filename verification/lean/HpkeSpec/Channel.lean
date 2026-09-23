/-
A sender context and a receiver context over an adversarial network, as a
TLA-style specification.

The sender seals with its sequence number (`Rfc9180.seal`); the receiver opens
with its own (`Rfc9180.open_ciphertext`) and, as `hpke.mli` documents, does not
advance on failure. The network belongs to the adversary: it may drop,
duplicate, reorder, and inject forgeries. The AEAD is abstracted by integrity
of ciphertexts (INT-CTXT): a ciphertext opens under the nonce of sequence
number `r` and associated data `aad` only if it is a copy of what the sender
sealed at sequence number `r` with `aad`.

Proved for every message limit `M` (the shipped one is `maxSeq 12`):

* `accepted_in_order`: the plaintexts the receiver returns are, in order and
  without gaps or repeats, a prefix of the plaintexts the sender sealed;
* `no_replay`: a sealed message opens at most once;
* `in_sync`: after any number of failed opens, the next in-order ciphertext
  still opens.
-/

import HpkeSpec.TLA

namespace Hpke.Channel

open TLA

variable {Msg : Type}

/-- What travels on the network. `sealed q aad pt` stands for the ciphertext
the sender produced at sequence number `q`; anything else is a forgery. -/
inductive Ct (Msg : Type) where
  | sealed (seq : Nat) (aad : String) (pt : Msg)
  | forged (junk : Nat)

structure State (Msg : Type) where
  sseq : Nat
  rseq : Nat
  /-- History: the `(aad, plaintext)` the sender sealed, indexed by sequence
  number. -/
  sent : List (String × Msg)
  network : List (Ct Msg)
  /-- History: what the receiver returned, in order. -/
  accepted : List Msg

inductive Step (M : Nat) : State Msg → State Msg → Prop where
  /-- `Sender.seal` below the limit: nonce of `sseq`, then increment. -/
  | sealOk {s aad pt} : s.sseq < M →
      Step M s { s with sseq := s.sseq + 1,
                        sent := s.sent ++ [(aad, pt)],
                        network := s.network ++ [.sealed s.sseq aad pt] }
  /-- The adversary rewrites the network from what it has seen and forgeries:
  it cannot create a sealed ciphertext the sender did not produce. -/
  | adversary {s net} : (∀ c ∈ net, c ∈ s.network ∨ ∃ j, c = .forged j) →
      Step M s { s with network := net }
  /-- `Receiver.open_` succeeds: the ciphertext is the one sealed at `rseq`
  with the receiver's `aad`. -/
  | openOk {s q aad pt} : s.rseq < M → Ct.sealed q aad pt ∈ s.network → q = s.rseq →
      Step M s { s with rseq := s.rseq + 1, accepted := s.accepted ++ [pt] }
  -- Every failed open (wrong sequence number, wrong `aad`, forgery,
  -- exhaustion) and every failed seal leaves the state unchanged: a stutter.

def spec (Msg : Type) (M : Nat) : Spec (State Msg) where
  init s := s.sseq = 0 ∧ s.rseq = 0 ∧ s.sent = [] ∧ s.network = [] ∧ s.accepted = []
  next := Step M

structure Inv (s : State Msg) : Prop where
  sent_len : s.sent.length = s.sseq
  network_sound : ∀ q aad pt, Ct.sealed q aad pt ∈ s.network → s.sent[q]? = some (aad, pt)
  behind : s.rseq ≤ s.sseq
  in_order : s.accepted = (s.sent.map Prod.snd).take s.rseq

theorem inv_init {M : Nat} (s : State Msg) (h : (spec Msg M).init s) : Inv s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by simp [h3, h1], by simp [h4], by omega, by simp [h5, h2]⟩

theorem inv_step (M : Nat) (s t : State Msg) (hi : Inv s)
    (hs : (spec Msg M).next s t) : Inv t := by
  cases hs with
  | @sealOk aad pt hlt =>
    refine ⟨by simp [hi.sent_len], ?_, by simp only; have := hi.behind; omega, ?_⟩
    · intro q a p hm
      simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · have := hi.network_sound q a p hm
        have hq : q < s.sent.length := by
          rcases h : s.sent[q]? with _ | x
          · rw [h] at this; cases this
          · exact (List.getElem?_eq_some_iff.mp h).1
        simp only
        rw [List.getElem?_append_left hq, this]
      · cases hm
        simp [← hi.sent_len]
    · simp only [List.map_append]
      rw [List.take_append_of_le_length (by simp; have := hi.behind; have := hi.sent_len; omega)]
      exact hi.in_order
  | @adversary net hnet =>
    refine ⟨hi.sent_len, ?_, hi.behind, hi.in_order⟩
    intro q a p hm
    rcases hnet _ hm with h | ⟨j, h⟩
    · exact hi.network_sound q a p h
    · cases h
  | @openOk q aad pt hlt hmem hq =>
    have hsent := hi.network_sound q aad pt hmem
    have hql : q < s.sent.length := (List.getElem?_eq_some_iff.mp hsent).1
    refine ⟨hi.sent_len, hi.network_sound, ?_, ?_⟩
    · simp only; have := hi.sent_len; omega
    · simp only
      have hpt : (s.sent.map Prod.snd)[q]? = some pt := by
        simp [List.getElem?_map, hsent]
      rw [hi.in_order, ← hq, List.take_add_one, hpt]
      rfl

theorem invariant (M : Nat) : Invariant (spec Msg M) Inv :=
  invariant_of_inductive _ (inv_init (M := M)) (inv_step M) (fun _ h => h)

/-- What the receiver returns is, in order, what the sender sealed. -/
theorem accepted_in_order (M : Nat) :
    Invariant (spec Msg M)
      (fun s => s.accepted = (s.sent.map Prod.snd).take s.rseq ∧ s.rseq ≤ s.sseq) :=
  fun s hs => ⟨(invariant M s hs).in_order, (invariant M s hs).behind⟩

/-- A sealed message opens at most once: a successful open is always at the
receiver's current sequence number, which then strictly increases, so the
ciphertext of an already accepted sequence number never opens again. -/
theorem no_replay (M : Nat) (s t : State Msg) (hs : Step M s t)
    (hadv : t.rseq ≠ s.rseq) :
    t.rseq = s.rseq + 1 ∧ ∃ aad pt, Ct.sealed s.rseq aad pt ∈ s.network ∧
      t.accepted = s.accepted ++ [pt] := by
  cases hs with
  | sealOk => exact absurd rfl hadv
  | adversary => exact absurd rfl hadv
  | @openOk q aad pt _ hmem hq => subst hq; exact ⟨rfl, aad, pt, hmem, rfl⟩

/-- Failed opens do not desynchronise: the next in-order ciphertext opens. -/
theorem in_sync (M : Nat) (s : State Msg) (hr : Reachable (spec Msg M) s)
    (hlt : s.rseq < M) (hin : s.rseq < s.sseq)
    (hnet : ∀ aad pt, s.sent[s.rseq]? = some (aad, pt) →
      Ct.sealed s.rseq aad pt ∈ s.network) :
    ∃ t, Step M s t ∧ t.rseq = s.rseq + 1 := by
  have hi := invariant M s hr
  have hl : s.rseq < s.sent.length := by rw [hi.sent_len]; exact hin
  have hm := hnet s.sent[s.rseq].1 s.sent[s.rseq].2
    (by rw [List.getElem?_eq_getElem hl])
  exact ⟨_, .openOk hlt hm rfl, rfl⟩

end Hpke.Channel
