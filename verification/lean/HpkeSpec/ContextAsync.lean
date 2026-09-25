/-
The shared context of `Context.lean`, with asynchronous exceptions delivered
inside `increment_sequence`.

An OCaml signal handler runs at a poll point and may raise; `increment` polls
before each byte store (see `Atomicity.lean`). The exception unwinds through
`Fun.protect`, which releases the context: the call returns no ciphertext, and
the sequence keeps the bytes stored so far. `interrupt` is that step: the
sequence becomes any state the increment passes through (`stores seq`), and
the history of returned results does not change.

The specification is parameterised by the increment (`inc`) and its
intermediate states (`stores`):

* `shipped_reuses_nonce`: with the shipped `increment_sequence`, a reachable
  state of the 12-byte context has returned two ciphertexts under one nonce
  (one domain, 255 seals, one interrupted increment, one more seal);
* `fixed_no_nonce_reuse`: with the carry-first increment (`incrementFixed`),
  no reachable state ever has, for every counter width and set of domains.
-/

import HpkeSpec.Context
import HpkeSpec.Atomicity

namespace Hpke.ContextAsync

open TLA
open Hpke.Context (Pc State upd upd_same upd_other rfcNonces)

variable {D : Type} [DecidableEq D]

inductive Step (baseNonce : Bytes) (inc : Bytes → Bytes) (stores : Bytes → List Bytes) :
    D → State D → State D → Prop where
  | acquire {s d} : s.pc d = .idle → s.busy = false →
      Step baseNonce inc stores d s { s with pc := upd s.pc d .check, busy := true }
  | contend {s d} : s.pc d = .idle → s.busy = true → Step baseNonce inc stores d s s
  | exhausted {s d} : s.pc d = .check → sequenceExhausted s.seq = true →
      Step baseNonce inc stores d s { s with pc := upd s.pc d .release }
  | tooLong {s d} : s.pc d = .check → sequenceExhausted s.seq = false →
      Step baseNonce inc stores d s { s with pc := upd s.pc d .release }
  | readNonce {s d} : s.pc d = .check → sequenceExhausted s.seq = false →
      Step baseNonce inc stores d s { s with pc := upd s.pc d (.crypto (nonceOf baseNonce s.seq)) }
  | cryptoOk {s d n} : s.pc d = .crypto n →
      Step baseNonce inc stores d s { s with pc := upd s.pc d (.increment n) }
  | cryptoFail {s d n} : s.pc d = .crypto n →
      Step baseNonce inc stores d s { s with pc := upd s.pc d .release }
  | increment {s d n} : s.pc d = .increment n →
      Step baseNonce inc stores d s
        { s with pc := upd s.pc d .release, seq := inc s.seq, used := s.used ++ [n] }
  /-- An exception at a poll inside the increment, after the stores so far. -/
  | interrupt {s d n t} : s.pc d = .increment n → t ∈ s.seq :: stores s.seq →
      Step baseNonce inc stores d s { s with pc := upd s.pc d .release, seq := t }
  | release {s d} : s.pc d = .release →
      Step baseNonce inc stores d s { s with pc := upd s.pc d .idle, busy := false }

def spec (D : Type) [DecidableEq D] (baseNonce : Bytes) (inc : Bytes → Bytes)
    (stores : Bytes → List Bytes) : Spec (State D) where
  init s := (∀ d, s.pc d = .idle) ∧ s.busy = false ∧
    s.seq = i2osp 0 baseNonce.length ∧ s.used = []
  next s t := ∃ d, Step baseNonce inc stores d s t

/-! ## The shipped increment reuses a nonce -/

section Counterexample

/-- One domain. -/
abbrev D1 := Unit

def shipped (baseNonce : Bytes) : Spec (State D1) :=
  spec D1 baseNonce incrementSequence (fun s => incrementStores s (s.length - 1))

def idleAt (k : Nat) (used : List Bytes) : State D1 :=
  { pc := fun _ => .idle, busy := false, seq := i2osp k 12, used }

private theorem upd_unit (f : D1 → Pc) (v : Pc) : upd f () v = fun _ => v := by
  funext e; cases e; simp [upd]

private abbrev shippedStep (bn : Bytes) :=
  Step (D := D1) bn incrementSequence (fun s => incrementStores s (s.length - 1)) ()

private theorem reach {bn : Bytes} {s t t' : State D1} (hr : Reachable (shipped bn) s)
    (h : shippedStep bn s t) (e : t = t') : Reachable (shipped bn) t' :=
  e ▸ .step hr ⟨(), h⟩

private theorem not_exhausted (k : Nat) (hk : k + 1 < 256 ^ 12) :
    sequenceExhausted (i2osp k 12) = false := by
  cases h : sequenceExhausted (i2osp k 12) with
  | false => rfl
  | true =>
    have := (sequenceExhausted_i2osp k 12 (by omega)).mp h
    simp only [maxSeq] at this; omega

/-- A seal up to its increment: `acquire`, `readNonce`, `cryptoOk`. -/
private theorem seal_prefix (bn : Bytes) (hb : bn.length = 12) (k : Nat) (used : List Bytes)
    (hk : k + 1 < 256 ^ 12) (hr : Reachable (shipped bn) (idleAt k used)) :
    Reachable (shipped bn)
      { pc := fun _ => .increment (computeNonce bn k), busy := true, seq := i2osp k 12, used } := by
  have hnonce : nonceOf bn (i2osp k 12) = computeNonce bn k := by
    rw [← hb]; exact nonce_spec bn k
  have r1 := reach hr (Step.acquire (s := idleAt k used) rfl rfl) rfl
  have r2 := reach r1 (Step.readNonce (by simp [idleAt]) (not_exhausted k hk)) rfl
  exact reach r2 (Step.cryptoOk (n := nonceOf bn (i2osp k 12)) (by simp [idleAt]))
    (by simp [idleAt, upd_unit, hnonce])

/-- One successful seal. -/
private theorem seal_once (bn : Bytes) (hb : bn.length = 12) (k : Nat) (used : List Bytes)
    (hk : k + 1 < 256 ^ 12) (hr : Reachable (shipped bn) (idleAt k used)) :
    Reachable (shipped bn) (idleAt (k + 1) (used ++ [computeNonce bn k])) := by
  have r3 := seal_prefix bn hb k used hk hr
  have r4 := reach r3 (Step.increment rfl) rfl
  exact reach r4 (Step.release (by simp))
    (by simp [idleAt, upd_unit, incrementSequence_i2osp k 12 (by decide) hk])

private theorem seals (bn : Bytes) (hb : bn.length = 12) :
    ∀ k, k < 256 ^ 12 → Reachable (shipped bn) (idleAt k (rfcNonces bn k)) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact .init ⟨fun _ => rfl, rfl, by simp [idleAt, hb], rfl⟩
  | succ k ih =>
    intro hk
    have := seal_once bn hb k _ hk (ih (by omega))
    simpa [rfcNonces, List.range_succ] using this

/-- 255 seals, a seal whose increment is interrupted after its first store,
and one more seal: nonce `ComputeNonce(0)` has been returned twice. -/
theorem shipped_reuses_nonce (bn : Bytes) (hb : bn.length = 12) :
    ∃ s, Reachable (shipped bn) s ∧ ¬ s.used.Nodup := by
  have h255 := seals bn hb 255 (by decide)
  have r3 := seal_prefix bn hb 255 _ (by decide) h255
  -- The exception: after the first store the sequence reads 0.
  have r4 := reach r3 (Step.interrupt (t := i2osp 0 12) rfl
    (show i2osp 0 12 ∈ i2osp 255 12 :: incrementStores (i2osp 255 12) (12 - 1) by decide)) rfl
  have r5 : Reachable (shipped bn) (idleAt 0 (rfcNonces bn 255)) :=
    reach r4 (Step.release (by simp)) (by simp [idleAt, upd_unit])
  have r6 := seal_once bn hb 0 _ (by decide) r5
  refine ⟨_, r6, fun hnd => ?_⟩
  -- `ComputeNonce(0)` is the first nonce returned, and the last.
  have hmem : computeNonce bn 0 ∈ rfcNonces bn 255 := by
    simp only [rfcNonces, List.mem_map, List.mem_range]
    exact ⟨0, by decide, rfl⟩
  simp only [idleAt] at hnd
  rw [List.nodup_append] at hnd
  exact hnd.2.2 _ hmem _ (List.mem_singleton_self _) rfl

end Counterexample

/-! ## The fixed increment never reuses a nonce -/

def fixed (D : Type) [DecidableEq D] (baseNonce : Bytes) : Spec (State D) :=
  spec D baseNonce incrementFixed incrementFixedStores

/-- Returned nonces are those of strictly increasing sequence numbers, all
below the current one; with interrupts the numbers may have gaps. -/
structure Inv (baseNonce : Bytes) (s : State D) : Prop where
  len : s.seq.length = baseNonce.length
  history : ∃ qs : List Nat, s.used = qs.map (computeNonce baseNonce) ∧
    qs.Pairwise (· < ·) ∧ ∀ q ∈ qs, q < os2ip s.seq
  busy_iff : s.busy = true ↔ ∃ d, (s.pc d).owns
  exclusive : ∀ d e, (s.pc d).owns → (s.pc e).owns → d = e
  pending : ∀ d n, (s.pc d = .crypto n ∨ s.pc d = .increment n) →
    n = computeNonce baseNonce (os2ip s.seq) ∧ sequenceExhausted s.seq = false

private theorem step_pc_other {baseNonce : Bytes} {inc stores} {d e : D} {s t : State D}
    (hs : Step baseNonce inc stores d s t) (he : e ≠ d) : t.pc e = s.pc e := by
  cases hs <;> first | rfl | exact upd_other _ _ he

/-- The frame conditions every owning step shares. -/
private theorem owner_frame {baseNonce : Bytes} {s t : State D} {d : D} (hi : Inv baseNonce s)
    (other : ∀ e, e ≠ d → t.pc e = s.pc e) (hdo : (s.pc d).owns) (hbusy : t.busy = s.busy)
    (hto : (t.pc d).owns) :
    (t.busy = true ↔ ∃ d, (t.pc d).owns) ∧ (∀ a b, (t.pc a).owns → (t.pc b).owns → a = b) := by
  refine ⟨?_, ?_⟩
  · rw [hbusy, hi.busy_iff]
    exact ⟨fun _ => ⟨d, hto⟩, fun _ => ⟨d, hdo⟩⟩
  · intro a b ha hb
    apply hi.exclusive
    · by_cases had : a = d
      · rw [had]; exact hdo
      · rwa [other _ had] at ha
    · by_cases hbd : b = d
      · rw [hbd]; exact hdo
      · rwa [other _ hbd] at hb

private theorem nodup_of_increasing (baseNonce : Bytes) (qs : List Nat)
    (hinc : qs.Pairwise (· < ·)) (hlt : ∀ q ∈ qs, q < 256 ^ baseNonce.length) :
    (qs.map (computeNonce baseNonce)).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ hinc
  intro a b ha hb hab heq
  have := nonce_injective baseNonce (hlt a ha) (hlt b hb) heq
  omega

theorem inv_init (baseNonce : Bytes) (s : State D) (h : (fixed D baseNonce).init s) :
    Inv baseNonce s := by
  obtain ⟨hpc, hbusy, hseq, hused⟩ := h
  refine ⟨by rw [hseq, length_i2osp], ⟨[], by simp [hused], List.Pairwise.nil, by simp⟩,
    ?_, ?_, ?_⟩
  · simp [hbusy, hpc, Pc.owns]
  · intro d e hd; simp [hpc, Pc.owns] at hd
  · intro d n hd; simp [hpc] at hd

theorem inv_step (baseNonce : Bytes) (hn : 0 < baseNonce.length) (s t : State D)
    (hi : Inv baseNonce s) (hs : (fixed D baseNonce).next s t) : Inv baseNonce t := by
  obtain ⟨d, hs⟩ := hs
  have other : ∀ e, e ≠ d → t.pc e = s.pc e := fun e he => step_pc_other hs he
  have keep_pending : ∀ (t : State D), t.seq = s.seq → t.pc d = .release ∨ t.pc d = .idle ∨
      t.pc d = .check → (∀ e, e ≠ d → t.pc e = s.pc e) →
      ∀ e n, (t.pc e = .crypto n ∨ t.pc e = .increment n) →
        n = computeNonce baseNonce (os2ip t.seq) ∧ sequenceExhausted t.seq = false := by
    intro t hseq hd hother e n he
    by_cases hed : e = d
    · subst hed; rcases hd with h | h | h <;> rw [h] at he <;> simp at he
    · rw [hother e hed] at he; rw [hseq]; exact hi.pending e n he
  cases hs with
  | acquire hpc hbusy =>
    refine ⟨hi.len, hi.history, ?_, ?_, ?_⟩
    · simp only [true_iff]; exact ⟨d, by simp [Pc.owns]⟩
    · intro a b ha hb
      have none : ∀ e, ¬ (s.pc e).owns := fun e he => by
        have := hi.busy_iff.mpr ⟨e, he⟩; simp_all
      by_cases had : a = d <;> by_cases hbd : b = d
      · rw [had, hbd]
      · exact absurd (by rwa [other _ hbd] at hb) (none b)
      · exact absurd (by rwa [other _ had] at ha) (none a)
      · exact absurd (by rwa [other _ had] at ha) (none a)
    · exact keep_pending _ rfl (by simp) other
  | contend => exact hi
  | exhausted hpc _ | tooLong hpc _ | cryptoFail hpc =>
    have hdo : (s.pc d).owns := by rw [hpc]; trivial
    obtain ⟨h1, h2⟩ := owner_frame hi other hdo rfl (by simp [Pc.owns])
    exact ⟨hi.len, hi.history, h1, h2, keep_pending _ rfl (by simp) other⟩
  | readNonce hpc hex =>
    have hdo : (s.pc d).owns := by rw [hpc]; trivial
    obtain ⟨h1, h2⟩ := owner_frame hi other hdo rfl (by simp [Pc.owns])
    refine ⟨hi.len, hi.history, h1, h2, ?_⟩
    intro e n he
    by_cases hed : e = d
    · subst hed
      simp only [upd_same, Pc.crypto.injEq, reduceCtorEq, or_false] at he
      subst he
      refine ⟨?_, hex⟩
      show nonceOf baseNonce s.seq = computeNonce baseNonce (os2ip s.seq)
      rw [nonceOf_eq_xorBytes _ _ hi.len.symm]
      unfold computeNonce
      rw [← hi.len, i2osp_os2ip]
    · rw [other _ hed] at he; exact hi.pending e n he
  | cryptoOk hpc =>
    have hdo : (s.pc d).owns := by rw [hpc]; trivial
    obtain ⟨h1, h2⟩ := owner_frame hi other hdo rfl (by simp [Pc.owns])
    refine ⟨hi.len, hi.history, h1, h2, ?_⟩
    intro e m he
    by_cases hed : e = d
    · subst hed
      simp only [upd_same, reduceCtorEq, Pc.increment.injEq, false_or] at he
      subst he
      exact hi.pending e _ (Or.inl hpc)
    · rw [other _ hed] at he; exact hi.pending e m he
  | @increment _ _ n hpc =>
    obtain ⟨hnonce, hne⟩ := hi.pending d n (Or.inr hpc)
    have hdo : (s.pc d).owns := by rw [hpc]; trivial
    obtain ⟨h1, h2⟩ := owner_frame hi other hdo rfl (by simp [Pc.owns])
    have hsucc := incrementFixed_spec s.seq (by rw [hi.len]; exact hn) hne
    have hlen : (incrementFixed s.seq).length = baseNonce.length := by
      have := incrementFixed_eq s.seq (by rw [hi.len]; exact hn) hne
      rw [this, length_incrementSequence, hi.len]
    obtain ⟨qs, hh, hinc, hbelow⟩ := hi.history
    refine ⟨hlen, ⟨qs ++ [os2ip s.seq], ?_, ?_, ?_⟩, h1, h2, ?_⟩
    · simp only; rw [hh, hnonce]; simp
    · rw [List.pairwise_append]
      refine ⟨hinc, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb; simp at hb; subst hb; exact hbelow a ha
    · intro q hq
      simp only [List.mem_append, List.mem_singleton] at hq
      simp only [hsucc]
      rcases hq with hq | hq
      · have := hbelow q hq; omega
      · omega
    · intro e m he
      by_cases hed : e = d
      · subst hed; simp at he
      · rw [other _ hed] at he
        have heo : (s.pc e).owns := by rcases he with h | h <;> rw [h] <;> trivial
        exact absurd (hi.exclusive e d heo hdo) hed
  | @interrupt _ _ n u hpc hu =>
    obtain ⟨_, hne⟩ := hi.pending d n (Or.inr hpc)
    have hdo : (s.pc d).owns := by rw [hpc]; trivial
    obtain ⟨h1, h2⟩ := owner_frame hi other hdo rfl (by simp [Pc.owns])
    -- Every state the interrupted increment can leave is at or above `seq`.
    have hge : os2ip s.seq ≤ os2ip u ∧ u.length = baseNonce.length := by
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨Nat.le_refl _, hi.len⟩
      · refine ⟨?_, ?_⟩
        · have := fixed_never_below s.seq (by rw [hi.len]; exact hn) hne u hu; omega
        · simp only [incrementFixedStores, List.mem_cons, List.not_mem_nil, or_false] at hu
          have := carryIndex_le s.seq (s.seq.length - 1)
          rcases hu with rfl | rfl <;> simp [List.length_take, hi.len] <;> omega
    obtain ⟨qs, hh, hinc, hbelow⟩ := hi.history
    refine ⟨hge.2, ⟨qs, hh, hinc, ?_⟩, h1, h2, ?_⟩
    · intro q hq; have := hbelow q hq; simp only; omega
    · intro e m he
      by_cases hed : e = d
      · subst hed; simp at he
      · rw [other _ hed] at he
        have heo : (s.pc e).owns := by rcases he with h | h <;> rw [h] <;> trivial
        exact absurd (hi.exclusive e d heo hdo) hed
  | release hpc =>
    refine ⟨hi.len, hi.history, ?_, ?_, ?_⟩
    · simp only [Bool.false_eq_true, false_iff, not_exists]
      intro e he
      by_cases hed : e = d
      · subst hed; simp [Pc.owns] at he
      · rw [upd_other _ _ hed] at he
        have hdo : (s.pc d).owns := by rw [hpc]; trivial
        exact hed (hi.exclusive e d he hdo)
    · intro a b ha hb
      by_cases had : a = d
      · subst had; simp [Pc.owns] at ha
      · by_cases hbd : b = d
        · subst hbd; simp [Pc.owns] at hb
        · rw [other _ had] at ha; rw [other _ hbd] at hb
          exact hi.exclusive a b ha hb
    · exact keep_pending _ rfl (by simp) other

/-- With the carry-first increment, asynchronous exceptions inside it never
lead to a nonce being returned twice. -/
theorem fixed_no_nonce_reuse (baseNonce : Bytes) (hn : 0 < baseNonce.length) :
    Invariant (fixed D baseNonce) (fun s => s.used.Nodup) := by
  refine invariant_of_inductive _ (inv_init baseNonce) (inv_step baseNonce hn) ?_
  intro s hi
  obtain ⟨qs, hh, hinc, hbelow⟩ := hi.history
  rw [hh]
  apply nodup_of_increasing _ _ hinc
  intro q hq
  have := hbelow q hq
  have := os2ip_lt s.seq
  rw [hi.len] at this
  omega

end Hpke.ContextAsync
