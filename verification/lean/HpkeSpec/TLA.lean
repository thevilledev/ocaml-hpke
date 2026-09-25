/-
A minimal embedding of TLA's safety fragment, used to state and prove the
state-machine properties of HPKE contexts for every parameter value (TLC checks
the matching `.tla` specifications only for small constants).

A specification is `Init ∧ □[Next]_vars`: an initial predicate and a next-state
relation, with stuttering allowed. An invariant holds in every reachable state,
and `Refinement I A f` is TLA's `I ⇒ A` under the refinement mapping `f`: every
step of `I` is a step of `A` or leaves the image of the state unchanged.
-/

namespace TLA

structure Spec (σ : Type) where
  init : σ → Prop
  next : σ → σ → Prop

variable {σ τ : Type}

inductive Reachable (S : Spec σ) : σ → Prop where
  | init {s : σ} : S.init s → Reachable S s
  | step {s t : σ} : Reachable S s → S.next s t → Reachable S t

/-- `S ⇒ □P`. -/
def Invariant (S : Spec σ) (P : σ → Prop) : Prop := ∀ s, Reachable S s → P s

/-- The standard proof rule: an inductive invariant that implies `P`. -/
theorem invariant_of_inductive (S : Spec σ) {P Inv : σ → Prop}
    (hInit : ∀ s, S.init s → Inv s)
    (hStep : ∀ s t, Inv s → S.next s t → Inv t)
    (hImp : ∀ s, Inv s → P s) : Invariant S P := by
  intro s hs
  apply hImp
  induction hs with
  | init h => exact hInit _ h
  | step _ hn ih => exact hStep _ _ ih hn

/-- An inductive invariant may use facts already known to be invariant. -/
theorem invariant_of_inductive_with (S : Spec σ) {P Q Inv : σ → Prop}
    (hQ : Invariant S Q)
    (hInit : ∀ s, S.init s → Inv s)
    (hStep : ∀ s t, Reachable S s → Q s → Inv s → S.next s t → Inv t)
    (hImp : ∀ s, Inv s → P s) : Invariant S P := by
  intro s hs
  apply hImp
  induction hs with
  | init h => exact hInit _ h
  | step hr hn ih => exact hStep _ _ hr (hQ _ hr) ih hn

theorem Invariant.and {S : Spec σ} {P Q : σ → Prop} (hP : Invariant S P)
    (hQ : Invariant S Q) : Invariant S (fun s => P s ∧ Q s) :=
  fun s hs => ⟨hP s hs, hQ s hs⟩

/-- A behaviour of `S`: an infinite sequence of states starting in `Init`
whose every step is a `Next` step or a stutter. -/
def IsBehavior (S : Spec σ) (b : Nat → σ) : Prop :=
  S.init (b 0) ∧ ∀ n, S.next (b n) (b (n + 1)) ∨ b (n + 1) = b n

theorem IsBehavior.reachable {S : Spec σ} {b : Nat → σ} (hb : IsBehavior S b) :
    ∀ n, Reachable S (b n) := by
  intro n
  induction n with
  | zero => exact .init hb.1
  | succ n ih =>
    rcases hb.2 n with h | h
    · exact .step ih h
    · rw [h]; exact ih

/-- `S ⇒ □P` on behaviours. -/
theorem Invariant.always {S : Spec σ} {P : σ → Prop} {b : Nat → σ}
    (hP : Invariant S P) (hb : IsBehavior S b) : ∀ n, P (b n) :=
  fun n => hP _ (hb.reachable n)

/-- `S ⇒ □[A]_v` for an action `A`: every step of every behaviour. -/
def ActionInvariant (S : Spec σ) (A : σ → σ → Prop) : Prop :=
  ∀ s t, Reachable S s → S.next s t → A s t

/-- TLA refinement under a mapping (stuttering-insensitive). -/
structure Refinement (I : Spec σ) (A : Spec τ) (f : σ → τ) : Prop where
  init : ∀ s, I.init s → A.init (f s)
  step : ∀ s t, Reachable I s → I.next s t → A.next (f s) (f t) ∨ f t = f s

/-- A refinement maps every behaviour of `I` to a behaviour of `A`. -/
theorem Refinement.behavior {I : Spec σ} {A : Spec τ} {f : σ → τ}
    (hr : Refinement I A f) {b : Nat → σ} (hb : IsBehavior I b) :
    IsBehavior A (f ∘ b) := by
  refine ⟨hr.init _ hb.1, fun n => ?_⟩
  rcases hb.2 n with h | h
  · exact hr.step _ _ (hb.reachable n) h
  · right; simp [Function.comp, h]

/-- Invariants of the abstract specification transfer along a refinement. -/
theorem Refinement.invariant {I : Spec σ} {A : Spec τ} {f : σ → τ}
    (hr : Refinement I A f) {P : τ → Prop} (hP : Invariant A P) :
    Invariant I (fun s => P (f s)) := by
  intro s hs
  apply hP
  induction hs with
  | init h => exact .init (hr.init _ h)
  | @step s t hs hn ih =>
    rcases hr.step s t hs hn with h | h
    · exact .step ih h
    · rw [h]; exact ih

end TLA
