/-
An HPKE context shared by concurrent OCaml 5 domains, as a TLA-style
specification (`lib/hpke.ml`, `Rfc9180.with_busy`, `seal`, `open_ciphertext`,
lines 937-972).

Every call to `Sender.seal` or `Receiver.open_` is split into the atomic steps
the OCaml code performs on shared state:

1. `acquire`: `Atomic.compare_and_set busy false true`; on failure the call
   returns `Concurrent_use` at once;
2. `check`: `sequence_exhausted` and the length check, inside `Fun.protect`;
3. `crypto`: `nonce state` reads the sequence bytes and the AEAD runs; it can
   succeed, return an `Error`, or raise;
4. `increment`: `increment_sequence`, only after success;
5. `release`: `Atomic.set busy false`, the `~finally` of `Fun.protect`, which
   runs on every exit from steps 2-4.

`Export` reads only immutable fields and is omitted: it is a stutter step.

Proved for every set of domains and every counter width `n ≥ 1`:

* `mutual_exclusion`: at most one domain is between `acquire` and `release`;
* `no_nonce_reuse`: the nonces of successful operations are pairwise distinct;
  indeed they are exactly `ComputeNonce(0), ..., ComputeNonce(k-1)` in order;
* `never_max_nonce`: `ComputeNonce(2^(8n) - 1)` is never used, as RFC 9180
  requires (its `IncrementSeq` fails there);
* `refines_rfc`: the implementation refines RFC 9180's atomic context
  (`rfcContext`) under the mapping `seq ↦ OS2IP(seq)`.
-/

import HpkeSpec.Sequence
import HpkeSpec.TLA

namespace Hpke.Context

open TLA

/-- Where a domain is in its current call. -/
inductive Pc where
  | idle
  | check
  | crypto (nonce : Bytes)
  | increment (nonce : Bytes)
  | release
  deriving DecidableEq, Repr

/-- The domain holds `busy`: it is inside `Fun.protect`. -/
def Pc.owns : Pc → Prop
  | .idle => False
  | _ => True

structure State (D : Type) where
  pc : D → Pc
  busy : Bool
  seq : Bytes
  /-- History variable: the nonce of every successful operation, in order. -/
  used : List Bytes

variable {D : Type} [DecidableEq D]

/-- `Function.update`, which core Lean does not provide. -/
def upd (f : D → Pc) (d : D) (v : Pc) : D → Pc := fun e => if e = d then v else f e

@[simp] theorem upd_same (f : D → Pc) (d : D) (v : Pc) : upd f d v d = v := by simp [upd]

theorem upd_other (f : D → Pc) {d e : D} (v : Pc) (h : e ≠ d) : upd f d v e = f e := by
  simp [upd, h]

/-- The atomic steps of domain `d`. The nondeterminism of the outside world
(the length check, the AEAD's result, exceptions) is left free. -/
inductive Step (baseNonce : Bytes) : D → State D → State D → Prop where
  /-- `compare_and_set busy false true` succeeds. -/
  | acquire {s d} : s.pc d = .idle → s.busy = false →
      Step baseNonce d s { s with pc := upd s.pc d .check, busy := true }
  /-- `compare_and_set` fails: `Error Concurrent_use`, nothing else happens. -/
  | contend {s d} : s.pc d = .idle → s.busy = true → Step baseNonce d s s
  /-- `sequence_exhausted`: `Error Message_limit_reached`. -/
  | exhausted {s d} : s.pc d = .check → sequenceExhausted s.seq = true →
      Step baseNonce d s { s with pc := upd s.pc d .release }
  /-- The length check fails: `Plaintext_too_long` or `Open_error`. -/
  | tooLong {s d} : s.pc d = .check → sequenceExhausted s.seq = false →
      Step baseNonce d s { s with pc := upd s.pc d .release }
  /-- The checks pass; `nonce state` reads the sequence bytes. -/
  | readNonce {s d} : s.pc d = .check → sequenceExhausted s.seq = false →
      Step baseNonce d s { s with pc := upd s.pc d (.crypto (nonceOf baseNonce s.seq)) }
  /-- The AEAD succeeds. -/
  | cryptoOk {s d n} : s.pc d = .crypto n →
      Step baseNonce d s { s with pc := upd s.pc d (.increment n) }
  /-- The AEAD returns `Error` or raises: no increment. -/
  | cryptoFail {s d n} : s.pc d = .crypto n →
      Step baseNonce d s { s with pc := upd s.pc d .release }
  /-- `increment_sequence`; the operation's nonce enters the history. -/
  | increment {s d n} : s.pc d = .increment n →
      Step baseNonce d s { s with pc := upd s.pc d .release,
                                  seq := incrementSequence s.seq,
                                  used := s.used ++ [n] }
  /-- `~finally:(fun () -> Atomic.set busy false)`. -/
  | release {s d} : s.pc d = .release →
      Step baseNonce d s { s with pc := upd s.pc d .idle, busy := false }

/-- The implementation, for a context with `base_nonce` of length `n`. -/
def impl (D : Type) [DecidableEq D] (baseNonce : Bytes) : Spec (State D) where
  init s := (∀ d, s.pc d = .idle) ∧ s.busy = false ∧
    s.seq = i2osp 0 baseNonce.length ∧ s.used = []
  next s t := ∃ d, Step baseNonce d s t

/-! ## The inductive invariant -/

/-- The nonces RFC 9180 assigns to the first `k` messages. -/
def rfcNonces (baseNonce : Bytes) (k : Nat) : List Bytes :=
  (List.range k).map (computeNonce baseNonce)

structure Inv (baseNonce : Bytes) (s : State D) : Prop where
  len : s.seq.length = baseNonce.length
  bound : os2ip s.seq ≤ maxSeq baseNonce.length
  history : s.used = rfcNonces baseNonce (os2ip s.seq)
  busy_iff : s.busy = true ↔ ∃ d, (s.pc d).owns
  exclusive : ∀ d e, (s.pc d).owns → (s.pc e).owns → d = e
  pending : ∀ d n, (s.pc d = .crypto n ∨ s.pc d = .increment n) →
    n = computeNonce baseNonce (os2ip s.seq) ∧ os2ip s.seq < maxSeq baseNonce.length

private theorem owns_idle : ¬ Pc.owns .idle := id

private theorem maxSeq_lt (n : Nat) : maxSeq n < 256 ^ n := by
  unfold maxSeq; have : 0 < 256 ^ n := Nat.pow_pos (by decide); omega

private theorem seq_eq (baseNonce : Bytes) {s : Bytes} (h : s.length = baseNonce.length) :
    s = i2osp (os2ip s) baseNonce.length := by
  rw [← h, i2osp_os2ip]

theorem inv_init (baseNonce : Bytes) (s : State D) (h : (impl D baseNonce).init s) :
    Inv baseNonce s := by
  obtain ⟨hpc, hbusy, hseq, hused⟩ := h
  have h0 : os2ip s.seq = 0 := by rw [hseq, os2ip_i2osp]; simp
  refine ⟨by rw [hseq, length_i2osp], by rw [h0]; exact Nat.zero_le _,
    by rw [hused, h0]; rfl, ?_, ?_, ?_⟩
  · simp [hbusy, hpc, Pc.owns]
  · intro d e hd; simp [hpc, Pc.owns] at hd
  · intro d n hd; simp [hpc] at hd

/-- A step of domain `d` leaves every other domain's `pc` alone. -/
private theorem step_pc_other {baseNonce : Bytes} {d e : D} {s t : State D}
    (hs : Step baseNonce d s t) (he : e ≠ d) : t.pc e = s.pc e := by
  cases hs <;> first | rfl | exact upd_other _ _ he

theorem inv_step (baseNonce : Bytes) (hn : 0 < baseNonce.length) (s t : State D)
    (hi : Inv baseNonce s) (hs : (impl D baseNonce).next s t) : Inv baseNonce t := by
  obtain ⟨d, hs⟩ := hs
  have other : ∀ e, e ≠ d → t.pc e = s.pc e := fun e he => step_pc_other hs he
  -- The domain stepping owns the context in every step but `acquire`/`contend`.
  cases hs with
  | acquire hpc hbusy =>
    refine ⟨hi.len, hi.bound, hi.history, ?_, ?_, ?_⟩
    · simp only [true_iff]; exact ⟨d, by simp [Pc.owns]⟩
    · intro a b ha hb
      have none : ∀ e, ¬ (s.pc e).owns := fun e he => by
        have := hi.busy_iff.mpr ⟨e, he⟩; simp_all
      by_cases had : a = d <;> by_cases hbd : b = d
      · rw [had, hbd]
      · exact absurd (by rwa [other _ hbd] at hb) (none b)
      · exact absurd (by rwa [other _ had] at ha) (none a)
      · exact absurd (by rwa [other _ had] at ha) (none a)
    · intro e n he
      by_cases hed : e = d
      · subst hed; simp at he
      · rw [other _ hed] at he; exact hi.pending e n he
  | contend => exact hi
  | exhausted hpc hex =>
    refine ⟨hi.len, hi.bound, hi.history, ?_, ?_, ?_⟩
    · simp only
      rw [hi.busy_iff]
      constructor <;> rintro ⟨e, he⟩ <;> refine ⟨d, ?_⟩ <;> simp [Pc.owns]
      rw [hpc]; trivial
    · intro a b ha hb
      have hdo : (s.pc d).owns := by rw [hpc]; trivial
      apply hi.exclusive
      · by_cases had : a = d
        · rw [had]; exact hdo
        · rwa [other _ had] at ha
      · by_cases hbd : b = d
        · rw [hbd]; exact hdo
        · rwa [other _ hbd] at hb
    · intro e n he
      by_cases hed : e = d
      · subst hed; simp at he
      · rw [other _ hed] at he; exact hi.pending e n he
  | tooLong hpc hex =>
    refine ⟨hi.len, hi.bound, hi.history, ?_, ?_, ?_⟩
    · simp only
      rw [hi.busy_iff]
      constructor <;> rintro ⟨e, he⟩ <;> refine ⟨d, ?_⟩ <;> simp [Pc.owns]
      rw [hpc]; trivial
    · intro a b ha hb
      have hdo : (s.pc d).owns := by rw [hpc]; trivial
      apply hi.exclusive
      · by_cases had : a = d
        · rw [had]; exact hdo
        · rwa [other _ had] at ha
      · by_cases hbd : b = d
        · rw [hbd]; exact hdo
        · rwa [other _ hbd] at hb
    · intro e n he
      by_cases hed : e = d
      · subst hed; simp at he
      · rw [other _ hed] at he; exact hi.pending e n he
  | readNonce hpc hex =>
    refine ⟨hi.len, hi.bound, hi.history, ?_, ?_, ?_⟩
    · simp only
      rw [hi.busy_iff]
      constructor <;> rintro ⟨e, he⟩ <;> refine ⟨d, ?_⟩ <;> simp [Pc.owns]
      rw [hpc]; trivial
    · intro a b ha hb
      have hdo : (s.pc d).owns := by rw [hpc]; trivial
      apply hi.exclusive
      · by_cases had : a = d
        · rw [had]; exact hdo
        · rwa [other _ had] at ha
      · by_cases hbd : b = d
        · rw [hbd]; exact hdo
        · rwa [other _ hbd] at hb
    · intro e n he
      by_cases hed : e = d
      · subst hed
        simp only [upd_same, Pc.crypto.injEq, reduceCtorEq, or_false] at he
        subst he
        have hne : os2ip s.seq ≠ maxSeq baseNonce.length := by
          intro h; rw [← hi.len] at h
          have := (sequenceExhausted_iff s.seq).mpr h; simp_all
        show nonceOf baseNonce s.seq = computeNonce baseNonce (os2ip s.seq) ∧
          os2ip s.seq < maxSeq baseNonce.length
        refine ⟨?_, by have := hi.bound; omega⟩
        rw [nonceOf_eq_xorBytes _ _ hi.len.symm]
        unfold computeNonce
        rw [← hi.len, i2osp_os2ip]
      · rw [other _ hed] at he; exact hi.pending e n he
  | cryptoOk hpc =>
    refine ⟨hi.len, hi.bound, hi.history, ?_, ?_, ?_⟩
    · simp only
      rw [hi.busy_iff]
      constructor <;> rintro ⟨e, he⟩ <;> refine ⟨d, ?_⟩ <;> simp [Pc.owns]
      rw [hpc]; trivial
    · intro a b ha hb
      have hdo : (s.pc d).owns := by rw [hpc]; trivial
      apply hi.exclusive
      · by_cases had : a = d
        · rw [had]; exact hdo
        · rwa [other _ had] at ha
      · by_cases hbd : b = d
        · rw [hbd]; exact hdo
        · rwa [other _ hbd] at hb
    · intro e m he
      by_cases hed : e = d
      · subst hed
        simp only [upd_same, reduceCtorEq, Pc.increment.injEq, false_or] at he
        subst he
        exact hi.pending e _ (Or.inl hpc)
      · rw [other _ hed] at he; exact hi.pending e m he
  | cryptoFail hpc =>
    refine ⟨hi.len, hi.bound, hi.history, ?_, ?_, ?_⟩
    · simp only
      rw [hi.busy_iff]
      constructor <;> rintro ⟨e, he⟩ <;> refine ⟨d, ?_⟩ <;> simp [Pc.owns]
      rw [hpc]; trivial
    · intro a b ha hb
      have hdo : (s.pc d).owns := by rw [hpc]; trivial
      apply hi.exclusive
      · by_cases had : a = d
        · rw [had]; exact hdo
        · rwa [other _ had] at ha
      · by_cases hbd : b = d
        · rw [hbd]; exact hdo
        · rwa [other _ hbd] at hb
    · intro e m he
      by_cases hed : e = d
      · subst hed; simp at he
      · rw [other _ hed] at he; exact hi.pending e m he
  | @increment _ _ n hpc =>
    obtain ⟨hnonce, hlt⟩ := hi.pending d n (Or.inr hpc)
    have hsucc : os2ip (incrementSequence s.seq) = os2ip s.seq + 1 := by
      rw [os2ip_incrementSequence _ (by rw [hi.len]; exact hn), hi.len,
        Nat.mod_eq_of_lt (by have := maxSeq_lt baseNonce.length; omega)]
    refine ⟨by simp [length_incrementSequence, hi.len], by simp only; omega, ?_, ?_, ?_, ?_⟩
    · simp only
      rw [hsucc, hi.history, hnonce]
      simp [rfcNonces, List.range_succ]
    · simp only
      rw [hi.busy_iff]
      constructor <;> rintro ⟨e, he⟩ <;> refine ⟨d, ?_⟩ <;> simp [Pc.owns]
      rw [hpc]; trivial
    · intro a b ha hb
      have hdo : (s.pc d).owns := by rw [hpc]; trivial
      apply hi.exclusive
      · by_cases had : a = d
        · rw [had]; exact hdo
        · rwa [other _ had] at ha
      · by_cases hbd : b = d
        · rw [hbd]; exact hdo
        · rwa [other _ hbd] at hb
    · intro e m he
      by_cases hed : e = d
      · subst hed; simp at he
      · rw [other _ hed] at he
        -- `e` cannot be mid-operation: `d` owns the context.
        have heo : (s.pc e).owns := by rcases he with h | h <;> rw [h] <;> trivial
        have hdo : (s.pc d).owns := by rw [hpc]; trivial
        exact absurd (hi.exclusive e d heo hdo) hed
  | release hpc =>
    refine ⟨hi.len, hi.bound, hi.history, ?_, ?_, ?_⟩
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
    · intro e m he
      by_cases hed : e = d
      · subst hed; simp at he
      · rw [other _ hed] at he; exact hi.pending e m he

theorem invariant (baseNonce : Bytes) (hn : 0 < baseNonce.length) :
    Invariant (impl D baseNonce) (Inv baseNonce) :=
  invariant_of_inductive _ (inv_init baseNonce) (inv_step baseNonce hn) (fun _ h => h)

/-! ## Consequences -/

theorem mutual_exclusion (baseNonce : Bytes) (hn : 0 < baseNonce.length) :
    Invariant (impl D baseNonce)
      (fun s => ∀ d e, (s.pc d).owns → (s.pc e).owns → d = e) :=
  fun s hs => (invariant baseNonce hn s hs).exclusive

theorem rfcNonces_nodup (baseNonce : Bytes) (k : Nat) (hk : k ≤ 256 ^ baseNonce.length) :
    (rfcNonces baseNonce k).Nodup := by
  unfold rfcNonces List.Nodup
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ List.nodup_range
  intro a b ha hb hab heq
  simp only [List.mem_range] at ha hb
  exact hab (nonce_injective baseNonce (by omega) (by omega) heq)

/-- No nonce is ever used for two successful operations. -/
theorem no_nonce_reuse (baseNonce : Bytes) (hn : 0 < baseNonce.length) :
    Invariant (impl D baseNonce) (fun s => s.used.Nodup) := by
  intro s hs
  have hi := invariant baseNonce hn s hs
  rw [hi.history]
  apply rfcNonces_nodup
  have := hi.bound; have := maxSeq_lt baseNonce.length; omega

/-- The nonce of sequence number `2^(8n) - 1` is never used. -/
theorem never_max_nonce (baseNonce : Bytes) (hn : 0 < baseNonce.length) :
    Invariant (impl D baseNonce)
      (fun s => computeNonce baseNonce (maxSeq baseNonce.length) ∉ s.used) := by
  intro s hs
  have hi := invariant baseNonce hn s hs
  rw [hi.history]
  simp only [rfcNonces, List.mem_map, List.mem_range, not_exists, not_and]
  intro k hk heq
  have hb := hi.bound
  have hm := maxSeq_lt baseNonce.length
  have := nonce_injective baseNonce (by omega) hm heq
  omega

/-! ## Refinement of RFC 9180's context -/

/-- RFC 9180 Section 5.2 as an atomic specification: the sequence number and
the nonces of the operations that returned a result. `Seal` and a successful
`Open` compute the nonce of `seq` and, through `IncrementSeq`, fail with
`MessageLimitReachedError` at `seq = 2^(8n) - 1` without changing the state;
every failure is a stutter. -/
structure RfcState where
  seq : Nat
  used : List Bytes

def rfcContext (baseNonce : Bytes) : Spec RfcState where
  init a := a.seq = 0 ∧ a.used = []
  next a b := a.seq < maxSeq baseNonce.length ∧
    b = { seq := a.seq + 1, used := a.used ++ [computeNonce baseNonce a.seq] }

/-- The refinement mapping. -/
def abs (s : State D) : RfcState := { seq := os2ip s.seq, used := s.used }

theorem refines_rfc (baseNonce : Bytes) (hn : 0 < baseNonce.length) :
    Refinement (impl D baseNonce) (rfcContext baseNonce) abs where
  init s h := by
    obtain ⟨_, _, hseq, hused⟩ := h
    exact ⟨by simp [abs, hseq, os2ip_i2osp], hused⟩
  step s t hr hs := by
    have hi := invariant baseNonce hn s hr
    obtain ⟨d, hs⟩ := hs
    cases hs with
    | @increment _ _ n hpc =>
      left
      obtain ⟨hnonce, hlt⟩ := hi.pending d n (Or.inr hpc)
      refine ⟨hlt, ?_⟩
      simp only [abs, RfcState.mk.injEq]
      refine ⟨?_, by rw [hnonce]⟩
      rw [os2ip_incrementSequence _ (by rw [hi.len]; exact hn), hi.len,
        Nat.mod_eq_of_lt (by have := maxSeq_lt baseNonce.length; omega)]
    | _ => right; rfl

/-- An invariant of the RFC's context, transported to the implementation. -/
theorem rfc_seq_bound (baseNonce : Bytes) :
    Invariant (rfcContext baseNonce) (fun a => a.seq ≤ maxSeq baseNonce.length) := by
  refine invariant_of_inductive (rfcContext baseNonce)
    (Inv := fun a => a.seq ≤ maxSeq baseNonce.length) ?_ ?_ (fun _ h => h)
  · intro a h; rw [h.1]; exact Nat.zero_le _
  · intro a b _ h; rw [h.2]; exact h.1

theorem impl_seq_bound (baseNonce : Bytes) (hn : 0 < baseNonce.length) :
    Invariant (impl D baseNonce) (fun s => os2ip s.seq ≤ maxSeq baseNonce.length) :=
  (refines_rfc baseNonce hn).invariant (rfc_seq_bound baseNonce)

/-- The instance that ships: 12-byte nonces. -/
theorem shipped (baseNonce : Bytes) (h : baseNonce.length = 12) :
    Invariant (impl D baseNonce) (fun s => s.used.Nodup) ∧
    Refinement (impl D baseNonce) (rfcContext baseNonce) abs :=
  ⟨no_nonce_reuse baseNonce (by omega), refines_rfc baseNonce (by omega)⟩

end Hpke.Context
