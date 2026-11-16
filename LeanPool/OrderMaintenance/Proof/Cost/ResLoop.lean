/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.Count


/-!
# The reservation loop

`reservation reservationBudget` runs `reservationBudget` iterations. Without a job, it pops the
  fullest chunk and starts its
split, or stops when the queue is empty; with a job, it runs one job step.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- A bounded loop followed by a continuation that does nothing. -/
theorem loop_bind {β : Type} {F : Nat → β → CM (ForInStep β)} {K : β → CM Unit} {s : Core}
    {k : Nat} {b0 : β} (I : Nat → Core → Prop) (Q : Core → Prop) (h0 : I 0 s)
    (hF : ∀ x j b t, I j t → j < k → ∃ c t',
      ((F x b).run t = .ok (.yield c) t' ∧ I (j + 1) t') ∨
      ((F x b).run t = .ok (.done c) t' ∧ Q t'))
    (hK : ∀ a t, (K a).run t = .ok () t) :
    ∃ t', (forIn (List.range k) b0 F >>= K).run s = .ok () t' ∧ (I k t' ∨ Q t') := by
  obtain ⟨c, t', hr, hres⟩ := forIn_loop F I Q k hF (List.range k) 0 b0 s h0 (by simp)
  rw [run_bind, hr]
  exact ⟨t', hK c t', by simpa using hres⟩

/-- **The reservation loop**, given what each iteration does. `I j` holds after `j` iterations;
`Q` holds when the loop stopped at an empty queue. -/
theorem reservation_ok {s : Core} {k : Nat} (I : Nat → Core → Prop) (Q : Core → Prop)
    (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < k →
      (t.resJob = none → (t.pqHi = 0 ∧ Q t) ∨
        (t.pqHi ≠ 0 ∧ ∃ c t1 t2, pqPopMax.run t = .ok c t1 ∧ (splitChunkStart c).run t1 = .ok () t2 ∧
          I (j + 1) t2)) ∧
      (∀ job, t.resJob = some job → ∃ r t1, (jobStep job).run t = .ok r t1 ∧
        I (j + 1) { t1 with resJob := r })) :
    ∃ t', (reservation k).run s = .ok () t' ∧ (I k t' ∨ Q t') := by
  unfold reservation
  refine loop_bind I Q h0 ?_ ?_
  · intro _ j b t hI hj
    obtain ⟨hn, hs⟩ := hstep j t hI hj
    cases hjob : t.resJob with
    | none =>
      rcases hn hjob with ⟨h0, hQ⟩ | ⟨h0, c, t1, t2, hp, hsc, hI'⟩
      · refine ⟨(some (), ()), t, Or.inr ⟨?_, hQ⟩⟩
        simp only [run_get_bind, hjob]
        rw [run_bind, pqEmpty_run]
        dsimp only
        rw [ite_eq_left (by simp [h0])]
        rfl
      · refine ⟨(none, ()), t2, Or.inl ⟨?_, hI'⟩⟩
        simp only [run_get_bind, hjob]
        rw [run_bind, pqEmpty_run]
        dsimp only
        rw [ite_eq_right (by simpa using h0), run_bind, hp]
        dsimp only
        rw [run_bind, hsc]
        rfl
    | some job =>
      obtain ⟨r, t1, hj1, hI'⟩ := hs job hjob
      refine ⟨(none, ()), { t1 with resJob := r }, Or.inl ⟨?_, hI'⟩⟩
      simp only [run_get_bind, hjob]
      rw [run_bind, hj1]
      rfl
  · intro a t
    dsimp only
    split <;> rfl

end OrderMaintenance.Proof
