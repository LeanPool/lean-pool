/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.LevelExitTail
public import LeanPool.ECRuntime.UnrestrictedRuntime

/-!
Exact constant-exit hitting times. Finite-horizon increments give the
survival tail-sum formula, whose geometric specialization has mean `1/q`.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ECRuntime

/-- The increment of truncated expected hitting time equals probability
of survival at the preceding time. No stochasticity is needed for this
algebraic finite recursion. -/
theorem candidate_finiteRuntime_increment_eq_survival
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun z => z ∈ target)] :
    ∀ t (x : α),
      finiteHorizonRuntime P target (t + 1) x =
        finiteHorizonRuntime P target t x +
          finiteLevelSurvival P targetᶜ t x := by
  classical
  intro t
  induction t with
  | zero =>
      intro x
      by_cases hx : x ∈ target
      · have hxc : x ∉ targetᶜ := by simpa using hx
        simp [finiteHorizonRuntime_succ_of_mem P target 0 x hx,
          finiteLevelSurvival_eq_zero_of_not_mem P targetᶜ 0 x hxc]
      · have hxc : x ∈ targetᶜ := by simpa using hx
        rw [finiteHorizonRuntime_succ_of_not_mem P target 0 x hx]
        simp [finiteHorizonRuntime_zero, finiteLevelSurvival_zero_of_mem
          P targetᶜ x hxc, expectedValueAfter]
  | succ t ih =>
      intro x
      by_cases hx : x ∈ target
      · have hxc : x ∉ targetᶜ := by simpa using hx
        simp [finiteHorizonRuntime_succ_of_mem P target _ x hx,
          finiteLevelSurvival_eq_zero_of_not_mem P targetᶜ (t + 1) x hxc]
      · have hxc : x ∈ targetᶜ := by simpa using hx
        rw [finiteHorizonRuntime_succ_of_not_mem P target (t + 1) x hx,
          finiteHorizonRuntime_succ_of_not_mem P target t x hx,
          finiteLevelSurvival_succ_of_mem P targetᶜ t x hxc]
        have hsplit :
            expectedValueAfter P (finiteHorizonRuntime P target (t + 1)) x =
              expectedValueAfter P (finiteHorizonRuntime P target t) x +
                expectedValueAfter P (finiteLevelSurvival P targetᶜ t) x := by
          calc
            expectedValueAfter P (finiteHorizonRuntime P target (t + 1)) x =
                expectedValueAfter P
                  (fun y => finiteHorizonRuntime P target t y +
                    finiteLevelSurvival P targetᶜ t y) x := by
                      unfold expectedValueAfter
                      apply Finset.sum_congr rfl
                      intro y _
                      rw [ih y]
            _ = _ := expectedValueAfter_add P _ _ x
        rw [hsplit]
        unfold expectedValueAfter
        ring

/-- The exact finite tail-sum formula. -/
theorem candidate_finiteRuntime_eq_sum_survival
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun z => z ∈ target)]
    (t : Nat) (x : α) :
    finiteHorizonRuntime P target t x =
      ∑ k ∈ Finset.range t, finiteLevelSurvival P targetᶜ k x := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
      rw [candidate_finiteRuntime_increment_eq_survival P target t x,
        ih, Finset.sum_range_succ]

/-- Expected runtime as the nonnegative survival tail `tsum`. -/
theorem candidate_runtimeSup_eq_survival_tsum
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun z => z ∈ target)]
    (hP : IsStochastic P) (x : α) :
    runtimeSup P target x =
      ∑' t : Nat, ENNReal.ofReal (finiteLevelSurvival P targetᶜ t x) := by
  classical
  unfold runtimeSup
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_congr
  intro t
  rw [candidate_finiteRuntime_eq_sum_survival P target t x]
  exact ENNReal.ofReal_sum_of_nonneg
    (fun k _ => finiteLevelSurvival_nonneg P targetᶜ hP k x)

/-- Exact unrestricted expected runtime for a constant geometric survival
law, not merely an upper bound. -/
theorem candidate_runtimeSup_eq_inv_of_geometric_survival
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun z => z ∈ target)]
    (hP : IsStochastic P) (q : Real) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (x : α)
    (hsurvival : ∀ t : Nat,
      finiteLevelSurvival P targetᶜ t x = (1 - q) ^ t) :
    runtimeSup P target x = ENNReal.ofReal q⁻¹ := by
  have hstay0 : 0 ≤ 1 - q := by linarith
  rw [candidate_runtimeSup_eq_survival_tsum P target hP x]
  calc
    (∑' t : Nat, ENNReal.ofReal (finiteLevelSurvival P targetᶜ t x)) =
        ∑' t : Nat, (ENNReal.ofReal (1 - q)) ^ t := by
          apply tsum_congr
          intro t
          rw [hsurvival t]
          exact ENNReal.ofReal_pow hstay0 t
    _ = (1 - ENNReal.ofReal (1 - q))⁻¹ :=
      ENNReal.tsum_geometric (ENNReal.ofReal (1 - q))
    _ = ENNReal.ofReal q⁻¹ := by
      have hsub : 1 - ENNReal.ofReal (1 - q) = ENNReal.ofReal q := by
        calc
          1 - ENNReal.ofReal (1 - q) =
              ENNReal.ofReal (1 : Real) - ENNReal.ofReal (1 - q) := by norm_num
          _ = ENNReal.ofReal ((1 : Real) - (1 - q)) := by
                exact (ENNReal.ofReal_sub (1 : Real) hstay0).symm
          _ = ENNReal.ofReal q := by congr 1; ring
      rw [hsub]
      exact (ENNReal.ofReal_inv_of_pos hq0).symm

/-- For a finite stochastic transition matrix, a target whose complement
has constant one-step exit probability q has exact geometric expected
hitting time, from every state outside the target. -/
theorem proposed_exactEscape_runtimeSup_of_constant_exit
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P)
    (q : Real) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hexit : ∀ y : α, y ∈ targetᶜ →
      finiteEventMass (P y) (fun z => z ∉ targetᶜ) = q)
    (x : α) (hx : x ∉ target) :
    runtimeSup P target x = ENNReal.ofReal q⁻¹ := by
  classical
  have hxc : x ∈ targetᶜ := by simpa using hx
  have hsurvival : ∀ t : Nat,
      finiteLevelSurvival P targetᶜ t x = (1 - q) ^ t := by
    intro t
    exact finiteLevelSurvival_eq_geometric_of_exact_exit_mass
      P targetᶜ hP q hexit t x hxc
  exact candidate_runtimeSup_eq_inv_of_geometric_survival
    P target hP q hq0 hq1 x hsurvival

end ECRuntime
