/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.FiniteMarginalIdentification

/-!
# Stage 23: truncated hitting costs on the infinite trajectory law

Stage 22 identifies every finite post-initial marginal of the Ionescu--Tulcea
trajectory measure with the explicit Stage-15 finite trajectory measure.  This file
uses that equality to transport the already verified finite path-sum hitting-cost
identity into a genuine measure-theoretic statement on the infinite trajectory space.

The stage intentionally stops one step before defining the infinite first-hitting-time
random variable.  Its endpoint is the exact finite-horizon integral formula

`lintegral truncatedCost (transitionTrajectoryMeasure ...) = ofReal finiteHorizonRuntime`.

This isolates all finite-dimensional integration and `ENNReal.ofReal` bookkeeping from
the later monotone-convergence argument.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-- The real-valued finite trajectory truncated hitting cost is always nonnegative. -/
theorem finiteTrajectoryTruncatedHittingCost_nonneg {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)] :
    ∀ t x (path : FiniteTrajectory α t),
      0 ≤ finiteTrajectoryTruncatedHittingCost target t x path := by
  intro t
  induction t with
  | zero =>
      intro x path
      simp [finiteTrajectoryTruncatedHittingCost]
  | succ t ih =>
      intro x path
      by_cases hx : x ∈ target
      · simp [finiteTrajectoryTruncatedHittingCost, hx]
      · rw [finiteTrajectoryTruncatedHittingCost]
        rw [ite_eq_right hx]
        exact add_nonneg zero_le_one (ih (path 0) (Fin.tail path))

/-- `ENNReal` form of the explicit finite-trajectory truncated hitting cost. -/
def finiteTrajectoryTruncatedHittingCostENNReal {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (t : ℕ) (x : α) (path : FiniteTrajectory α t) : ENNReal :=
  ENNReal.ofReal (finiteTrajectoryTruncatedHittingCost target t x path)

/-- On the finite trajectory space, the truncated hitting-cost observable is measurable. -/
@[fun_prop] theorem measurable_finiteTrajectoryTruncatedHittingCostENNReal
    {α : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (t : ℕ) (x : α) :
    Measurable (finiteTrajectoryTruncatedHittingCostENNReal target t x) := by
  exact measurable_of_finite _

/-- Integrating the explicit truncated hitting cost against the Stage-18 finite
trajectory measure recovers the `ENNReal.ofReal` embedding of the Stage-15 finite
path-sum expectation. -/
theorem finiteTrajectoryMeasure_lintegral_truncatedHittingCost
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (t : ℕ) (x : α) :
    (∫⁻ path : FiniteTrajectory α t,
        finiteTrajectoryTruncatedHittingCostENNReal target t x path
      ∂finiteTrajectoryMeasure P hP t x) =
      ENNReal.ofReal (finiteTrajectoryExpectedHittingCost P target t x) := by
  classical
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [finiteTrajectoryMeasure_singleton P hP t x]
  have hterm :
      ∀ path ∈ (Finset.univ : Finset (FiniteTrajectory α t)),
        0 ≤ finiteTrajectoryWeight P t x path *
          finiteTrajectoryTruncatedHittingCost target t x path := by
    intro path _hpath
    exact mul_nonneg
      (finiteTrajectoryWeight_nonneg P hP t x path)
      (finiteTrajectoryTruncatedHittingCost_nonneg target t x path)
  calc
    (∑ path : FiniteTrajectory α t,
        finiteTrajectoryTruncatedHittingCostENNReal target t x path *
          ENNReal.ofReal (finiteTrajectoryWeight P t x path)) =
        ∑ path : FiniteTrajectory α t,
          ENNReal.ofReal
            (finiteTrajectoryWeight P t x path *
              finiteTrajectoryTruncatedHittingCost target t x path) := by
      apply Finset.sum_congr rfl
      intro path _hpath
      unfold finiteTrajectoryTruncatedHittingCostENNReal
      rw [mul_comm]
      rw [← ENNReal.ofReal_mul
        (finiteTrajectoryWeight_nonneg P hP t x path)]
    _ = ENNReal.ofReal
        (∑ path : FiniteTrajectory α t,
          finiteTrajectoryWeight P t x path *
            finiteTrajectoryTruncatedHittingCost target t x path) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg hterm
    _ = ENNReal.ofReal (finiteTrajectoryExpectedHittingCost P target t x) := by
      rfl

/-- Truncated hitting-cost observable on the infinite trajectory space, for the
trajectory law started from the supplied deterministic initial state `x`.

Only the first `t` post-initial coordinates are inspected.  Stage 24 can take the
pointwise supremum over `t` to obtain the extended first-hitting-time variable. -/
def transitionTrajectoryTruncatedHittingCost {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (x : α) (t : ℕ) (path : ℕ → α) : ENNReal :=
  finiteTrajectoryTruncatedHittingCostENNReal target t x
    (transitionTrajectoryTail t path)

/-- Every finite-horizon truncated hitting-cost observable on the infinite path
space is measurable because it factors through the finite tail projection. -/
@[fun_prop] theorem measurable_transitionTrajectoryTruncatedHittingCost
    {α : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (x : α) (t : ℕ) :
    Measurable (transitionTrajectoryTruncatedHittingCost target x t) := by
  exact
    (measurable_finiteTrajectoryTruncatedHittingCostENNReal target t x).comp
      (measurable_transitionTrajectoryTail (α := α) t)

/-- Stage-23 endpoint: under the actual Ionescu--Tulcea trajectory law, the
measure-theoretic expectation of the horizon-`t` truncated hitting cost is exactly
the existing Bellman finite-horizon runtime, embedded into `ENNReal`.

The proof is now short because Stage 22 identifies the finite tail marginal with the
explicit finite trajectory measure. -/
theorem transitionTrajectoryMeasure_lintegral_truncatedHittingCost
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (x : α) (t : ℕ) :
    (∫⁻ path : ℕ → α,
        transitionTrajectoryTruncatedHittingCost target x t path
      ∂transitionTrajectoryMeasure P hP x) =
      ENNReal.ofReal (finiteHorizonRuntime P target t x) := by
  have hcost :
      Measurable
        (finiteTrajectoryTruncatedHittingCostENNReal target t x) :=
    measurable_finiteTrajectoryTruncatedHittingCostENNReal target t x
  have htail :
      Measurable (transitionTrajectoryTail (α := α) t) :=
    measurable_transitionTrajectoryTail (α := α) t
  unfold transitionTrajectoryTruncatedHittingCost
  rw [← MeasureTheory.lintegral_map hcost htail]
  rw [transitionTrajectoryMeasure_map_tail_eq_finiteTrajectoryMeasure P hP x t]
  rw [finiteTrajectoryMeasure_lintegral_truncatedHittingCost P target hP t x]
  rw [finiteTrajectoryExpectedHittingCost_eq_finiteHorizonRuntime P target hP t x]

end ECRuntime
