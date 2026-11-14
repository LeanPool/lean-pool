/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.TrajectoryTruncation
public import LeanPool.ECRuntime.UnrestrictedRuntime

/-!
# Stage 24: infinite hitting time and monotone convergence

Stage 23 proves that, for every finite horizon `t`, the lower Lebesgue integral of the
pathwise truncated hitting-cost observable under the Ionescu--Tulcea trajectory law is
exactly `ENNReal.ofReal (finiteHorizonRuntime ... t x)`.

This file closes the remaining monotone-convergence bridge.  The finite pathwise costs
are compatible under deletion of the last state and increase with the horizon.  Their
pointwise supremum therefore defines an extended nonnegative hitting-time observable on
the infinite trajectory space.  Mathlib's `lintegral_iSup` then identifies its
expectation with the existing Bellman quantity `runtimeSup`.

A later semantic lemma may characterize this supremum explicitly as the least target
hitting index (or `⊤` if the target is never reached).  That least-index representation
is deliberately separated from the expectation theorem proved here.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-- Deleting the final state of the first `t+1` post-initial coordinates of an infinite
trajectory gives exactly its first `t` post-initial coordinates. -/
@[simp] theorem transitionTrajectoryTail_init {α : Type*}
    (t : ℕ) (path : ℕ → α) :
    Fin.init (transitionTrajectoryTail (t + 1) path) =
      transitionTrajectoryTail t path := by
  funext j
  rfl

/-- Extending a finite trajectory by one additional state cannot decrease the real-valued
truncated hitting cost when the shorter observable ignores that final state. -/
theorem finiteTrajectoryTruncatedHittingCost_init_le {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)] :
    ∀ t x (path : FiniteTrajectory α (t + 1)),
      finiteTrajectoryTruncatedHittingCost target t x (Fin.init path) ≤
        finiteTrajectoryTruncatedHittingCost target (t + 1) x path := by
  intro t
  induction t with
  | zero =>
      intro x path
      simpa [finiteTrajectoryTruncatedHittingCost] using
        (finiteTrajectoryTruncatedHittingCost_nonneg target 1 x path)
  | succ t ih =>
      intro x path
      by_cases hx : x ∈ target
      · simp [finiteTrajectoryTruncatedHittingCost, hx]
      · have hhead :
            (Fin.init path) (0 : Fin (t + 1)) = path (0 : Fin (t + 2)) := by
          unfold Fin.init
          apply congrArg path
          apply Fin.ext
          rfl
        calc
          finiteTrajectoryTruncatedHittingCost target (t + 1) x (Fin.init path) =
              1 + finiteTrajectoryTruncatedHittingCost target t (path 0)
                (Fin.init (Fin.tail path)) := by
            simp only [finiteTrajectoryTruncatedHittingCost, hx, ite_false]
            rw [Fin.tail_init_eq_init_tail, hhead]
          _ ≤ 1 + finiteTrajectoryTruncatedHittingCost target (t + 1) (path 0)
                (Fin.tail path) := by
            simpa only [add_comm] using
              (add_le_add_left (ih (path 0) (Fin.tail path)) 1)
          _ = finiteTrajectoryTruncatedHittingCost target (t + 2) x path := by
            simp [finiteTrajectoryTruncatedHittingCost, hx]

/-- `ENNReal` form of the one-step monotonicity of finite truncated hitting costs. -/
theorem finiteTrajectoryTruncatedHittingCostENNReal_init_le {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (t : ℕ) (x : α) (path : FiniteTrajectory α (t + 1)) :
    finiteTrajectoryTruncatedHittingCostENNReal target t x (Fin.init path) ≤
      finiteTrajectoryTruncatedHittingCostENNReal target (t + 1) x path := by
  unfold finiteTrajectoryTruncatedHittingCostENNReal
  exact ENNReal.ofReal_le_ofReal
    (finiteTrajectoryTruncatedHittingCost_init_le target t x path)

/-- On every infinite trajectory, increasing the truncation horizon by one cannot
reduce the truncated hitting cost. -/
theorem transitionTrajectoryTruncatedHittingCost_le_succ {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (x : α) (t : ℕ) (path : ℕ → α) :
    transitionTrajectoryTruncatedHittingCost target x t path ≤
      transitionTrajectoryTruncatedHittingCost target x (t + 1) path := by
  unfold transitionTrajectoryTruncatedHittingCost
  rw [← transitionTrajectoryTail_init t path]
  exact finiteTrajectoryTruncatedHittingCostENNReal_init_le target t x
    (transitionTrajectoryTail (t + 1) path)

/-- The family of infinite-path truncated hitting costs is monotone in the horizon,
with the function-space order interpreted pointwise in the trajectory. -/
theorem transitionTrajectoryTruncatedHittingCost_monotone {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (x : α) :
    Monotone (fun t : ℕ => transitionTrajectoryTruncatedHittingCost target x t) := by
  apply monotone_nat_of_le_succ
  intro t path
  exact transitionTrajectoryTruncatedHittingCost_le_succ target x t path

/-- Extended pathwise hitting time obtained as the pointwise supremum of all finite
truncated hitting costs.  It takes values in `ENNReal`, so paths that never reach the
target may have value `⊤`. -/
noncomputable def transitionTrajectoryHittingTime {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (x : α) (path : ℕ → α) : ENNReal :=
  ⨆ t : ℕ, transitionTrajectoryTruncatedHittingCost target x t path

/-- The extended hitting-time observable is measurable as a countable supremum of the
Stage-23 measurable truncation observables. -/
@[fun_prop] theorem measurable_transitionTrajectoryHittingTime
    {α : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (x : α) :
    Measurable (transitionTrajectoryHittingTime target x) := by
  unfold transitionTrajectoryHittingTime
  exact Measurable.iSup
    (fun t => measurable_transitionTrajectoryTruncatedHittingCost target x t)

/-- Stage-24 endpoint and the main semantic bridge: the Bellman unrestricted runtime
supremum is exactly the expectation of the extended sample-path hitting time under the
Ionescu--Tulcea trajectory law.

The proof is monotone convergence.  Stage 23 identifies each finite truncation integral
with the corresponding Bellman finite-horizon runtime, and the two resulting suprema are
precisely the definitions on the two sides. -/
theorem runtimeSup_eq_lintegral_transitionTrajectoryHittingTime
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (x : α) :
    runtimeSup P target x =
      ∫⁻ path : ℕ → α,
        transitionTrajectoryHittingTime target x path
      ∂transitionTrajectoryMeasure P hP x := by
  unfold runtimeSup transitionTrajectoryHittingTime
  rw [MeasureTheory.lintegral_iSup
    (fun t => measurable_transitionTrajectoryTruncatedHittingCost target x t)
    (transitionTrajectoryTruncatedHittingCost_monotone target x)]
  simp_rw [transitionTrajectoryMeasure_lintegral_truncatedHittingCost P target hP x]

/-- Equivalent orientation of the Stage-24 bridge, convenient when the sample-path
expectation is the left-hand side of a runtime estimate. -/
theorem transitionTrajectoryHittingTime_lintegral_eq_runtimeSup
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (x : α) :
    (∫⁻ path : ℕ → α,
        transitionTrajectoryHittingTime target x path
      ∂transitionTrajectoryMeasure P hP x) =
      runtimeSup P target x := by
  exact (runtimeSup_eq_lintegral_transitionTrajectoryHittingTime
    P target hP x).symm

end ECRuntime
