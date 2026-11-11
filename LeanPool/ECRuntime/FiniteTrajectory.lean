/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import Mathlib.Data.Fintype.BigOperators

public import LeanPool.ECRuntime.HittingTime

/-!
# Finite trajectory semantics

This file gives an explicit finite-path interpretation of `finiteHorizonRuntime`.
A horizon-`t` trajectory stores the next `t` states; the initial state is supplied
separately.  For a stochastic transition matrix the recursively defined trajectory
weights are nonnegative and sum to one.  The main theorem identifies the finite path
sum of the truncated hitting cost with the Bellman quantity `finiteHorizonRuntime`.

No infinite path space or measure-theoretic expectation is introduced here.  Those are
separate later steps.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- The next `t` states of a finite trajectory.  The state at time zero is supplied
separately to the trajectory weight/cost functions. -/
abbrev FiniteTrajectory (α : Type*) (t : ℕ) := Fin t → α

/-- Probability weight of a finite trajectory, conditional on its supplied initial state. -/
def finiteTrajectoryWeight {α : Type*}
    (P : TransitionMatrix α) :
    (t : ℕ) → α → FiniteTrajectory α t → ℝ
  | 0, _x, _path => 1
  | t + 1, x, path =>
      P x (path 0) *
        finiteTrajectoryWeight P t (path 0) (Fin.tail path)

/-- Real-valued truncated first-hitting cost along one finite trajectory.

Starting from `x`, this counts one unit for each pre-target state among the first `t`
transitions.  Thus it is the pathwise finite-horizon quantity corresponding to
`min(T_target,t)`.
-/
def finiteTrajectoryTruncatedHittingCost {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)] :
    (t : ℕ) → α → FiniteTrajectory α t → ℝ
  | 0, _x, _path => 0
  | t + 1, x, path =>
      if x ∈ target then 0
      else 1 + finiteTrajectoryTruncatedHittingCost target t (path 0) (Fin.tail path)

/-- Explicit finite path-sum expectation of the truncated hitting cost. -/
def finiteTrajectoryExpectedHittingCost {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (t : ℕ) (x : α) : ℝ :=
  ∑ path : FiniteTrajectory α t,
    finiteTrajectoryWeight P t x path *
      finiteTrajectoryTruncatedHittingCost target t x path

@[simp] theorem finiteTrajectoryWeight_cons {α : Type*}
    (P : TransitionMatrix α) (t : ℕ) (x y : α)
    (tail : FiniteTrajectory α t) :
    finiteTrajectoryWeight P (t + 1) x (Fin.cons y tail) =
      P x y * finiteTrajectoryWeight P t y tail := by
  simp [finiteTrajectoryWeight]

@[simp] theorem finiteTrajectoryTruncatedHittingCost_cons_of_mem {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (t : ℕ) (x y : α) (tail : FiniteTrajectory α t)
    (hx : x ∈ target) :
    finiteTrajectoryTruncatedHittingCost target (t + 1) x (Fin.cons y tail) = 0 := by
  simp [finiteTrajectoryTruncatedHittingCost, hx]

@[simp] theorem finiteTrajectoryTruncatedHittingCost_cons_of_not_mem {α : Type*}
    (target : Set α) [DecidablePred (fun x => x ∈ target)]
    (t : ℕ) (x y : α) (tail : FiniteTrajectory α t)
    (hx : x ∉ target) :
    finiteTrajectoryTruncatedHittingCost target (t + 1) x (Fin.cons y tail) =
      1 + finiteTrajectoryTruncatedHittingCost target t y tail := by
  simp [finiteTrajectoryTruncatedHittingCost, hx]

/-- A sum over length-`t+1` trajectories can be split into the first next-state and
the remaining length-`t` tail. -/
theorem sum_finiteTrajectory_succ {α : Type*} [Fintype α]
    (t : ℕ) (F : FiniteTrajectory α (t + 1) → ℝ) :
    (∑ path : FiniteTrajectory α (t + 1), F path) =
      ∑ y : α, ∑ tail : FiniteTrajectory α t, F (Fin.cons y tail) := by
  classical
  let e : FiniteTrajectory α (t + 1) ≃ α × FiniteTrajectory α t :=
    (Fin.consEquiv (fun _ : Fin (t + 1) => α)).symm
  calc
    (∑ path : FiniteTrajectory α (t + 1), F path) =
        ∑ z : α × FiniteTrajectory α t, F (Fin.cons z.1 z.2) := by
      refine Fintype.sum_equiv e F
        (fun z : α × FiniteTrajectory α t => F (Fin.cons z.1 z.2)) ?_
      intro path
      simp [e]
    _ = ∑ y : α, ∑ tail : FiniteTrajectory α t, F (Fin.cons y tail) := by
      simpa using
        (Fintype.sum_prod_type
          (fun z : α × FiniteTrajectory α t => F (Fin.cons z.1 z.2)))

/-- Under a stochastic transition matrix, every finite trajectory weight is nonnegative. -/
theorem finiteTrajectoryWeight_nonneg {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P) :
    ∀ t x (path : FiniteTrajectory α t), 0 ≤ finiteTrajectoryWeight P t x path := by
  intro t
  induction t with
  | zero =>
      intro x path
      simp [finiteTrajectoryWeight]
  | succ t ih =>
      intro x path
      simp only [finiteTrajectoryWeight]
      exact mul_nonneg (hP.1 x (path 0)) (ih (path 0) (Fin.tail path))

/-- Under a stochastic transition matrix, finite trajectory weights have total mass one. -/
theorem finiteTrajectoryWeight_sum {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P) :
    ∀ t x, (∑ path : FiniteTrajectory α t, finiteTrajectoryWeight P t x path) = 1 := by
  intro t
  induction t with
  | zero =>
      intro x
      simp [finiteTrajectoryWeight]
  | succ t ih =>
      intro x
      rw [sum_finiteTrajectory_succ]
      simp_rw [finiteTrajectoryWeight_cons]
      calc
        (∑ y : α, ∑ tail : FiniteTrajectory α t,
            P x y * finiteTrajectoryWeight P t y tail) =
            ∑ y : α, P x y *
              (∑ tail : FiniteTrajectory α t, finiteTrajectoryWeight P t y tail) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
        _ = ∑ y : α, P x y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [ih y, mul_one]
        _ = 1 := hP.2 x

@[simp] theorem finiteTrajectoryExpectedHittingCost_zero {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)] (x : α) :
    finiteTrajectoryExpectedHittingCost P target 0 x = 0 := by
  simp [finiteTrajectoryExpectedHittingCost, finiteTrajectoryWeight,
    finiteTrajectoryTruncatedHittingCost]

/-- If the initial state is already in the target, every positive-horizon trajectory
has zero truncated hitting cost. -/
theorem finiteTrajectoryExpectedHittingCost_succ_of_mem {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (t : ℕ) (x : α) (hx : x ∈ target) :
    finiteTrajectoryExpectedHittingCost P target (t + 1) x = 0 := by
  unfold finiteTrajectoryExpectedHittingCost
  apply Finset.sum_eq_zero
  intro path hpath
  simp [finiteTrajectoryTruncatedHittingCost, hx]

/-- Away from the target, the explicit finite-path expectation satisfies exactly the
same one-step Bellman recursion as `finiteHorizonRuntime`. -/
theorem finiteTrajectoryExpectedHittingCost_succ_of_not_mem
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (t : ℕ) (x : α) (hx : x ∉ target) :
    finiteTrajectoryExpectedHittingCost P target (t + 1) x =
      1 + expectedValueAfter P
        (finiteTrajectoryExpectedHittingCost P target t) x := by
  classical
  unfold finiteTrajectoryExpectedHittingCost
  rw [sum_finiteTrajectory_succ]
  simp_rw [finiteTrajectoryWeight_cons]
  simp_rw [finiteTrajectoryTruncatedHittingCost, hx]
  calc
    (∑ y : α, ∑ tail : FiniteTrajectory α t,
        (P x y * finiteTrajectoryWeight P t y tail) *
          (1 + finiteTrajectoryTruncatedHittingCost target t y tail)) =
        ∑ y : α,
          (P x y + P x y *
            finiteTrajectoryExpectedHittingCost P target t y) := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        (∑ tail : FiniteTrajectory α t,
            (P x y * finiteTrajectoryWeight P t y tail) *
              (1 + finiteTrajectoryTruncatedHittingCost target t y tail)) =
            ∑ tail : FiniteTrajectory α t,
              (P x y * finiteTrajectoryWeight P t y tail +
                P x y *
                  (finiteTrajectoryWeight P t y tail *
                    finiteTrajectoryTruncatedHittingCost target t y tail)) := by
          apply Finset.sum_congr rfl
          intro tail htail
          ring
        _ =
            (∑ tail : FiniteTrajectory α t,
              P x y * finiteTrajectoryWeight P t y tail) +
            (∑ tail : FiniteTrajectory α t,
              P x y *
                (finiteTrajectoryWeight P t y tail *
                  finiteTrajectoryTruncatedHittingCost target t y tail)) := by
          rw [Finset.sum_add_distrib]
        _ =
            P x y *
              (∑ tail : FiniteTrajectory α t,
                finiteTrajectoryWeight P t y tail) +
            P x y *
              (∑ tail : FiniteTrajectory α t,
                finiteTrajectoryWeight P t y tail *
                  finiteTrajectoryTruncatedHittingCost target t y tail) := by
          have hfirst :
              (∑ tail : FiniteTrajectory α t,
                P x y * finiteTrajectoryWeight P t y tail) =
                P x y *
                  (∑ tail : FiniteTrajectory α t,
                    finiteTrajectoryWeight P t y tail) := by
            rw [Finset.mul_sum]
          have hsecond :
              (∑ tail : FiniteTrajectory α t,
                P x y *
                  (finiteTrajectoryWeight P t y tail *
                    finiteTrajectoryTruncatedHittingCost target t y tail)) =
                P x y *
                  (∑ tail : FiniteTrajectory α t,
                    finiteTrajectoryWeight P t y tail *
                      finiteTrajectoryTruncatedHittingCost target t y tail) := by
            rw [Finset.mul_sum]
          rw [hfirst, hsecond]
        _ = P x y + P x y *
            finiteTrajectoryExpectedHittingCost P target t y := by
          rw [finiteTrajectoryWeight_sum P hP t y]
          simp [finiteTrajectoryExpectedHittingCost]
    _ = 1 + expectedValueAfter P
        (finiteTrajectoryExpectedHittingCost P target t) x := by
      rw [Finset.sum_add_distrib]
      unfold expectedValueAfter
      rw [hP.2 x]

/-- The explicit finite path-sum expectation is exactly the existing Bellman
finite-horizon runtime. -/
theorem finiteTrajectoryExpectedHittingCost_eq_finiteHorizonRuntime
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) :
    ∀ t x,
      finiteTrajectoryExpectedHittingCost P target t x =
        finiteHorizonRuntime P target t x := by
  intro t
  induction t with
  | zero =>
      intro x
      simp
  | succ t ih =>
      intro x
      by_cases hx : x ∈ target
      · rw [finiteTrajectoryExpectedHittingCost_succ_of_mem P target t x hx]
        rw [finiteHorizonRuntime_succ_of_mem P target t x hx]
      · rw [finiteTrajectoryExpectedHittingCost_succ_of_not_mem P target hP t x hx]
        rw [finiteHorizonRuntime_succ_of_not_mem P target t x hx]
        unfold expectedValueAfter
        apply congrArg (fun z : ℝ => 1 + z)
        apply Finset.sum_congr rfl
        intro y hy
        rw [ih y]

/-- In particular, the explicit finite path-sum expectation is nonnegative. -/
theorem finiteTrajectoryExpectedHittingCost_nonneg
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (t : ℕ) (x : α) :
    0 ≤ finiteTrajectoryExpectedHittingCost P target t x := by
  rw [finiteTrajectoryExpectedHittingCost_eq_finiteHorizonRuntime P target hP t x]
  exact finiteHorizonRuntime_nonneg P target hP t x

end ECRuntime
