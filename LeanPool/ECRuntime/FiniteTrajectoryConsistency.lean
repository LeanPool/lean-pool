/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.FiniteTrajectory

/-!
# Projective consistency of finite trajectory laws

Stage 15 gives, for each horizon `t`, an explicit finite probability law on
`FiniteTrajectory α t`.  This file proves that these finite laws are compatible
when the last state is forgotten.  The result is still entirely finite-state:
no infinite product space or measure is introduced here.

The key statement is the observable form of consistency: for every real-valued
function of a length-`t` pref, its expectation under the length-`t+1` law after
applying `Fin.init` equals its expectation under the length-`t` law.  This is the
projective property needed by a later infinite-path construction.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- A sum over length-`t+1` trajectories can be split into the final state and
its length-`t` pref. -/
theorem sum_finiteTrajectory_snoc {α : Type*} [Fintype α]
    (t : ℕ) (F : FiniteTrajectory α (t + 1) → ℝ) :
    (∑ path : FiniteTrajectory α (t + 1), F path) =
      ∑ y : α, ∑ pref : FiniteTrajectory α t, F (Fin.snoc pref y) := by
  classical
  let e : FiniteTrajectory α (t + 1) ≃ α × FiniteTrajectory α t :=
    (Fin.snocEquiv (fun _ : Fin (t + 1) => α)).symm
  calc
    (∑ path : FiniteTrajectory α (t + 1), F path) =
        ∑ z : α × FiniteTrajectory α t, F (Fin.snoc z.2 z.1) := by
      refine Fintype.sum_equiv e F
        (fun z : α × FiniteTrajectory α t => F (Fin.snoc z.2 z.1)) ?_
      intro path
      simp [e]
    _ = ∑ y : α, ∑ pref : FiniteTrajectory α t,
          F (Fin.snoc pref y) := by
      simpa using
        (Fintype.sum_prod_type
          (fun z : α × FiniteTrajectory α t => F (Fin.snoc z.2 z.1)))

/-- Appending one state to a nonempty trajectory commutes with the recursive
front decomposition used by `finiteTrajectoryWeight`. -/
theorem finiteTrajectoryWeight_snoc_succ {α : Type*}
    (P : TransitionMatrix α) (t : ℕ) (x : α)
    (path : FiniteTrajectory α (t + 1)) (y : α) :
    finiteTrajectoryWeight P (t + 2) x (Fin.snoc path y) =
      P x (path 0) *
        finiteTrajectoryWeight P (t + 1) (path 0) (Fin.snoc (Fin.tail path) y) := by
  rw [← Fin.cons_self_tail path]
  rw [← Fin.cons_snoc_eq_snoc_cons]
  simp [finiteTrajectoryWeight]

/-- Projective consistency at one step: the total weight of all one-state
extensions of a fixed finite pref is exactly the weight of that pref. -/
theorem finiteTrajectoryWeight_snoc_sum {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P) :
    ∀ t x (path : FiniteTrajectory α t),
      (∑ y : α, finiteTrajectoryWeight P (t + 1) x (Fin.snoc path y)) =
        finiteTrajectoryWeight P t x path := by
  intro t
  induction t with
  | zero =>
      intro x path
      calc
        (∑ y : α, finiteTrajectoryWeight P 1 x (Fin.snoc path y)) =
            ∑ y : α, P x y := by
          apply Finset.sum_congr rfl
          intro y hy
          simp [finiteTrajectoryWeight, Fin.snoc_zero]
        _ = 1 := hP.2 x
        _ = finiteTrajectoryWeight P 0 x path := by
          rfl
  | succ t ih =>
      intro x path
      simp_rw [finiteTrajectoryWeight_snoc_succ P t x path]
      calc
        (∑ y : α,
            P x (path 0) *
              finiteTrajectoryWeight P (t + 1) (path 0)
                (Fin.snoc (Fin.tail path) y)) =
            P x (path 0) *
              (∑ y : α,
                finiteTrajectoryWeight P (t + 1) (path 0)
                  (Fin.snoc (Fin.tail path) y)) := by
          rw [Finset.mul_sum]
        _ = P x (path 0) *
              finiteTrajectoryWeight P t (path 0) (Fin.tail path) := by
          rw [ih (path 0) (Fin.tail path)]
        _ = finiteTrajectoryWeight P (t + 1) x path := by
          rfl

/-- Observable form of projective consistency.  If a function only observes the
first `t` states, then taking its expectation under the `(t+1)`-step law after
forgetting the last state gives exactly its expectation under the `t`-step law. -/
theorem finiteTrajectoryWeight_init_expectation {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (t : ℕ) (x : α) (F : FiniteTrajectory α t → ℝ) :
    (∑ path : FiniteTrajectory α (t + 1),
      finiteTrajectoryWeight P (t + 1) x path * F (Fin.init path)) =
      ∑ pref : FiniteTrajectory α t,
        finiteTrajectoryWeight P t x pref * F pref := by
  rw [sum_finiteTrajectory_snoc]
  simp_rw [Fin.init_snoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro pref hprefix
  calc
    (∑ y : α,
        finiteTrajectoryWeight P (t + 1) x (Fin.snoc pref y) * F pref) =
        (∑ y : α,
          finiteTrajectoryWeight P (t + 1) x (Fin.snoc pref y)) * F pref := by
      rw [Finset.sum_mul]
    _ = finiteTrajectoryWeight P t x pref * F pref := by
      rw [finiteTrajectoryWeight_snoc_sum P hP t x pref]

/-- Point-mass form of projective consistency: summing the `(t+1)`-step law over
all trajectories whose `Fin.init` pref is `pref` recovers the `t`-step path
weight. -/
theorem finiteTrajectoryWeight_init_fiber_sum {α : Type*} [Fintype α] [DecidableEq α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (t : ℕ) (x : α) (pref : FiniteTrajectory α t) :
    (∑ path : FiniteTrajectory α (t + 1),
      if Fin.init path = pref then finiteTrajectoryWeight P (t + 1) x path else 0) =
      finiteTrajectoryWeight P t x pref := by
  classical
  have h := finiteTrajectoryWeight_init_expectation P hP t x
    (fun q : FiniteTrajectory α t => if q = pref then 1 else 0)
  simpa [mul_ite] using h

/-- The Stage-15 truncated hitting-cost expectation is compatible with extending
finite trajectory laws: observe only the first `t` states of a `(t+1)`-step path,
and the resulting expectation is the original horizon-`t` expectation. -/
theorem finiteTrajectoryExpectedHittingCost_init_consistent
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (t : ℕ) (x : α) :
    (∑ path : FiniteTrajectory α (t + 1),
      finiteTrajectoryWeight P (t + 1) x path *
        finiteTrajectoryTruncatedHittingCost target t x (Fin.init path)) =
      finiteTrajectoryExpectedHittingCost P target t x := by
  simpa [finiteTrajectoryExpectedHittingCost] using
    (finiteTrajectoryWeight_init_expectation P hP t x
      (fun pref : FiniteTrajectory α t =>
        finiteTrajectoryTruncatedHittingCost target t x pref))

/-- Combining Stage 15 with projective consistency, the Bellman
`finiteHorizonRuntime` is also the expectation of the horizon-`t` pathwise hitting
cost when that observable is evaluated under the next longer finite law. -/
theorem finiteTrajectoryExpectedHittingCost_init_eq_finiteHorizonRuntime
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (t : ℕ) (x : α) :
    (∑ path : FiniteTrajectory α (t + 1),
      finiteTrajectoryWeight P (t + 1) x path *
        finiteTrajectoryTruncatedHittingCost target t x (Fin.init path)) =
      finiteHorizonRuntime P target t x := by
  rw [finiteTrajectoryExpectedHittingCost_init_consistent P target hP t x]
  exact finiteTrajectoryExpectedHittingCost_eq_finiteHorizonRuntime P target hP t x

end ECRuntime
