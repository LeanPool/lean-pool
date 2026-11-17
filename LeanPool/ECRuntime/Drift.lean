/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.Transition

/-!
# Drift

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- Finite-state one-step expectation of a real-valued observable. -/
def expectedValueAfter {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (V : α → ℝ) (x : α) : ℝ :=
  ∑ y, P x y * V y

/-- Pointwise order is preserved by expectation under a stochastic matrix. -/
theorem expectedValueAfter_mono {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (V W : α → ℝ) (hVW : ∀ y, V y ≤ W y) (x : α) :
    expectedValueAfter P V x ≤ expectedValueAfter P W x := by
  unfold expectedValueAfter
  apply Finset.sum_le_sum
  intro y hy
  exact mul_le_mul_of_nonneg_left (hVW y) (hP.1 x y)

/-- Finite expectation commutes with multiplication of an observable by a scalar. -/
theorem expectedValueAfter_const_mul {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (c : ℝ) (V : α → ℝ) (x : α) :
    expectedValueAfter P (fun y => c * V y) x =
      c * expectedValueAfter P V x := by
  unfold expectedValueAfter
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Finite expectation is additive in the observable. -/
theorem expectedValueAfter_add {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (V W : α → ℝ) (x : α) :
    expectedValueAfter P (fun y => V y + W y) x =
      expectedValueAfter P V x + expectedValueAfter P W x := by
  unfold expectedValueAfter
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- One-step expected decrease of a potential. -/
def driftAt {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (V : α → ℝ) (x : α) : ℝ :=
  V x - expectedValueAfter P V x

/-- A stochastic matrix preserves constant observables. -/
theorem expectedValueAfter_const {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P) (c : ℝ) (x : α) :
    expectedValueAfter P (fun _ => c) x = c := by
  unfold expectedValueAfter
  calc
    (∑ y, P x y * c) = (∑ y, P x y) * c := by
      rw [Finset.sum_mul]
    _ = c := by rw [hP.2 x, one_mul]

/-- Nonnegative observables have nonnegative one-step expectation. -/
theorem expectedValueAfter_nonneg {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (V : α → ℝ) (hV : ∀ x, 0 ≤ V x) (x : α) :
    0 ≤ expectedValueAfter P V x := by
  unfold expectedValueAfter
  apply Finset.sum_nonneg
  intro y hy
  exact mul_nonneg (hP.1 x y) (hV y)

/-- Uniform additive-drift condition away from the zero-potential target. -/
def HasAdditiveDriftLowerBound {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (V : α → ℝ) (δ : ℝ) : Prop :=
  ∀ x, 0 < V x → δ ≤ driftAt P V x

/-- Multiplicative-drift condition away from the zero-potential target. -/
def HasMultiplicativeDriftLowerBound {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (V : α → ℝ) (δ : ℝ) : Prop :=
  ∀ x, 0 < V x → δ * V x ≤ driftAt P V x

/-- A finite Bellman-style certificate for an upper bound on expected remaining runtime. -/
def IsRuntimeSuperSolution {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α) (R : α → ℝ) : Prop :=
  (∀ x, x ∈ target → R x = 0) ∧
  (∀ x, x ∉ target → 1 + expectedValueAfter P R x ≤ R x)

/-- The Bellman operator for unit-cost reachability of a target set. -/
noncomputable def runtimeBellman {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    (R : α → ℝ) (x : α) : ℝ := by
  classical
  exact if x ∈ target then 0 else 1 + expectedValueAfter P R x

/-- The Bellman operator is monotone on observables for stochastic transition matrices. -/
theorem runtimeBellman_mono {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α) (hP : IsStochastic P)
    (V W : α → ℝ) (hVW : ∀ y, V y ≤ W y) (x : α) :
    runtimeBellman P target V x ≤ runtimeBellman P target W x := by
  classical
  by_cases hx : x ∈ target
  · simp [runtimeBellman, hx]
  · simpa [runtimeBellman, hx] using
      (add_le_add_left (expectedValueAfter_mono P hP V W hVW x) 1)

/-- A runtime supersolution is, in particular, a Bellman pre-fixed point. -/
theorem runtimeBellman_le_of_superSolution {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α) (R : α → ℝ)
    (hR : IsRuntimeSuperSolution P target R) (x : α) :
    runtimeBellman P target R x ≤ R x := by
  classical
  by_cases hx : x ∈ target
  · simp [runtimeBellman, hx, hR.1 x hx]
  · simpa [runtimeBellman, hx] using hR.2 x hx

/--
For the explicit `(1+1)`-EA semantics, one-step drift can be calculated directly
as an expectation over mutation masks rather than over pushed-forward next states.
-/
theorem onePlusOneTransition_drift_eq_mask_sum {n : ℕ}
    (p : ℝ) (fitness V : BitString n → ℝ) (x : BitString n) :
    driftAt (onePlusOneTransition p fitness) V x =
      ∑ mask : MutationMask n,
        mutationMaskWeight p mask *
          (V x - V (selectedAfterMask fitness x mask)) := by
  have hEV :
      expectedValueAfter (onePlusOneTransition p fitness) V x =
        ∑ mask : MutationMask n,
          mutationMaskWeight p mask * V (selectedAfterMask fitness x mask) := by
    unfold expectedValueAfter onePlusOneTransition
    exact pushforwardWeight_expectation
      (fun mask : MutationMask n => mutationMaskWeight p mask)
      (selectedAfterMask fitness x) V
  unfold driftAt
  rw [hEV]
  calc
    V x - ∑ mask : MutationMask n,
        mutationMaskWeight p mask * V (selectedAfterMask fitness x mask) =
      (∑ mask : MutationMask n, mutationMaskWeight p mask) * V x -
        ∑ mask : MutationMask n,
          mutationMaskWeight p mask * V (selectedAfterMask fitness x mask) := by
            rw [mutationMaskWeight_sum, one_mul]
    _ = ∑ mask : MutationMask n,
        mutationMaskWeight p mask *
          (V x - V (selectedAfterMask fitness x mask)) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro mask hmask
      ring

end ECRuntime
