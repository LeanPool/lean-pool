/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.Mutation

/-!
# Transition

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- A finite-state transition matrix. -/
abbrev TransitionMatrix (α : Type*) := α → α → ℝ

/-- Every transition probability is nonnegative and every row has mass one. -/
def IsStochastic {α : Type*} [Fintype α] (P : TransitionMatrix α) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧ (∀ x, ∑ y, P x y = 1)

/-- A state is absorbing when it stays put with probability one. -/
def IsAbsorbing {α : Type*}
    (P : TransitionMatrix α) (a : α) : Prop :=
  P a a = 1 ∧ ∀ y, y ≠ a → P a y = 0

/-- A natural-valued potential characterizes a target set by its zero level. -/
def IsTargetPotential {α : Type*} (V : α → ℕ) (target : Set α) : Prop :=
  ∀ x, x ∈ target ↔ V x = 0

/-- Elitist acceptance for a maximization problem. -/
def Accepts {α : Type*} (fitness : α → ℝ) (parent child : α) : Prop :=
  fitness parent ≤ fitness child

/-- Deterministic elitist selection for a maximization problem. -/
noncomputable def elitistSelect {α : Type*}
    (fitness : α → ℝ) (parent child : α) : α :=
  if fitness parent ≤ fitness child then child else parent

@[simp] theorem elitistSelect_of_accepts {α : Type*}
    (fitness : α → ℝ) (parent child : α)
    (h : Accepts fitness parent child) :
    elitistSelect fitness parent child = child := by
  have hle : fitness parent ≤ fitness child := by
    simpa [Accepts] using h
  simp [elitistSelect, hle]

@[simp] theorem elitistSelect_of_rejects {α : Type*}
    (fitness : α → ℝ) (parent child : α)
    (h : ¬ Accepts fitness parent child) :
    elitistSelect fitness parent child = parent := by
  have hnle : ¬ fitness parent ≤ fitness child := by
    simpa [Accepts] using h
  simp [elitistSelect, hnle]

/--
Push a finite nonnegative weight function through a deterministic map.
This is the finite analogue of the push-forward construction used for a Markov kernel.
-/
def pushforwardWeight {α β : Type*} [Fintype α] [DecidableEq β]
    (w : α → ℝ) (f : α → β) (y : β) : ℝ :=
  ∑ x, if f x = y then w x else 0

theorem pushforwardWeight_nonneg {α β : Type*} [Fintype α] [DecidableEq β]
    (w : α → ℝ) (f : α → β) (hw : ∀ x, 0 ≤ w x) (y : β) :
    0 ≤ pushforwardWeight w f y := by
  unfold pushforwardWeight
  apply Finset.sum_nonneg
  intro x hx
  by_cases h : f x = y
  · simp [h, hw x]
  · simp [h]

/-- Push-forward preserves total mass on finite types. -/
theorem pushforwardWeight_sum {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β]
    (w : α → ℝ) (f : α → β) :
    (∑ y, pushforwardWeight w f y) = ∑ x, w x := by
  classical
  unfold pushforwardWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp

/-- A finite random-step model, obtained by pushing outcome weights through a state update map. -/
def finiteRandomTransition {α Ω : Type*}
    [Fintype Ω] [DecidableEq α]
    (w : α → Ω → ℝ) (step : α → Ω → α) : TransitionMatrix α :=
  fun x y => pushforwardWeight (w x) (step x) y

/-- A normalized nonnegative finite random-step model is stochastic. -/
theorem finiteRandomTransition_stochastic {α Ω : Type*}
    [Fintype α] [Fintype Ω] [DecidableEq α]
    (w : α → Ω → ℝ) (step : α → Ω → α)
    (hw : ∀ x ω, 0 ≤ w x ω)
    (hsum : ∀ x, ∑ ω, w x ω = 1) :
    IsStochastic (finiteRandomTransition w step) := by
  constructor
  · intro x y
    unfold finiteRandomTransition
    exact pushforwardWeight_nonneg (w x) (step x) (hw x) y
  · intro x
    simpa [finiteRandomTransition] using
      (pushforwardWeight_sum (w := w x) (f := step x)).trans (hsum x)

/-- State obtained after applying one mutation mask and elitist selection. -/
noncomputable def selectedAfterMask {n : ℕ}
    (fitness : BitString n → ℝ) (parent : BitString n) (mask : MutationMask n) :
    BitString n :=
  elitistSelect fitness parent (mutateWithMask parent mask)

/--
Finite transition matrix of the `(1+1)` EA with independent bit mutation rate `p`
and elitist selection for a maximization objective.
-/
noncomputable def onePlusOneTransition {n : ℕ}
    (p : ℝ) (fitness : BitString n → ℝ) : TransitionMatrix (BitString n) :=
  fun parent next =>
    pushforwardWeight
      (fun mask : MutationMask n => mutationMaskWeight p mask)
      (selectedAfterMask fitness parent)
      next

/-- The specialized `(1+1)`-EA matrix is an instance of the generic finite random-step model. -/
theorem onePlusOneTransition_eq_finiteRandomTransition {n : ℕ}
    (p : ℝ) (fitness : BitString n → ℝ) :
    onePlusOneTransition p fitness =
      finiteRandomTransition
        (fun _parent (_mask : MutationMask n) => mutationMaskWeight p _mask)
        (selectedAfterMask fitness) := by
  rfl

/-- For `0 ≤ p ≤ 1`, the `(1+1)`-EA transition matrix is stochastic. -/
theorem onePlusOneTransition_stochastic {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (fitness : BitString n → ℝ) :
    IsStochastic (onePlusOneTransition p fitness) := by
  constructor
  · intro parent next
    unfold onePlusOneTransition
    apply pushforwardWeight_nonneg
    intro mask
    exact mutationMaskWeight_nonneg hp0 hp1 mask
  · intro parent
    calc
      (∑ next, onePlusOneTransition p fitness parent next) =
          ∑ mask : MutationMask n, mutationMaskWeight p mask := by
            simpa [onePlusOneTransition] using
              (pushforwardWeight_sum
                (w := fun mask : MutationMask n => mutationMaskWeight p mask)
                (f := selectedAfterMask fitness parent))
      _ = 1 := mutationMaskWeight_sum n p

/-- Push-forward also preserves finite weighted expectations. -/
theorem pushforwardWeight_expectation {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β]
    (w : α → ℝ) (f : α → β) (V : β → ℝ) :
    (∑ y, pushforwardWeight w f y * V y) =
      ∑ x, w x * V (f x) := by
  classical
  unfold pushforwardWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp

/-- Total weight of an event in a finite weighted sample space.

`Set.indicator` is deliberately used here because it is noncomputable and does not
thread `DecidablePred` instances through theorem statements.  This makes event mass
extensional in the predicate rather than dependent on a particular decision procedure.
-/
noncomputable def finiteEventMass {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) : ℝ :=
  ∑ x, ({x | event x} : Set α).indicator w x

/-- A nonnegative subfamily of an event gives a lower bound on its total mass. -/
theorem sum_le_finiteEventMass_of_subset {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop)
    (s : Finset α) (hw : ∀ x, 0 ≤ w x)
    (hs : ∀ x ∈ s, event x) :
    (∑ x ∈ s, w x) ≤ finiteEventMass w event := by
  classical
  unfold finiteEventMass
  calc
    (∑ x ∈ s, w x) =
        ∑ x ∈ s, ({y | event y} : Set α).indicator w x := by
      apply Finset.sum_congr rfl
      intro x hx
      have hmem : x ∈ ({y | event y} : Set α) := hs x hx
      rw [Set.indicator_of_mem hmem w]
    _ ≤ ∑ x, ({y | event y} : Set α).indicator w x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ s
      · intro x hx hxs
        by_cases he : event x
        · have hmem : x ∈ ({y | event y} : Set α) := he
          rw [Set.indicator_of_mem hmem w]
          exact hw x
        · have hnotmem : x ∉ ({y | event y} : Set α) := he
          rw [Set.indicator_of_notMem hnotmem w]

end ECRuntime
