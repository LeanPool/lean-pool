/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.AdditiveDrift
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Multiplicative Drift

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- Target set associated with the zero level of a real-valued potential. -/
def realPotentialTarget {α : Type*} (V : α → ℝ) : Set α :=
  {x | V x = 0}

/-- Membership in a real zero-potential target is decidable classically. -/
noncomputable instance instDecidablePredRealPotentialTarget {α : Type*} (V : α → ℝ) :
    DecidablePred (fun x => x ∈ realPotentialTarget V) := by
  classical
  intro x
  change Decidable (V x = 0)
  infer_instance

/--
Logarithmic transform used in the multiplicative-drift theorem.

The value is zero on the target.  Away from zero it is
`1 + log(V(x)) - log(vmin)`, which is at least one whenever
`vmin ≤ V(x)`.
-/
noncomputable def multiplicativeDriftPotential {α : Type*}
    (vmin : ℝ) (V : α → ℝ) (x : α) : ℝ :=
  if V x = 0 then 0 else 1 + Real.log (V x) - Real.log vmin

/-- The logarithmic transform vanishes on the zero-potential target. -/
theorem multiplicativeDriftPotential_eq_zero_of_mem {α : Type*}
    (vmin : ℝ) (V : α → ℝ) (x : α)
    (hx : x ∈ realPotentialTarget V) :
    multiplicativeDriftPotential vmin V x = 0 := by
  have hx0 : V x = 0 := by simpa [realPotentialTarget] using hx
  simp [multiplicativeDriftPotential, hx0]

/-- The logarithmic transform is nonnegative when positive potential values are at least `vmin`. -/
theorem multiplicativeDriftPotential_nonneg {α : Type*}
    (vmin : ℝ) (V : α → ℝ)
    (hvmin : 0 < vmin)
    (_hV : ∀ x, 0 ≤ V x)
    (hmin : ∀ x, x ∉ realPotentialTarget V → vmin ≤ V x) :
    ∀ x, 0 ≤ multiplicativeDriftPotential vmin V x := by
  intro x
  classical
  by_cases hx0 : V x = 0
  · simp [multiplicativeDriftPotential, hx0]
  · have hxTarget : x ∉ realPotentialTarget V := by
      simpa [realPotentialTarget] using hx0
    have hlog : Real.log vmin ≤ Real.log (V x) :=
      Real.log_le_log hvmin (hmin x hxTarget)
    simp [multiplicativeDriftPotential, hx0]
    linarith

/--
The logarithmic transform converts a relative potential decrease into an
additive decrease.  This is the pointwise inequality underlying the standard
multiplicative-drift theorem.
-/
theorem relativeDrop_le_multiplicativeDriftPotential_drop
    {α : Type*}
    (vmin : ℝ) (V : α → ℝ)
    (hvmin : 0 < vmin)
    (hV : ∀ z, 0 ≤ V z)
    (hmin : ∀ z, z ∉ realPotentialTarget V → vmin ≤ V z)
    (x y : α) (hx : x ∉ realPotentialTarget V) :
    (V x - V y) / V x ≤
      multiplicativeDriftPotential vmin V x -
        multiplicativeDriftPotential vmin V y := by
  classical
  have hx0 : V x ≠ 0 := by
    simpa [realPotentialTarget] using hx
  have hxpos : 0 < V x := lt_of_le_of_ne (hV x) (Ne.symm hx0)
  by_cases hy0 : V y = 0
  · have hlog : Real.log vmin ≤ Real.log (V x) :=
      Real.log_le_log hvmin (hmin x hx)
    have hfrac : (V x - V y) / V x = 1 := by
      rw [hy0, sub_zero, div_self hx0]
    rw [hfrac]
    simp [multiplicativeDriftPotential, hx0, hy0]
    linarith
  · have hypos : 0 < V y := lt_of_le_of_ne (hV y) (Ne.symm hy0)
    have hratioPos : 0 < V y / V x := div_pos hypos hxpos
    have hlogineq := Real.log_le_sub_one_of_pos hratioPos
    have hlogdiv : Real.log (V y / V x) = Real.log (V y) - Real.log (V x) :=
      Real.log_div hy0 hx0
    rw [hlogdiv] at hlogineq
    have hfrac : (V x - V y) / V x = 1 - V y / V x := by
      field_simp [hx0]
    rw [hfrac]
    simp [multiplicativeDriftPotential, hx0, hy0]
    linarith

/-- The weighted sum of one-step potential drops is exactly the finite-state drift. -/
theorem weightedDrop_sum_eq_drift
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (V : α → ℝ) (x : α) :
    (∑ y, P x y * (V x - V y)) = driftAt P V x := by
  have hconst : (∑ y, P x y * V x) = V x := by
    calc
      (∑ y, P x y * V x) = (∑ y, P x y) * V x := by
        rw [Finset.sum_mul]
      _ = V x := by rw [hP.2 x, one_mul]
  unfold driftAt expectedValueAfter
  calc
    (∑ y, P x y * (V x - V y)) =
        ∑ y, (P x y * V x - P x y * V y) := by
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = (∑ y, P x y * V x) - (∑ y, P x y * V y) := by
      rw [Finset.sum_sub_distrib]
    _ = V x - (∑ y, P x y * V y) := by rw [hconst]

/--
A multiplicative drift condition becomes an additive drift condition for the
logarithmically transformed potential.
-/
theorem multiplicativeDriftPotential_hasAdditiveDrift
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (V : α → ℝ) (δ vmin : ℝ)
    (hvmin : 0 < vmin)
    (hV : ∀ z, 0 ≤ V z)
    (hmin : ∀ z, z ∉ realPotentialTarget V → vmin ≤ V z)
    (hmult : HasMultiplicativeDriftLowerBound P V δ) :
    ∀ x, x ∉ realPotentialTarget V →
      δ ≤ driftAt P (multiplicativeDriftPotential vmin V) x := by
  intro x hx
  have hx0 : V x ≠ 0 := by
    simpa [realPotentialTarget] using hx
  have hxpos : 0 < V x := lt_of_le_of_ne (hV x) (Ne.symm hx0)
  have hpoint : ∀ y,
      V x - V y ≤ V x *
        (multiplicativeDriftPotential vmin V x -
          multiplicativeDriftPotential vmin V y) := by
    intro y
    have hrel := relativeDrop_le_multiplicativeDriftPotential_drop
      vmin V hvmin hV hmin x y hx
    have hscaled := mul_le_mul_of_nonneg_left hrel hxpos.le
    calc
      V x - V y = V x * ((V x - V y) / V x) := by
        field_simp [hx0]
      _ ≤ V x *
          (multiplicativeDriftPotential vmin V x -
            multiplicativeDriftPotential vmin V y) := hscaled
  have hsum :
      (∑ y, P x y * (V x - V y)) ≤
        ∑ y, P x y *
          (V x * (multiplicativeDriftPotential vmin V x -
            multiplicativeDriftPotential vmin V y)) := by
    apply Finset.sum_le_sum
    intro y hy
    exact mul_le_mul_of_nonneg_left (hpoint y) (hP.1 x y)
  have hright :
      (∑ y, P x y *
          (V x * (multiplicativeDriftPotential vmin V x -
            multiplicativeDriftPotential vmin V y))) =
        V x * driftAt P (multiplicativeDriftPotential vmin V) x := by
    calc
      (∑ y, P x y *
          (V x * (multiplicativeDriftPotential vmin V x -
            multiplicativeDriftPotential vmin V y))) =
          ∑ y, V x *
            (P x y * (multiplicativeDriftPotential vmin V x -
              multiplicativeDriftPotential vmin V y)) := by
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = V x *
          (∑ y, P x y *
            (multiplicativeDriftPotential vmin V x -
              multiplicativeDriftPotential vmin V y)) := by
        rw [Finset.mul_sum]
      _ = V x * driftAt P (multiplicativeDriftPotential vmin V) x := by
        rw [weightedDrop_sum_eq_drift P hP (multiplicativeDriftPotential vmin V) x]
  have hdriftScaled :
      driftAt P V x ≤
        V x * driftAt P (multiplicativeDriftPotential vmin V) x := by
    rw [← weightedDrop_sum_eq_drift P hP V x, ← hright]
    exact hsum
  have hmultx : δ * V x ≤ driftAt P V x := hmult x hxpos
  have hscaled : V x * δ ≤
      V x * driftAt P (multiplicativeDriftPotential vmin V) x := by
    calc
      V x * δ = δ * V x := by ring
      _ ≤ driftAt P V x := hmultx
      _ ≤ V x * driftAt P (multiplicativeDriftPotential vmin V) x := hdriftScaled
  by_contra hnot
  have hlt :
      driftAt P (multiplicativeDriftPotential vmin V) x < δ :=
    lt_of_not_ge hnot
  have hmul :
      V x * driftAt P (multiplicativeDriftPotential vmin V) x < V x * δ :=
    mul_lt_mul_of_pos_left hlt hxpos
  exact (not_lt_of_ge hscaled) hmul

/-- Runtime certificate produced by multiplicative drift. -/
noncomputable def multiplicativeDriftRuntime {α : Type*}
    (δ vmin : ℝ) (V : α → ℝ) (x : α) : ℝ :=
  additiveDriftRuntime δ (multiplicativeDriftPotential vmin V) x

/-- The logarithmic multiplicative-drift certificate is a Bellman supersolution. -/
theorem multiplicativeDrift_superSolution
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α)
    (V : α → ℝ) (δ vmin : ℝ)
    (hP : IsStochastic P) (hδ : 0 < δ) (hvmin : 0 < vmin)
    (hV : ∀ z, 0 ≤ V z)
    (hmin : ∀ z, z ∉ realPotentialTarget V → vmin ≤ V z)
    (hmult : HasMultiplicativeDriftLowerBound P V δ) :
    IsRuntimeSuperSolution P (realPotentialTarget V)
      (multiplicativeDriftRuntime δ vmin V) := by
  unfold multiplicativeDriftRuntime
  apply additiveDrift_superSolution
      P (realPotentialTarget V) (multiplicativeDriftPotential vmin V) δ hδ
  · intro x hx
    exact multiplicativeDriftPotential_eq_zero_of_mem vmin V x hx
  · exact multiplicativeDriftPotential_hasAdditiveDrift
      P hP V δ vmin hvmin hV hmin hmult

/-- Generic finite-state multiplicative-drift theorem for all finite truncations. -/
theorem multiplicativeDrift_finiteHorizonBound
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α)
    (V : α → ℝ) (δ vmin : ℝ)
    (hP : IsStochastic P) (hδ : 0 < δ) (hvmin : 0 < vmin)
    (hV : ∀ z, 0 ≤ V z)
    (hmin : ∀ z, z ∉ realPotentialTarget V → vmin ≤ V z)
    (hmult : HasMultiplicativeDriftLowerBound P V δ) :
    HasUniformFiniteHorizonRuntimeBound
      P (realPotentialTarget V) (multiplicativeDriftRuntime δ vmin V) := by
  apply hasUniformFiniteHorizonRuntimeBound_of_superSolution
  · exact hP
  · intro x
    unfold multiplicativeDriftRuntime
    exact additiveDriftRuntime_nonneg δ (multiplicativeDriftPotential vmin V) hδ
      (multiplicativeDriftPotential_nonneg vmin V hvmin hV hmin) x
  · exact multiplicativeDrift_superSolution
      P V δ vmin hP hδ hvmin hV hmin hmult

/-- Generic multiplicative drift also bounds the unrestricted runtime supremum. -/
theorem multiplicativeDrift_runtimeSup_le
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α)
    (V : α → ℝ) (δ vmin : ℝ)
    (hP : IsStochastic P) (hδ : 0 < δ) (hvmin : 0 < vmin)
    (hV : ∀ z, 0 ≤ V z)
    (hmin : ∀ z, z ∉ realPotentialTarget V → vmin ≤ V z)
    (hmult : HasMultiplicativeDriftLowerBound P V δ)
    (x : α) :
    runtimeSup P (realPotentialTarget V) x ≤
      ENNReal.ofReal (multiplicativeDriftRuntime δ vmin V x) := by
  apply runtimeSup_le_of_uniform_bound P (realPotentialTarget V)
      (multiplicativeDriftRuntime δ vmin V)
  exact multiplicativeDrift_finiteHorizonBound
    P V δ vmin hP hδ hvmin hV hmin hmult

/-- Away from the target, the certificate has the textbook `(1 + log(V/vmin))/δ` form. -/
theorem multiplicativeDriftRuntime_eq_log_ratio
    {α : Type*} (V : α → ℝ) (δ vmin : ℝ)
    (hvmin : vmin ≠ 0)
    (x : α) (hx : V x ≠ 0) :
    multiplicativeDriftRuntime δ vmin V x =
      δ⁻¹ * (1 + Real.log (V x / vmin)) := by
  unfold multiplicativeDriftRuntime additiveDriftRuntime multiplicativeDriftPotential
  rw [ite_eq_right hx]
  rw [Real.log_div hx hvmin]
  ring

end ECRuntime
