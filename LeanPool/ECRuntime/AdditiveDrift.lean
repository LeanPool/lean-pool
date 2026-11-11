/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.UnrestrictedRuntime

/-!
# Additive Drift

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

namespace ECRuntime

/-- Standard additive-drift runtime certificate `V / δ`, written as `δ⁻¹ V`. -/
noncomputable def additiveDriftRuntime {α : Type*}
    (δ : ℝ) (V : α → ℝ) (x : α) : ℝ :=
  δ⁻¹ * V x

/-- A nonnegative potential gives a nonnegative additive-drift certificate. -/
theorem additiveDriftRuntime_nonneg {α : Type*}
    (δ : ℝ) (V : α → ℝ) (hδ : 0 < δ)
    (hV : ∀ x, 0 ≤ V x) (x : α) :
    0 ≤ additiveDriftRuntime δ V x := by
  unfold additiveDriftRuntime
  exact mul_nonneg (inv_nonneg.mpr hδ.le) (hV x)

/--
Finite-state additive drift as a Bellman certificate.

If `V=0` on the target and every non-target state has expected decrease at least
`δ>0`, then `V/δ` is a runtime supersolution.
-/
theorem additiveDrift_superSolution
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    (V : α → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hzero : ∀ x, x ∈ target → V x = 0)
    (hdrift : ∀ x, x ∉ target → δ ≤ driftAt P V x) :
    IsRuntimeSuperSolution P target (additiveDriftRuntime δ V) := by
  constructor
  · intro x hx
    simp [additiveDriftRuntime, hzero x hx]
  · intro x hx
    have hstep : δ + expectedValueAfter P V x ≤ V x := by
      have hd := hdrift x hx
      unfold driftAt at hd
      linarith
    have hinvnonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    have hscaled := mul_le_mul_of_nonneg_left hstep hinvnonneg
    have hδne : δ ≠ 0 := ne_of_gt hδ
    unfold additiveDriftRuntime
    rw [expectedValueAfter_const_mul]
    calc
      1 + δ⁻¹ * expectedValueAfter P V x =
          δ⁻¹ * (δ + expectedValueAfter P V x) := by
        rw [mul_add, inv_mul_cancel₀ hδne]
      _ ≤ δ⁻¹ * V x := hscaled

/-- Additive drift bounds every finite truncation by `V(x)/δ`. -/
theorem additiveDrift_finiteHorizonBound
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (V : α → ℝ) (δ : ℝ)
    (hP : IsStochastic P) (hδ : 0 < δ)
    (hV : ∀ x, 0 ≤ V x)
    (hzero : ∀ x, x ∈ target → V x = 0)
    (hdrift : ∀ x, x ∉ target → δ ≤ driftAt P V x) :
    HasUniformFiniteHorizonRuntimeBound
      P target (additiveDriftRuntime δ V) := by
  apply hasUniformFiniteHorizonRuntimeBound_of_superSolution
  · exact hP
  · exact additiveDriftRuntime_nonneg δ V hδ hV
  · exact additiveDrift_superSolution P target V δ hδ hzero hdrift

/-- Additive drift also bounds the unrestricted runtime supremum in `ℝ≥0∞`. -/
theorem additiveDrift_runtimeSup_le
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun x => x ∈ target)]
    (V : α → ℝ) (δ : ℝ)
    (hP : IsStochastic P) (hδ : 0 < δ)
    (hV : ∀ x, 0 ≤ V x)
    (hzero : ∀ x, x ∈ target → V x = 0)
    (hdrift : ∀ x, x ∉ target → δ ≤ driftAt P V x)
    (x : α) :
    runtimeSup P target x ≤ ENNReal.ofReal (additiveDriftRuntime δ V x) := by
  apply runtimeSup_le_of_uniform_bound P target (additiveDriftRuntime δ V)
  exact additiveDrift_finiteHorizonBound
    P target V δ hP hδ hV hzero hdrift

/-- A multiplicative drift bound becomes an additive one when positive states are separated from
zero. -/
theorem multiplicativeDrift_implies_additive_away_target
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    (V : α → ℝ) (δ vmin : ℝ)
    (hδ : 0 < δ) (hvmin : 0 < vmin)
    (hmin : ∀ x, x ∉ target → vmin ≤ V x)
    (hmult : HasMultiplicativeDriftLowerBound P V δ) :
    ∀ x, x ∉ target → δ * vmin ≤ driftAt P V x := by
  intro x hx
  have hVpos : 0 < V x := lt_of_lt_of_le hvmin (hmin x hx)
  have hmul : δ * V x ≤ driftAt P V x := hmult x hVpos
  have hlower : δ * vmin ≤ δ * V x :=
    mul_le_mul_of_nonneg_left (hmin x hx) hδ.le
  exact hlower.trans hmul

end ECRuntime
