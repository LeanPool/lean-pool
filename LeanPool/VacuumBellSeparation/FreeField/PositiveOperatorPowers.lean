/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Nonnegative powers without an invertibility hypothesis

The actual continuous functional calculus allows zero in the spectrum.
Nonnegative exponent addition, injectivity for exponents in [0,1], and
dense range are proved without replacing pointwise injectivity by a
uniform positive lower bound.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem positiveOperator_rpow_add (A : E →L[ℂ] E)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    A ^ (p + q) = A ^ p * A ^ q := by
  simp only [CFC.rpow_def]
  rw [← cfc_mul (fun x : ℝ≥0 => x ^ p) (fun x : ℝ≥0 => x ^ q) A
    (NNReal.continuous_rpow_const hp).continuousOn
    (NNReal.continuous_rpow_const hq).continuousOn]
  congr 1
  funext x
  exact NNReal.rpow_add_of_nonneg x hp hq

theorem positiveOperator_rpow_injective (A : E →L[ℂ] E) (hA : 0 ≤ A)
    (hi : Function.Injective A) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Function.Injective (A ^ p) := by
  have hf : A = A ^ (1 - p) * A ^ p := by
    rw [← positiveOperator_rpow_add A (sub_nonneg.mpr hp1) hp,
      sub_add_cancel, CFC.rpow_one A hA]
  intro x y hxy
  apply hi
  rw [hf]
  change (A ^ (1 - p)) ((A ^ p) x) = (A ^ (1 - p)) ((A ^ p) y)
  rw [hxy]

theorem selfAdjoint_denseRange_of_injective (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hi : Function.Injective A) : DenseRange A := by
  have hker : A.ker = ⊥ := LinearMap.ker_eq_bot.mpr hi
  have horth : A.rangeᗮ = ⊥ := by rw [A.orthogonal_range, hA.adjoint_eq, hker]
  have hclose := A.range.topologicalClosure_eq_top_iff.mpr horth
  rw [denseRange_iff_closure_range]
  change (A.range.topologicalClosure : Set E) = Set.univ
  rw [hclose]
  rfl

theorem positiveOperator_rpow_denseRange (A : E →L[ℂ] E) (hA : 0 ≤ A)
    (hi : Function.Injective A) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    DenseRange (A ^ p) :=
  selfAdjoint_denseRange_of_injective _ CFC.rpow_nonneg.isSelfAdjoint
    (positiveOperator_rpow_injective A hA hi hp hp1)

end VacuumBellSeparation
