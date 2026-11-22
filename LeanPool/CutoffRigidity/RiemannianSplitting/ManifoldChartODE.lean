/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartFrames
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! # Genuine chart ODEs pull back to actual manifold integral curves -/

@[expose] public section
open Bundle Set Filter
open scoped Manifold Topology


namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]

omit [BoundarylessManifold I M] in
/-- An actual solution of the actual coordinate pullback ODE yields the actual
manifold derivative prescribed by the original vector field. -/
theorem hasMFDerivAt_chart_inverse_of_coordinateODE
    (x₀ : M) {X : (x : M) → TangentSpace I x} {f : ℝ → E} {t : ℝ}
    (hf : HasDerivAt f (chartCoordinateField (I := I) x₀ X (f t)) t)
    (htarget : f t ∈ interior (extChartAt I x₀).target) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I ((extChartAt I x₀).symm ∘ f) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X ((extChartAt I x₀).symm (f t)))) := by
  let e := extChartAt I x₀
  have hRange : range I ∈ 𝓝 (f t) := mem_of_superset (isOpen_interior.mem_nhds htarget)
    (interior_subset.trans (extChartAt_target_subset_range x₀))
  have hInv : MDifferentiableAt 𝓘(ℝ, E) I e.symm (f t) :=
    (mdifferentiableWithinAt_extChartAt_symm (interior_subset htarget)).mdifferentiableAt hRange
  let D : E →L[ℝ] TangentSpace I (e.symm (f t)) := mfderiv 𝓘(ℝ, E) I e.symm (f t)
  have hDir : D (chartCoordinateField (I := I) x₀ X (f t)) = X (e.symm (f t)) := by
    have hD : D = mfderivWithin 𝓘(ℝ, E) I e.symm (range I) (f t) :=
      (mfderivWithin_of_mem_nhds hRange).symm
    rw [hD]
    symm
    apply (isInvertible_mfderivWithin_extChartAt_symm
      (I := I) (interior_subset htarget)).inverse_apply_eq.mp
    rfl
  have h := hInv.hasMFDerivAt.comp t hf.hasFDerivAt.hasMFDerivAt
  have derivative :
      D.comp ((1 : ℝ →L[ℝ] ℝ).smulRight (chartCoordinateField (I := I) x₀ X (f t))) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (X (e.symm (f t))) := by
    apply ContinuousLinearMap.ext
    intro a
    change D (a • chartCoordinateField (I := I) x₀ X (f t)) = a • X (e.symm (f t))
    rw [map_smul, hDir]
  change HasMFDerivAt 𝓘(ℝ, ℝ) I (e.symm ∘ f) t _
  rw [← derivative]
  exact h

omit [BoundarylessManifold I M] in
/-- The actual coordinate ODE gives an actual manifold integral curve on the
specified time domain, with all domain obligations visible. -/
theorem isMIntegralCurveOn_chart_inverse_of_coordinateODE
    (x₀ : M) {X : (x : M) → TangentSpace I x} {f : ℝ → E} {s : Set ℝ}
    (hf : ∀ t ∈ s, HasDerivAt f (chartCoordinateField (I := I) x₀ X (f t)) t)
    (htarget : ∀ t ∈ s, f t ∈ interior (extChartAt I x₀).target) :
    IsMIntegralCurveOn ((extChartAt I x₀).symm ∘ f) X s :=
  fun t ht ↦ (hasMFDerivAt_chart_inverse_of_coordinateODE x₀ (hf t ht) (htarget t
      ht)).hasMFDerivWithinAt

end CutoffRigidity
