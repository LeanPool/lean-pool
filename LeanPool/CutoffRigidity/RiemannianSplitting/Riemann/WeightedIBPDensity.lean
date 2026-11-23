/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Statements
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-! # Density of the preferred inverse chart -/

@[expose] public section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace CutCur

/-- The chart density is the inverse chart's Riemannian Jacobian in an orthonormal basis. -/
theorem chartDensity_eq_jacobian {F M : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [ChartedSpace F M]
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
    (Ξ : OpenPartialHomeomorph M F) (z : F) :
    chartDensity Ξ z = TauCeti.riemannianJacobian (I := 𝓘(ℝ, F))
      (stdOrthonormalBasis ℝ F).toBasis Ξ.symm z := by
  rw [TauCeti.riemannianJacobian_eq_sqrt_det_gram]
  rfl

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]

omit [IsManifold 𝓘(ℝ, F) ∞ M] in
/-- The chart density is the inverse chart's Riemannian Jacobian in an orthonormal basis. -/
theorem chartVolumeDensity_eq_jacobian (x₀ : M) (z : F) :
    chartVolumeDensity F x₀ z =
      TauCeti.riemannianJacobian (I := 𝓘(ℝ, F)) (stdOrthonormalBasis ℝ F).toBasis
        (chartAt F x₀).symm z :=
  chartDensity_eq_jacobian (chartAt F x₀) z

omit [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
private theorem extChartAt_target_model (x₀ : M) :
    (extChartAt 𝓘(ℝ, F) x₀).target = (chartAt F x₀).target := by
  simp [extChartAt, OpenPartialHomeomorph.extend]

theorem chartVolumeDensity_pos (x₀ : M) {z : F} (hz : z ∈ (chartAt F x₀).target) :
    0 < chartVolumeDensity F x₀ z := by
  let e := chartAt F x₀
  let D : F →L[ℝ] TangentSpace 𝓘(ℝ, F) (e.symm z) :=
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) e.symm z
  have hz' : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := extChartAt_target_model F x₀ ▸ hz
  have hInv := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, F)) hz'
  simp only [ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ] at hInv
  have hLeft : Function.LeftInverse D.inverse D := fun x ↦ hInv.inverse_apply_eq.mpr rfl
  have hIndependent := (stdOrthonormalBasis ℝ F).toBasis.linearIndependent.map'
    D.toLinearMap (LinearMap.ker_eq_bot.mpr hLeft.injective)
  rw [chartVolumeDensity_eq_jacobian, TauCeti.riemannianJacobian_eq_sqrt_det_gram]
  exact Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent hIndependent).det_pos

variable [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]

theorem continuousOn_chartVolumeDensity (x₀ : M) :
    ContinuousOn (chartVolumeDensity F x₀) (chartAt F x₀).target := by
  let : IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
      (IB := 𝓘(ℝ, F)) (n := ∞) (V := fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)
  have hchart : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 (chartAt F x₀).symm
      (chartAt F x₀).target := by
    rw [← extChartAt_target_model F x₀]
    exact contMDiffOn_extChartAt_symm x₀
  refine (TauCeti.continuousOn_riemannianJacobian (stdOrthonormalBasis ℝ F).toBasis
    hchart (chartAt F x₀).open_target).congr ?_
  exact fun z _ ↦ chartVolumeDensity_eq_jacobian F x₀ z

end CutCur
