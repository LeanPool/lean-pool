/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.AffineSubspaceSplitting

/-! # Curvature of the genuine complementary potential

The actual second Frechet derivative is pulled back through the orthogonal
subspace inclusion. Its inherited rho-convexity is thus proved, rather than
added as a factorization premise.
-/
public section
namespace CutoffRigidity

theorem second_fderiv_comp_affine
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (L : F →L[ℝ] E) (m : E) (y h k : F) :
    fderiv ℝ (fderiv ℝ (fun z : F => V (L z+m))) y h k =
      fderiv ℝ (fderiv ℝ V) (L y+m) (L h) (L k) := by
  have hVd := hV.differentiable (by norm_num)
  have hfirst : fderiv ℝ (fun z : F => V (L z+m)) =
      fun z : F => (fderiv ℝ V (L z+m)).comp L := by
    funext z
    exact ((hVd (L z+m)).hasFDerivAt.comp z (L.hasFDerivAt.add_const m)).fderiv
  have hDf : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  have hd := ((hDf.differentiable one_ne_zero (L y+m)).hasFDerivAt.comp y
    (L.hasFDerivAt.add_const m)).clm_comp (hasFDerivAt_const L y)
  simp only [Function.comp_def] at hd
  rw [hfirst,hd.fderiv]
  simp

open MeasureTheory
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual complementary potential has the same source curvature lower
bound on its true orthogonal-complement Euclidean space. -/
theorem affineComplementPotential_hessian_lower
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (y z : (affineEigenRows V ρ)ᗮ) :
    ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ (affineComplementPotential V ρ)) y z z := by
  have hh := second_fderiv_comp_affine hV (affineEigenRows V ρ)ᗮ.subtypeL
    (affineSplittingCenter V) y z z
  change fderiv ℝ (fderiv ℝ (affineComplementPotential V ρ)) y z z =
    fderiv ℝ (fderiv ℝ V) ((y:E)+affineSplittingCenter V) (z:E) (z:E) at hh
  rw [hh]
  simpa only [Submodule.norm_coe] using hHess ((y:E)+affineSplittingCenter V) (z:E)

end CutoffRigidity
