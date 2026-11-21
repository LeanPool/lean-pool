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
