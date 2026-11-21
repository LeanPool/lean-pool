/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.AffineRowsOrthonormalExtension
public import LeanPool.CutoffRigidity.AffineSubspaceGaussianProduct

/-! # The exact first-k orthonormal-coordinate potential formula

All affine directions occur among the first k vectors of one actual ambient
orthonormal basis. The remainder is the actual orthogonal-complement potential.
-/
public section
namespace CutoffRigidity
open MeasureTheory
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem affineEigenRows_projection_sum_sq (V : E → ℝ) (ρ : ℝ) (y : E) :
    (∑ i : Fin (Module.finrank ℝ (affineEigenRows V ρ)),
      (inner ℝ (affineEigenBasisRows V ρ i) y)^2) =
      ‖(affineEigenRows V ρ).orthogonalProjectionOnto y‖^2 := by
  have hh := (affineEigenRowsBasis V ρ).sum_sq_inner_right
    ((affineEigenRows V ρ).orthogonalProjectionOnto y)
  simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,affineEigenBasisRows] using hh

theorem potential_split_affine_orthogonal_coordinates
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (x : E) :
    V x = ρ/2*‖affineRowProjection V ρ x‖^2 +
      affineComplementPotential V ρ ((affineEigenRows V ρ)ᗮ.orthogonalProjectionOnto
        (x-affineSplittingCenter V)) := by
  let y := x-affineSplittingCenter V
  let U := affineEigenRows V ρ
  have hh := potential_split_affineEigenRows hV ρ hρ hHess hp
    (U.orthogonalProjectionOnto y) (Uᗮ.orthogonalProjectionOnto y)
  have hsum : (U.orthogonalProjectionOnto y : E)+(Uᗮ.orthogonalProjectionOnto y : E)=y := by
    exact U.starProjection_add_starProjection_orthogonal y
  rw [hsum] at hh
  have he : y+affineSplittingCenter V=x := sub_add_cancel _ _
  rw [he] at hh
  exact hh

/-- The literal ordered orthonormal-basis formula with every one of the k
Gaussian directions, rather than only a one-dimensional factor. -/
theorem exists_orthonormal_coordinates_full_affine_split
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) :
    ∃ e : OrthonormalBasis (Fin d) ℝ E,
      (∀ i : Fin (Module.finrank ℝ (affineEigenRows V ρ)),
        e (Fin.castLE (affineEigenRows_finrank_le V ρ) i)=affineEigenBasisRows V ρ i) ∧
      ∀ x : E, V x =
        ρ/2*(∑ i : Fin (Module.finrank ℝ (affineEigenRows V ρ)),
          (inner ℝ (e (Fin.castLE (affineEigenRows_finrank_le V ρ) i)) (x-affineSplittingCenter
            V))^2) +
        affineComplementPotential V ρ ((affineEigenRows V ρ)ᗮ.orthogonalProjectionOnto
          (x-affineSplittingCenter V)) := by
  obtain ⟨e,he⟩ := exists_orthonormalBasis_extending_affine_rows V ρ
  refine ⟨e,he,?_⟩
  intro x
  simp_rw [he]
  rw [affineEigenRows_projection_sum_sq]
  exact potential_split_affine_orthogonal_coordinates hV ρ hρ hHess hp x

end CutoffRigidity
