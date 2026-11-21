/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.FirstEigenspaceAffineCoordinates

/-! # Full Euclidean Gaussian splitting at the actual spectral gap

This assembles the paper's Euclidean splitting theorem. The Gaussian factor
is the full affine eigen-row space, whose dimension is proved equal to that
of the actual first eigenspace. The complementary Euclidean space has
 dimension d-k. The ordered ambient orthonormal basis identifies these with
 the first k and remaining d-k coordinates. Independence comes from the
 actual Gibbs density and orthogonal change of variables, not from its
 Gaussian marginals.
-/
public section
namespace CutoffRigidity
open MeasureTheory
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The conclusions of the full Euclidean splitting theorem, using genuine
orthogonal Euclidean factors and the actual normalized Gibbs probability. -/
structure EuclideanGaussianSplitting (V : E → ℝ) (ρ : ℝ)
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V)) : Prop where
  dimension : Module.finrank ℝ (affineEigenRows V ρ) =
    Module.finrank ℝ (gibbsFirstEigenspace hV hp)
  positive_dimension : 0 < Module.finrank ℝ (affineEigenRows V ρ)
  dimension_le : Module.finrank ℝ (affineEigenRows V ρ) ≤ d
  complementary_dimension : Module.finrank ℝ (affineEigenRows V ρ)ᗮ =
    d-Module.finrank ℝ (gibbsFirstEigenspace hV hp)
  orthonormal_coordinates : ∃ e : OrthonormalBasis (Fin d) ℝ E,
    (∀ i : Fin (Module.finrank ℝ (affineEigenRows V ρ)),
      e (Fin.castLE (affineEigenRows_finrank_le V ρ) i)=affineEigenBasisRows V ρ i) ∧
    ∀ x : E, V x =
      ρ/2*(∑ i : Fin (Module.finrank ℝ (affineEigenRows V ρ)),
        (inner ℝ (e (Fin.castLE (affineEigenRows_finrank_le V ρ) i))
          (x-affineSplittingCenter V))^2) +
      affineComplementPotential V ρ
        ((affineEigenRows V ρ)ᗮ.orthogonalProjectionOnto (x-affineSplittingCenter V))
  complement_C2 : ContDiff ℝ 2 (affineComplementPotential V ρ)
  complement_curvature : ∀ y z : (affineEigenRows V ρ)ᗮ,
    ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ (affineComplementPotential V ρ)) y z z
  complement_probability : IsProbabilityMeasure (affineComplementLaw V ρ)
  product_probability : (gibbsMeasure volume V).map (affineSplittingCoordinates V ρ) =
    (affineRowGaussian V ρ).prod (affineComplementLaw V ρ)
  first_eigenclasses : ∀ u : gibbsFirstEigenspace hV hp,
    ∃ a : affineEigenRows V ρ,
      (u : E →₂[gibbsMeasure volume V] ℝ) =ᵐ[gibbsMeasure volume V]
        fun x => inner ℝ a (affineRowProjection V ρ x)

/-- Full-k Gaussian splitting from the source hypotheses. In particular,
the gap is the canonical actual spectral gap, and k is the dimension of
its genuine first eigenspace. No splitting or Gaussian-law premise occurs. -/
theorem euclidean_gaussian_splitting
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp=ρ) :
    EuclideanGaussianSplitting V ρ hV hp := by
  have hdim := firstEigenspace_finrank_eq_affine_rows hV hp ρ hρ hHess hgap
  obtain ⟨hprob,hprod⟩ := normalized_gibbs_affineSubspace_gaussian_product hV ρ hρ hHess hp
  exact {
    dimension := hdim.symm
    positive_dimension := by
      rw [← hdim]
      exact firstEigenspace_finrank_pos hV hp hd ρ hρ hHess hgap
    dimension_le := affineEigenRows_finrank_le V ρ
    complementary_dimension := by rw [hdim]; exact affineComplement_finrank_eq V ρ
    orthonormal_coordinates := exists_orthonormal_coordinates_full_affine_split hV ρ hρ hHess hp
    complement_C2 := contDiff_affineComplementPotential hV ρ
    complement_curvature := affineComplementPotential_hessian_lower hV ρ hHess
    complement_probability := hprob
    product_probability := hprod
    first_eigenclasses := firstEigenspace_depends_only_on_affine_projection hV hp ρ hρ hHess hgap }

end CutoffRigidity
