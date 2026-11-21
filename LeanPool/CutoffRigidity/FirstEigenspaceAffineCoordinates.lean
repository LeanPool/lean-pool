/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.AffineSubspaceCoordinates
public import LeanPool.CutoffRigidity.GibbsFirstEigenspace

/-! # Actual first-eigenclass dimension and dependence on Gaussian coordinates

Weak Bochner rigidity supplies every affine representative. Its genuine
pointwise eigen-equation identifies its row in the constructed full Gaussian
subspace. Thus all actual first eigenclasses depend only on that first factor.
-/
public section
namespace CutoffRigidity
open MeasureTheory
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The dimension of the classical eigenspace equals the dimension of its gradient space. -/
theorem classicalL2Eigenspace_finrank_eq_rows {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Module.finrank ℝ (classicalL2Eigenspace V ρ) = Module.finrank ℝ (affineEigenRows V ρ) :=
  (classicalEigenRowsEquiv hV ρ hρ hHess hprob).finrank_eq

theorem firstEigenspace_finrank_eq_affine_rows
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp=ρ) :
    Module.finrank ℝ (gibbsFirstEigenspace hV hp)=Module.finrank ℝ (affineEigenRows V ρ) := by
  rw [firstEigenspace_finrank_eq_operator hV hp ρ hgap,
    operatorEigenspace_finrank_eq_classical hV hp ρ hρ hHess,
    classicalL2Eigenspace_finrank_eq_rows hV ρ hρ hHess hp]

theorem affineComplement_finrank_eq (V : E → ℝ) (ρ : ℝ) :
    Module.finrank ℝ (affineEigenRows V ρ)ᗮ=d-Module.finrank ℝ (affineEigenRows V ρ) := by
  have hh := (affineEigenRows V ρ).finrank_add_finrank_orthogonal
  simp only [finrank_euclideanSpace_fin] at hh
  omega

/-- Every actual first eigenclass has a genuine linear representative on
just the Gaussian factor, with no smoothness assumption on the eigenclass. -/
theorem firstEigenspace_depends_only_on_affine_projection
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp=ρ) (u : gibbsFirstEigenspace hV hp) :
    ∃ a : affineEigenRows V ρ,
      (u : E →₂[gibbsMeasure volume V] ℝ) =ᵐ[gibbsMeasure volume V]
        fun x => inner ℝ a (affineRowProjection V ρ x) := by
  have hu : (u : E →₂[gibbsMeasure volume V] ℝ) ∈ gibbsOperatorEigenspace hV hp ρ := by
    have hh := u.property
    change (u : E →₂[gibbsMeasure volume V] ℝ) ∈
      gibbsOperatorEigenspace hV hp (gibbsSpectralGap hV hp) at hh
    rwa [hgap] at hh
  let v : gibbsOperatorEigenspace hV hp ρ := ⟨u.val,hu⟩
  obtain ⟨a,b,hgrad,hrep⟩ := gibbsOperatorEigen_equalRate_affine_representative hV hp ρ hρ hHess v
  have heigen := gibbsOperatorEigen_affine_pointwise_equation hV hp ρ v a b hgrad hrep
  obtain ⟨ha,hb⟩ := (affineEigenRows_iff_eigenfunction V hρ a b).mp heigen
  let row : affineEigenRows V ρ := ⟨a,ha⟩
  refine ⟨row,?_⟩
  have hrepμ := (gibbsMeasure_absolutelyContinuous volume V).ae_eq hrep
  filter_upwards [hrepμ] with x hx
  rw [hx]
  change inner ℝ a x+b=inner ℝ row ((affineEigenRows V ρ).orthogonalProjectionOnto
    (x-affineSplittingCenter V))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,inner_sub_right,hb]
  have hc := affineEigenConstant_eq_neg_inner_mean hV ρ hρ hHess hp row
  rw [hc]
  rfl

end CutoffRigidity
