/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.AffineSubspaceGaussian
public import LeanPool.CutoffRigidity.AffineComplementCurvature
public import LeanPool.CutoffRigidity.OrthogonalGibbsProduct

/-! # The genuine full Gaussian product factor in orthogonal coordinates

The full affine eigen-row space and its orthogonal complement provide
actual orthogonal affine coordinates centered at the Gibbs mean. The exact
potential identity implies independence. The previously proved Gaussian
projection law then identifies the full first probability factor.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The row-space and complementary coordinates of a point centered at the Gibbs barycenter. -/
@[expose] noncomputable def affineSplittingCoordinates (V : E → ℝ) (ρ : ℝ) (x : E) :
    affineEigenRows V ρ × (affineEigenRows V ρ)ᗮ :=
  ((affineEigenRows V ρ).orthogonalDecomposition (x-affineSplittingCenter V)).ofLp

/-- The complementary marginal of the Gibbs law in the centered splitting coordinates. -/
@[expose] noncomputable def affineComplementLaw (V : E → ℝ) (ρ : ℝ) : Measure (affineEigenRows V
  ρ)ᗮ :=
  ((gibbsMeasure volume V).map (affineSplittingCoordinates V ρ)).map Prod.snd

theorem measurable_affineSplittingCoordinates (V : E → ℝ) (ρ : ℝ) :
    Measurable (affineSplittingCoordinates V ρ) := by
  unfold affineSplittingCoordinates
  fun_prop

/-- Actual normalized full-dimensional Gaussian independence, with the
Gaussian directions constructed from all genuine affine eigenfunctions. -/
theorem normalized_gibbs_affineSubspace_gaussian_product
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) :
    IsProbabilityMeasure (affineComplementLaw V ρ) ∧
      (gibbsMeasure volume V).map (affineSplittingCoordinates V ρ) =
        (affineRowGaussian V ρ).prod (affineComplementLaw V ρ) := by
  let μ := gibbsMeasure volume V
  let A := (affineEigenRows V ρ).orthogonalDecomposition
  have hcoords := measurable_affineSplittingCoordinates V ρ
  have hprod := normalized_separated_gibbs_map_product_marginals A V hV.continuous.measurable
    (affineSplittingCenter V) (fun z : affineEigenRows V ρ => ρ/2*‖z‖^2) (by fun_prop)
    (affineComplementPotential V ρ) (contDiff_affineComplementPotential hV ρ).continuous.measurable
    (by
      intro v w
      simpa only [A,Submodule.orthogonalDecomposition_symm_apply,WithLp.toLp_fst,WithLp.toLp_snd]
        using
        potential_split_affineEigenRows hV ρ hρ hHess hp v w) hp
  change μ.map (affineSplittingCoordinates V ρ) =
    ((μ.map (affineSplittingCoordinates V ρ)).map Prod.fst).prod
      ((μ.map (affineSplittingCoordinates V ρ)).map Prod.snd) at hprod
  have hfirst : (μ.map (affineSplittingCoordinates V ρ)).map Prod.fst=affineRowGaussian V ρ := by
    rw [Measure.map_map measurable_fst hcoords]
    convert! (affineRowProjection_hasLaw_gaussian hV ρ hρ hHess hp).map_eq using 1
  have hprob : IsProbabilityMeasure (μ.map (affineSplittingCoordinates V ρ)) :=
    (Measure.isProbabilityMeasure_map_iff hcoords.aemeasurable).mpr hp
  have hsecond : IsProbabilityMeasure (affineComplementLaw V ρ) :=
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).mpr hprob
  refine ⟨hsecond,?_⟩
  rw [hfirst] at hprod
  exact hprod

end CutoffRigidity
