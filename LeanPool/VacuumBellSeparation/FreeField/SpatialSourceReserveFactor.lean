/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceCrossSeriesReconstruction
public import LeanPool.VacuumBellSeparation.FreeField.SpatialCrossCoefficientBounds
public import LeanPool.VacuumBellSeparation.Gaussian.CrossSeriesSummability

/-!
# The actual spatial reserve factor from weighted original moments

The actual scalar Taylor expansion, density of the original test pairs and
norm convergence now discharge the operator-series hypothesis. The only
analytic inputs left are weighted moment vectors representing the literal
polynomial functionals, and their norm-product summability.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification
open scoped ENNReal

variable {μ s R b : ℝ} (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R)
  (hsep : 8 * Real.sqrt 3 * R ≤ s) (hb : 0 ≤ b)
  {U W : Set (EuclideanSpace ℝ (Fin 3))}
  (hU : ∀ x ∈ U, ∀ j, ‖x j‖ ≤ R / 2)
  (hW : ∀ x ∈ W, ∀ j, ‖(x - spatialAxisDisplacement s 0) j‖ ≤ R / 2)

include hs hR hsep hU hW in
theorem hasSum_spatial_source_weighted_cross
    (u : SpatialCrossIndex → ComplexSourceHilbert hμ U)
    (v : SpatialCrossIndex → ComplexSourceHilbert hμ W)
    (hn : Summable fun i => ‖(spatialCrossCoefficient μ s R i : ℂ) • u i‖ * ‖v i‖)
    (hu : ∀ i (x : SourceTestSpace hμ U),
      inner ℂ (ofReal (x : SourceHilbert hμ U)) ((sourceReserve hμ U ^ b) (u i)) =
        (spatialCrossLeftMoment i x.1 : ℂ))
    (hv : ∀ i (y : SourceTestSpace hμ W),
      inner ℂ (ofReal (y : SourceHilbert hμ W)) ((sourceReserve hμ W ^ b) (v i)) =
        (spatialCrossRightMoment s i y.1 : ℂ)) :
    HasSum (fun i => crossRankOne
      ((sourceReserve hμ U ^ b) ((spatialCrossCoefficient μ s R i : ℂ) • u i))
      ((sourceReserve hμ W ^ b) (v i)))
      ((productSourceComplexEquiv hμ U W).conjStarAlgEquiv
        (complexify (productSourceCovariancePerturbation hμ U W))) := by
  apply hasSum_productSource_cross_of_test_moments hμ U W _ _
    (fun i x => spatialCrossCoefficient μ s R i * spatialCrossLeftMoment i x.1)
    (fun i y => spatialCrossRightMoment s i y.1)
    (summable_norm_product_map hn (sourceReserve hμ U ^ b) (sourceReserve hμ W ^ b))
  · intro i x
    rw [map_smul, inner_smul_right, hu, Complex.ofReal_mul]
  · exact hv
  · intro x y
    exact hasSum_localized_source_cross_index hμ hs hR hsep hU hW x y

include hs hR hsep hb hU hW in
/-- The actual full-source factor, with its true operator and nuclear norms.
No scalar or operator kernel expansion is supplied as an assumption. -/
theorem exists_spatial_source_reserve_factor
    (u : SpatialCrossIndex → ComplexSourceHilbert hμ U)
    (v : SpatialCrossIndex → ComplexSourceHilbert hμ W)
    (hn : Summable fun i => ‖(spatialCrossCoefficient μ s R i : ℂ) • u i‖ * ‖v i‖)
    (hu : ∀ i (x : SourceTestSpace hμ U),
      inner ℂ (ofReal (x : SourceHilbert hμ U)) ((sourceReserve hμ U ^ b) (u i)) =
        (spatialCrossLeftMoment i x.1 : ℂ))
    (hv : ∀ i (y : SourceTestSpace hμ W),
      inner ℂ (ofReal (y : SourceHilbert hμ W)) ((sourceReserve hμ W ^ b) (v i)) =
        (spatialCrossRightMoment s i y.1 : ℂ)) :
    ∃ Y : HilbertComplexification (WithLp 2 (SourceHilbert hμ U × SourceHilbert hμ W)) →L[ℂ]
        HilbertComplexification (WithLp 2 (SourceHilbert hμ U × SourceHilbert hμ W)),
      complexify (productSourceCovariancePerturbation hμ U W) =
        reserve (normalizedCommutation (complexify (productSourceCommutation hμ (UA := U)
          (UB := W)))) ^ b *
          Y * reserve (normalizedCommutation (complexify (productSourceCommutation hμ (UA := U)
            (UB := W)))) ^ b ∧
      IsCompactOperator Y ∧ IsSelfAdjoint Y ∧
      ‖Y‖ ≤ ∑' i, ‖(spatialCrossCoefficient μ s R i : ℂ) • u i‖ * ‖v i‖ ∧
      operatorTraceNorm Y ≤ ENNReal.ofReal
        (2 * ∑' i, ‖(spatialCrossCoefficient μ s R i : ℂ) • u i‖ * ‖v i‖) ∧
      operatorTraceNorm Y < ∞ := by
  exact exists_productSource_reserve_factor_of_cross_series hμ U W hb
    (fun i => (spatialCrossCoefficient μ s R i : ℂ) • u i) v hn
    (hasSum_spatial_source_weighted_cross hμ hs hR hsep hU hW u v hn hu hv)

end VacuumBellSeparation
