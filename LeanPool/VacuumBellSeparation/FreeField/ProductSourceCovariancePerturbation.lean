/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FinitePairSourceCompression
public import LeanPool.VacuumBellSeparation.FreeField.SourceInclusion

/-!
# The actual product-source covariance perturbation

The sum of the two original source inclusions is a bounded map into the
joint completion. Its Gram minus the product identity is the full
off-diagonal covariance perturbation. Compression by the actual whitened
finite source family gives the literal normalized covariance difference.
No compactness, reserve factorization or spatial decay is asserted here.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Gaussian ContinuousLinearMap Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

variable {m : ℝ} (hm : 0 < m) (U W : Set (EuclideanSpace ℝ (Fin 3)))

/-- Continuous linear map for the product source sum, of type `WithLp 2 (SourceHilbert hm U ×
SourceHilbert hm W) →L[ℝ] SourceHilbert hm (U ∪ W)`. -/
def productSourceSum : WithLp 2 (SourceHilbert hm U × SourceHilbert hm W) →L[ℝ]
    SourceHilbert hm (U ∪ W) :=
  ((sourceInclusion hm (show U ⊆ U ∪ W from Set.subset_union_left)).toContinuousLinearMap.coprod
    (sourceInclusion hm (show W ⊆ U ∪ W from Set.subset_union_right)).toContinuousLinearMap).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ (SourceHilbert hm U)
        (SourceHilbert hm W)).toContinuousLinearMap

@[simp] theorem productSourceSum_apply (z : WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)) :
    productSourceSum hm U W z =
      sourceInclusion hm Set.subset_union_left z.fst +
        sourceInclusion hm Set.subset_union_right z.snd := rfl

theorem sourceEmbedding_productSourceSum
    (z : WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)) :
    sourceEmbedding hm (U ∪ W) (productSourceSum hm U W z) =
      sourceEmbedding hm U z.fst + sourceEmbedding hm W z.snd := by
  rw [productSourceSum_apply, map_add, sourceEmbedding_inclusion, sourceEmbedding_inclusion]

/-- This is the actual covariance Gram difference on the full product space. -/
def productSourceCovariancePerturbation :
    WithLp 2 (SourceHilbert hm U × SourceHilbert hm W) →L[ℝ]
      WithLp 2 (SourceHilbert hm U × SourceHilbert hm W) :=
  (productSourceSum hm U W).adjoint.comp (productSourceSum hm U W) - 1

theorem productSourceCovariancePerturbation_isSelfAdjoint :
    IsSelfAdjoint (productSourceCovariancePerturbation hm U W) := by
  change (productSourceCovariancePerturbation hm U W).adjoint = _
  simp only [productSourceCovariancePerturbation, map_sub, adjoint_comp,
    adjoint_adjoint, adjoint_one]

theorem complexify_productSourceCovariancePerturbation_isSelfAdjoint :
    IsSelfAdjoint (complexify (productSourceCovariancePerturbation hm U W)) := by
  change (complexify (productSourceCovariancePerturbation hm U W)).adjoint = _
  rw [complexify_adjoint, (productSourceCovariancePerturbation_isSelfAdjoint hm U W).adjoint_eq]

theorem inner_productSourceCovariancePerturbation
    (x y : WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)) :
    inner ℝ x (productSourceCovariancePerturbation hm U W y) =
      inner ℝ (sourceEmbedding hm U x.fst) (sourceEmbedding hm W y.snd) +
        inner ℝ (sourceEmbedding hm W x.snd) (sourceEmbedding hm U y.fst) := by
  rw [productSourceCovariancePerturbation, _root_.sub_apply, inner_sub_right,
    one_apply_eq_self, ContinuousLinearMap.comp_apply, adjoint_inner_right,
    ← (sourceEmbedding hm (U ∪ W)).inner_map_map,
    sourceEmbedding_productSourceSum, sourceEmbedding_productSourceSum,
    inner_add_left, inner_add_right, inner_add_right,
    (sourceEmbedding hm U).inner_map_map, (sourceEmbedding hm W).inner_map_map,
    WithLp.prod_inner_apply]
  dsimp only [WithLp.fst, WithLp.snd]
  ring

variable (S : Submodule ℝ TimeZeroSource)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ (FiniteSourceSpace hm S))
  (L R : Submodule ℝ (ι → ℝ)) (hLR : IsCompl L R)
  (hLA : ∀ x ∈ L, finiteSourceCoordinates hm S b x ∈ localizedTimeZeroSources U)
  (hRB : ∀ x ∈ R, finiteSourceCoordinates hm S b x ∈ localizedTimeZeroSources W)

theorem productSourceSum_finiteFamily_physical (i : ι) :
    sourceEmbedding hm (U ∪ W)
        (productSourceSum hm U W (finiteProductSourceFamily hm S b L R hLR hLA hRB i)) =
      timeZeroL2 hm (finiteSourceCoordinates hm S b (Pi.single i 1)) := by
  rw [sourceEmbedding_productSourceSum]
  change sourceEmbedding hm U (projectedFiniteSourceTest hm S b L R hLR hLA i : SourceHilbert hm
    U) +
    sourceEmbedding hm W (projectedFiniteSourceTest hm S b R L hLR.symm hRB i : SourceHilbert hm
      W) = _
  rw [sourceEmbedding_coe, sourceEmbedding_coe]
  change timeZeroL2 hm (finiteSourceCoordinates hm S b (L.projection R hLR (Pi.single i 1))) +
    timeZeroL2 hm (finiteSourceCoordinates hm S b (R.projection L hLR.symm (Pi.single i 1))) = _
  rw [← timeZeroL2_add, ← map_add]
  congr 2
  exact DFunLike.congr_fun (Submodule.projection_add_projection_eq_id hLR) (Pi.single i 1)

theorem productSourceSum_finiteFamily_gram :
    realFamilyGram (fun i => productSourceSum hm U W
      (finiteProductSourceFamily hm S b L R hLR hLA hRB i)) =
        finiteSourceCovarianceMatrix hm S b := by
  have hreal (u v : TimeZeroSource) :
      inner ℝ (timeZeroL2 hm u) (timeZeroL2 hm v) = timeZeroFourierCovariance m u v := by
    have hre : inner ℝ (timeZeroL2 hm u) (timeZeroL2 hm v) =
        (inner ℂ (timeZeroL2 hm u) (timeZeroL2 hm v)).re := by
      rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
      calc
        _ = ∫ p, RCLike.re (inner ℂ ((timeZeroL2 hm u) p) ((timeZeroL2 hm v) p))
            ∂oneParticleMeasure m := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun p => by
            simp only [Complex.inner, RCLike.inner_apply]
            rfl
        _ = _ := integral_re
          (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (timeZeroL2 hm u) (timeZeroL2 hm v))
    rw [hre, inner_timeZeroL2_gram]
    simp [Complex.mul_re]
  ext i j
  change inner ℝ
    (productSourceSum hm U W (finiteProductSourceFamily hm S b L R hLR hLA hRB i))
    (productSourceSum hm U W (finiteProductSourceFamily hm S b L R hLR hLA hRB j)) = _
  rw [← (sourceEmbedding hm (U ∪ W)).inner_map_map,
    productSourceSum_finiteFamily_physical, productSourceSum_finiteFamily_physical,
    hreal, finiteSourceCoordinates_covariance]
  simp only [single_one_dotProduct, Matrix.mulVec_single_one, Matrix.col_apply]

theorem finiteProductSourceFamily_covariance_perturbation_form :
    realFamilyForm (finiteProductSourceFamily hm S b L R hLR hLA hRB)
        (productSourceCovariancePerturbation hm U W) =
      finiteSourceCovarianceMatrix hm S b -
        labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm S b) L R hLR := by
  ext i j
  change inner ℝ (finiteProductSourceFamily hm S b L R hLR hLA hRB i)
    (((productSourceSum hm U W).adjoint.comp (productSourceSum hm U W) - 1)
      (finiteProductSourceFamily hm S b L R hLR hLA hRB j)) = _
  rw [_root_.sub_apply, inner_sub_right, ContinuousLinearMap.comp_apply, adjoint_inner_right,
    one_apply_eq_self]
  change realFamilyGram (fun i => productSourceSum hm U W
      (finiteProductSourceFamily hm S b L R hLR hLA hRB i)) i j -
    realFamilyGram (finiteProductSourceFamily hm S b L R hLR hLA hRB) i j = _
  rw [productSourceSum_finiteFamily_gram, finiteProductSourceFamily_gram]; rfl

/-- The desired finite perturbation is a proved compression of the actual
full product Gram difference, prior to any reserve estimate. -/
theorem finiteProductSourceCompression_covariance_perturbation :
    compression (finiteProductSourceCompressionIsometry hm S b L R hLR hLA hRB)
        (complexify (productSourceCovariancePerturbation hm U W)) =
      realMatrixOperator (relativeCovariancePerturbation
        (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm S b) L R hLR)
        (finiteSourceCovarianceMatrix hm S b -
          labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm S b) L R hLR)) := by
  have h := compression_whitened_complexify
    (finiteProductSourceFamily hm S b L R hLR hLA hRB)
    (finiteProductSourceFamily_linearIndependent hm S b L R hLR hLA hRB)
    (productSourceCovariancePerturbation hm U W)
  rw [finiteProductSourceFamily_gram, finiteProductSourceFamily_covariance_perturbation_form] at h
  exact h

end VacuumBellSeparation
