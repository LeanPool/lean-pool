/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteSourceCompressionBridge
public import LeanPool.VacuumBellSeparation.FreeField.FiniteSourcePairCoordinates
public import LeanPool.VacuumBellSeparation.Gaussian.HilbertProductOperator
public import LeanPool.VacuumBellSeparation.Gaussian.ComplementaryLabelCovariance

/-!
# Actual product-source coordinates for the decorrelated finite covariance

The two projections of each original basis label are literal test sources
in their respective regions. Their pair lies in the genuine L2 product
of the two completed real source spaces. Its Gram is the decorrelated
covariance, and its componentwise source commutation form is the original
symplectic form when the two regional symplectic cross blocks vanish.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Gaussian Matrix
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {m : ℝ} (hm : 0 < m)

theorem sourceHilbert_test_inner_covariance
    {U : Set (EuclideanSpace ℝ (Fin 3))} (u v : SourceTestSpace hm U) :
    inner ℝ (u : SourceHilbert hm U) (v : SourceHilbert hm U) =
      timeZeroFourierCovariance m u.1 v.1 := by
  have hreal : inner ℝ (timeZeroL2 hm u.1) (timeZeroL2 hm v.1) =
      (inner ℂ (timeZeroL2 hm u.1) (timeZeroL2 hm v.1)).re := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    calc
      _ = ∫ p, RCLike.re (inner ℂ ((timeZeroL2 hm u.1) p) ((timeZeroL2 hm v.1) p))
          ∂oneParticleMeasure m := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          simp only [Complex.inner, RCLike.inner_apply]
          rfl
      _ = _ := integral_re
        (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (timeZeroL2 hm u.1) (timeZeroL2 hm v.1))
  calc
    _ = inner ℝ (sourceEmbedding hm U (u : SourceHilbert hm U))
        (sourceEmbedding hm U (v : SourceHilbert hm U)) :=
      ((sourceEmbedding hm U).inner_map_map _ _).symm
    _ = inner ℝ (timeZeroL2 hm u.1) (timeZeroL2 hm v.1) :=
      congrArg₂ (inner ℝ) (sourceEmbedding_coe hm U u) (sourceEmbedding_coe hm U v)
    _ = _ := by
      rw [hreal, inner_timeZeroL2_gram]
      simp [Complex.mul_re]

variable (S : Submodule ℝ TimeZeroSource)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ (FiniteSourceSpace hm S))
  (L R : Submodule ℝ (ι → ℝ)) (hLR : IsCompl L R)
  {UA UB : Set (EuclideanSpace ℝ (Fin 3))}
  (hLA : ∀ x ∈ L, finiteSourceCoordinates hm S b x ∈ localizedTimeZeroSources UA)
  (hRB : ∀ x ∈ R, finiteSourceCoordinates hm S b x ∈ localizedTimeZeroSources UB)

/-- Projected finite source test. -/
def projectedFiniteSourceTest (i : ι) : SourceTestSpace hm UA :=
  ⟨finiteSourceCoordinates hm S b (L.projection R hLR (Pi.single i 1)),
    hLA _ (Submodule.projection_apply_mem hLR _)⟩

/-- Finite product source family. -/
def finiteProductSourceFamily (i : ι) :
    WithLp 2 (SourceHilbert hm UA × SourceHilbert hm UB) :=
  WithLp.toLp 2
    ((projectedFiniteSourceTest hm S b L R hLR hLA i : SourceHilbert hm UA),
      (projectedFiniteSourceTest hm S b R L hLR.symm hRB i : SourceHilbert hm UB))

theorem finiteProductSourceFamily_gram :
    realFamilyGram (finiteProductSourceFamily hm S b L R hLR hLA hRB) =
      labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm S b) L R hLR := by
  ext i j
  change inner ℝ (finiteProductSourceFamily hm S b L R hLR hLA hRB i)
    (finiteProductSourceFamily hm S b L R hLR hLA hRB j) = _
  rw [finiteProductSourceFamily, finiteProductSourceFamily, WithLp.prod_inner_apply]
  change inner ℝ (projectedFiniteSourceTest hm S b L R hLR hLA i : SourceHilbert hm UA)
      (projectedFiniteSourceTest hm S b L R hLR hLA j : SourceHilbert hm UA) +
    inner ℝ (projectedFiniteSourceTest hm S b R L hLR.symm hRB i : SourceHilbert hm UB)
      (projectedFiniteSourceTest hm S b R L hLR.symm hRB j : SourceHilbert hm UB) = _
  rw [sourceHilbert_test_inner_covariance, sourceHilbert_test_inner_covariance]
  change timeZeroFourierCovariance m
      (finiteSourceCoordinates hm S b (L.projection R hLR (Pi.single i 1)))
      (finiteSourceCoordinates hm S b (L.projection R hLR (Pi.single j 1))) +
    timeZeroFourierCovariance m
      (finiteSourceCoordinates hm S b (R.projection L hLR.symm (Pi.single i 1)))
      (finiteSourceCoordinates hm S b (R.projection L hLR.symm (Pi.single j 1))) = _
  rw [finiteSourceCoordinates_covariance, finiteSourceCoordinates_covariance,
    ← complementaryLabelProjection_mulVec L R hLR,
    ← complementaryLabelProjection_mulVec L R hLR,
    ← complementaryLabelProjection_mulVec R L hLR.symm,
    ← complementaryLabelProjection_mulVec R L hLR.symm,
    bilinear_mixed_congruence, bilinear_mixed_congruence]
  simp only [single_one_dotProduct, Matrix.mulVec_single_one,
    labelDecorrelatedCovariance, decorrelatedCovariance, Matrix.add_apply, Matrix.col,
      Matrix.transpose_apply]

theorem finiteProductSourceFamily_linearIndependent :
    LinearIndependent ℝ (finiteProductSourceFamily hm S b L R hLR hLA hRB) := by
  apply Matrix.linearIndependent_of_posDef_gram
  change (realFamilyGram (finiteProductSourceFamily hm S b L R hLR hLA hRB)).PosDef
  rw [finiteProductSourceFamily_gram]
  exact labelDecorrelatedCovariance_posDef (finiteSourceCovarianceMatrix_posDef hm S b) L R hLR

/-- Product source commutation defined as `realHilbertProductOperator (sourceCommutation hm UA)
(sourceCommutation hm UB)`. -/
def productSourceCommutation :
    WithLp 2 (SourceHilbert hm UA × SourceHilbert hm UB) →L[ℝ]
      WithLp 2 (SourceHilbert hm UA × SourceHilbert hm UB) :=
  realHilbertProductOperator (sourceCommutation hm UA) (sourceCommutation hm UB)

theorem productSourceCommutation_mem_skewAdjoint :
    productSourceCommutation hm (UA := UA) (UB := UB) ∈ skewAdjoint
      (WithLp 2 (SourceHilbert hm UA × SourceHilbert hm UB) →L[ℝ]
        WithLp 2 (SourceHilbert hm UA × SourceHilbert hm UB)) :=
  realHilbertProductOperator_mem_skewAdjoint
    (sourceCommutation_mem_skewAdjoint hm UA) (sourceCommutation_mem_skewAdjoint hm UB)

theorem norm_productSourceCommutation_le_two :
    ‖productSourceCommutation hm (UA := UA) (UB := UB)‖ ≤ 2 :=
  norm_realHilbertProductOperator_le _ _ (by norm_num)
    (norm_sourceCommutation_le_two hm UA) (norm_sourceCommutation_le_two hm UB)

theorem finiteProductSourceFamily_commutation_form [FiniteDimensional ℝ S] :
    realFamilyForm (finiteProductSourceFamily hm S b L R hLR hLA hRB)
        (productSourceCommutation hm) =
      labelDecorrelatedCovariance (finiteSourceSymplecticMatrix hm S b) L R hLR := by
  ext i j
  change inner ℝ (finiteProductSourceFamily hm S b L R hLR hLA hRB i)
    (realHilbertProductOperator (sourceCommutation hm UA) (sourceCommutation hm UB)
      (finiteProductSourceFamily hm S b L R hLR hLA hRB j)) = _
  rw [realHilbertProductOperator_apply, finiteProductSourceFamily, WithLp.prod_inner_apply]
  change inner ℝ (projectedFiniteSourceTest hm S b L R hLR hLA i : SourceHilbert hm UA)
      (sourceCommutation hm UA (projectedFiniteSourceTest hm S b L R hLR hLA j : SourceHilbert
        hm UA)) +
    inner ℝ (projectedFiniteSourceTest hm S b R L hLR.symm hRB i : SourceHilbert hm UB)
      (sourceCommutation hm UB
        (projectedFiniteSourceTest hm S b R L hLR.symm hRB j : SourceHilbert hm UB)) = _
  rw [sourceCommutation_symplectic, sourceCommutation_symplectic]
  change timeZeroSymplectic
      (finiteSourceCoordinates hm S b (L.projection R hLR (Pi.single i 1)))
      (finiteSourceCoordinates hm S b (L.projection R hLR (Pi.single j 1))) +
    timeZeroSymplectic
      (finiteSourceCoordinates hm S b (R.projection L hLR.symm (Pi.single i 1)))
      (finiteSourceCoordinates hm S b (R.projection L hLR.symm (Pi.single j 1))) = _
  rw [finiteSourceCoordinates_symplectic, finiteSourceCoordinates_symplectic,
    ← complementaryLabelProjection_mulVec L R hLR,
    ← complementaryLabelProjection_mulVec L R hLR,
    ← complementaryLabelProjection_mulVec R L hLR.symm,
    ← complementaryLabelProjection_mulVec R L hLR.symm,
    bilinear_mixed_congruence, bilinear_mixed_congruence]
  simp only [single_one_dotProduct, Matrix.mulVec_single_one,
    labelDecorrelatedCovariance, decorrelatedCovariance, Matrix.add_apply, Matrix.col,
      Matrix.transpose_apply]

/-- Finite product source compression isometry. -/
def finiteProductSourceCompressionIsometry :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ]
      HilbertComplexification (WithLp 2 (SourceHilbert hm UA × SourceHilbert hm UB)) :=
  whitenedComplexFamily (finiteProductSourceFamily hm S b L R hLR hLA hRB)
    (finiteProductSourceFamily_linearIndependent hm S b L R hLR hLA hRB)

theorem finiteProductSourceCompression_normalized_commutation [FiniteDimensional ℝ S]
    (hskew : (finiteSourceSymplecticMatrix hm S b)ᵀ = -finiteSourceSymplecticMatrix hm S b)
    (hcross : ∀ x ∈ L, ∀ y ∈ R, x ⬝ᵥ (finiteSourceSymplecticMatrix hm S b *ᵥ y) = 0) :
    compression (finiteProductSourceCompressionIsometry hm S b L R hLR hLA hRB)
        (normalizedCommutation (complexify (productSourceCommutation hm))) =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (covarianceCommutationMatrix
        (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm S b) L R hLR)
        (finiteSourceSymplecticMatrix hm S b)) := by
  have h := compression_whitened_normalizedCommutation
    (finiteProductSourceFamily hm S b L R hLR hLA hRB)
    (finiteProductSourceFamily_linearIndependent hm S b L R hLR hLA hRB)
    (productSourceCommutation hm)
  rw [finiteProductSourceFamily_gram, finiteProductSourceFamily_commutation_form] at h
  have hc := complementaryLabelProjection_cross_zero L R hLR
    (finiteSourceSymplecticMatrix hm S b) hcross
  have hd : labelDecorrelatedCovariance (finiteSourceSymplecticMatrix hm S b) L R hLR =
      finiteSourceSymplecticMatrix hm S b :=
    complementary_symplectic_diagonal (complementaryLabelProjection_add L R hLR)
      hc (transpose_cross_zero_of_skew hskew hc)
  rw [hd] at h
  exact h

end VacuumBellSeparation
