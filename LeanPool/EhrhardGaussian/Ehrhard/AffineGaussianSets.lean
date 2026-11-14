/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.StandardSetInequality
public import LeanPool.EhrhardGaussian.Gaussian.Affine
import Mathlib.Analysis.Normed.Operator.Banach

/-! # Outer measures of convex sets under possibly singular affine Gaussian maps

Factoring through the linear range permits the use of open maps even when the covariance
is singular. No Borel measurability assumption on a convex set is needed.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open EhrhardGaussian.Gaussian
open scoped Topology Pointwise MatrixOrder Matrix.Norms.L2Operator

namespace EhrhardGaussian.Ehrhard

/-- Taking the closure preserves the measure of a set whose boundary is null. -/
theorem measure_closure_of_null_frontier {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] (μ : Measure E) {A : Set E} (hA : μ (frontier A) = 0) :
    μ (closure A) = μ A := by
  apply le_antisymm _ (measure_mono subset_closure)
  rw [closure_eq_self_union_frontier]
  exact (measure_union_le _ _).trans (by rw [hA, add_zero])

/-- A continuous open map evaluates a set by its preimage when the preimage boundary is null. -/
theorem map_apply_of_open_null_frontier {E F : Type*} [TopologicalSpace E]
    [TopologicalSpace F] [MeasurableSpace E] [MeasurableSpace F] [BorelSpace F]
    {μ : Measure E} {f : E → F} (hf : Continuous f) (hfm : Measurable f)
    (hopen : IsOpenMap f) (A : Set F) (hA : μ (frontier (f ⁻¹' A)) = 0) :
    μ.map f A = μ (f ⁻¹' A) := by
  refine le_antisymm ?_ (Measure.le_map_apply hfm.aemeasurable A)
  calc
    μ.map f A ≤ μ.map f (closure A) := measure_mono subset_closure
    _ = μ (f ⁻¹' closure A) := Measure.map_apply hfm isClosed_closure.measurableSet
    _ = μ (closure (f ⁻¹' A)) := by rw [hopen.preimage_closure_eq_closure_preimage hf]
    _ = μ (f ⁻¹' A) := measure_closure_of_null_frontier μ hA

/-- An affine image of standard Gaussian measure evaluates a convex set by its preimage. -/
theorem affine_standardGaussian_map_apply {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : (Fin n → ℝ) →L[ℝ] F) (m : F) {A : Set F} (hA : Convex ℝ A) :
    (standardGaussianMeasure n).map (fun x => m + L x) A =
      standardGaussianMeasure n ((fun x => m + L x) ⁻¹' A) := by
  let π := L.rangeRestrict
  let e : L.range → F := fun y => m + (y : F)
  have hπsurj : Function.Surjective π := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have he : MeasurableEmbedding e := by
    exact ((Homeomorph.addLeft m).isClosedEmbedding.comp
      L.range.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal).measurableEmbedding
  have hconv : Convex ℝ ((fun x => m + L x) ⁻¹' A) :=
    (hA.translate_preimage_right m).linear_preimage L.toLinearMap
  have hfront : standardGaussianMeasure n (frontier (π ⁻¹' (e ⁻¹' A))) = 0 :=
    standardGaussian_absolutelyContinuous n (hconv.addHaar_frontier volume)
  have hmap := map_apply_of_open_null_frontier π.continuous π.measurable
    (π.isOpenMap hπsurj) (e ⁻¹' A) hfront
  change (standardGaussianMeasure n).map (e ∘ π) A = _
  rw [← Measure.map_map he.measurable π.measurable]
  exact (he.map_apply _ A).trans hmap

/-- The linear part of the canonical Gaussian realization. -/
def gaussianLinearMap {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (gaussianCovarianceMatrix μ))).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap

/-- The affine Gaussian map is the sum of the mean and its linear part. -/
theorem gaussianAffineMap_eq {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    gaussianAffineMap μ = fun x => (∫ y, y ∂μ) + gaussianLinearMap μ x := rfl

/-- A Gaussian convex-set probability equals the standard Gaussian probability of its affine
preimage. -/
theorem gaussian_convex_preimage_measure {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : Convex ℝ A) :
    μ A = standardGaussianMeasure n (gaussianAffineMap μ ⁻¹' A) := by
  calc
    μ A = (standardGaussianMeasure n).map (gaussianAffineMap μ) A := by
      rw [(hasLaw_gaussianAffineMap μ).map_eq]
    _ = standardGaussianMeasure n (gaussianAffineMap μ ⁻¹' A) := by
      rw [gaussianAffineMap_eq]
      exact affine_standardGaussian_map_apply (gaussianLinearMap μ) _ hA

end EhrhardGaussian.Ehrhard

end
