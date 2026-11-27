/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteProductSourceCompression

/-!
# Source compression for an actual disjoint canonical pair

Both maps start from the same literal joint source basis. The reverse map
lands in the completed source space of the union. The forward map lands
in the actual product of the two regional source spaces. Localization,
complementarity and the vanishing symplectic cross form are derived from
the canonical source hypotheses and spatial disjointness.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Gaussian Matrix
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {m : ℝ} (hm : 0 < m)
  {U W : Set (EuclideanSpace ℝ (Fin 3))}
  {S T : Submodule ℝ TimeZeroSource} [FiniteDimensional ℝ ↥(S ⊔ T)]
  (hUW : Disjoint U W) (hS : IsCanonicalSourceSystem U S)
  (hT : IsCanonicalSourceSystem W T)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ (FiniteSourceSpace hm (S ⊔ T)))

include hUW hS hT in
omit [DecidableEq ι] [FiniteDimensional ℝ ↥(S ⊔ T)] in
theorem canonicalPairLabel_isCompl :
    IsCompl (finiteSourceLabelSubspace hm (S ⊔ T) b S)
      (finiteSourceLabelSubspace hm (S ⊔ T) b T) :=
  finiteSourceLabelSubspace_isCompl hm (S ⊔ T) b rfl
    (canonicalSourcePair_disjoint hUW hS hT)

include hS in
omit [DecidableEq ι] [FiniteDimensional ℝ ↥(S ⊔ T)] in
theorem canonicalPairLabel_left_localized {x : ι → ℝ}
    (hx : x ∈ finiteSourceLabelSubspace hm (S ⊔ T) b S) :
    finiteSourceCoordinates hm (S ⊔ T) b x ∈ localizedTimeZeroSources U :=
  hS.2.1 hx

include hT in
omit [DecidableEq ι] [FiniteDimensional ℝ ↥(S ⊔ T)] in
theorem canonicalPairLabel_right_localized {x : ι → ℝ}
    (hx : x ∈ finiteSourceLabelSubspace hm (S ⊔ T) b T) :
    finiteSourceCoordinates hm (S ⊔ T) b x ∈ localizedTimeZeroSources W :=
  hT.2.1 hx

include hUW hS hT in
omit [DecidableEq ι] in
theorem canonicalPairLabel_symplectic_cross {x y : ι → ℝ}
    (hx : x ∈ finiteSourceLabelSubspace hm (S ⊔ T) b S)
    (hy : y ∈ finiteSourceLabelSubspace hm (S ⊔ T) b T) :
    x ⬝ᵥ (finiteSourceSymplecticMatrix hm (S ⊔ T) b *ᵥ y) = 0 := by
  rw [← finiteSourceCoordinates_symplectic]
  exact canonicalSourcePair_cross hUW hS hT hx hy

omit [DecidableEq ι] [FiniteDimensional ℝ ↥(S ⊔ T)] [Fintype ι] in
theorem finiteSourceSymplecticMatrix_transpose :
    (finiteSourceSymplecticMatrix hm (S ⊔ T) b)ᵀ =
      -finiteSourceSymplecticMatrix hm (S ⊔ T) b := by
  ext i j
  exact timeZeroSymplectic_skew _ _

/-- The product reference uses the actual two regional completions. -/
def canonicalPairProductCompressionIsometry :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ]
      HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)) :=
  finiteProductSourceCompressionIsometry hm (S ⊔ T) b
    (finiteSourceLabelSubspace hm (S ⊔ T) b S)
    (finiteSourceLabelSubspace hm (S ⊔ T) b T)
    (canonicalPairLabel_isCompl hm hUW hS hT b)
    (fun _ hx => canonicalPairLabel_left_localized hm hS b hx)
    (fun _ hx => canonicalPairLabel_right_localized hm hT b hx)

theorem canonicalPairProductCompression_normalized_commutation :
    compression (canonicalPairProductCompressionIsometry hm hUW hS hT b)
        (normalizedCommutation (complexify (productSourceCommutation hm (UA := U) (UB := W)))) =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (covarianceCommutationMatrix
        (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm (S ⊔ T) b)
          (finiteSourceLabelSubspace hm (S ⊔ T) b S)
          (finiteSourceLabelSubspace hm (S ⊔ T) b T)
          (canonicalPairLabel_isCompl hm hUW hS hT b))
        (finiteSourceSymplecticMatrix hm (S ⊔ T) b)) :=
  finiteProductSourceCompression_normalized_commutation hm (S ⊔ T) b _ _ _ _ _
    (finiteSourceSymplecticMatrix_transpose hm b)
    (fun _ hx _ hy => canonicalPairLabel_symplectic_cross hm hUW hS hT b hx hy)

theorem productSource_normalizedCommutation_isSelfAdjoint :
    IsSelfAdjoint
      (normalizedCommutation (complexify (productSourceCommutation hm (UA := U) (UB := W)))) :=
  normalizedCommutation_isSelfAdjoint
    (complexify_mem_skewAdjoint (productSourceCommutation_mem_skewAdjoint hm))

theorem productSource_normalizedCommutation_norm_le_one :
    ‖normalizedCommutation (complexify (productSourceCommutation hm (UA := U) (UB := W)))‖ ≤ 1 := by
  apply norm_normalizedCommutation_le_one
  rw [norm_complexify]
  exact norm_productSourceCommutation_le_two hm

/-- The reverse comparison uses the joint source space in the union. -/
def canonicalPairJointCompressionIsometry :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] ComplexSourceHilbert hm (U ∪ W) :=
  finiteSourceCompressionIsometry hm (S ⊔ T) b
    (canonicalSourcePair_sup_isCanonical hUW hS hT).2.1

omit [FiniteDimensional ℝ ↥(S ⊔ T)] in
theorem canonicalPairJointCompression_normalized_commutation :
    compression (canonicalPairJointCompressionIsometry hm hUW hS hT b)
        (normalizedCommutation (complexSourceCommutation hm (U ∪ W))) =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (covarianceCommutationMatrix
        (finiteSourceCovarianceMatrix hm (S ⊔ T) b)
        (finiteSourceSymplecticMatrix hm (S ⊔ T) b)) :=
  finiteSourceCompression_normalized_commutation hm (S ⊔ T) b _

theorem canonicalPairProductCompression_thermal_weight {n : ℕ}
    (c : Module.Basis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm (S ⊔ T)))
    (hcanonical : finiteSourceSymplecticMatrix hm (S ⊔ T) c = modeSymplecticForm)
    {σ : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n}
    (hσ : IsFaithfulDensity σ)
    (hG : HasGaussianPhysicalCharacteristic σ
      (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm (S ⊔ T) c)
        (finiteSourceLabelSubspace hm (S ⊔ T) c S)
        (finiteSourceLabelSubspace hm (S ⊔ T) c T)
        (canonicalPairLabel_isCompl hm hUW hS hT c)))
    {τ : ℝ} (hτ : 0 < τ) :
    normalizedThermal τ
        (compression (canonicalPairProductCompressionIsometry hm hUW hS hT c)
          (normalizedCommutation (complexify (productSourceCommutation hm (UA := U) (UB := W))))) =
      realMatrixOperator (relativeCovariancePerturbation
        (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm (S ⊔ T) c)
          (finiteSourceLabelSubspace hm (S ⊔ T) c S)
          (finiteSourceLabelSubspace hm (S ⊔ T) c T)
          (canonicalPairLabel_isCompl hm hUW hS hT c)) (gaussianPowerIncrement σ τ)) := by
  rw [canonicalPairProductCompression_normalized_commutation, hcanonical]
  apply (gaussian_power_increment_operator_eq_normalizedThermal hσ _ hG hτ).symm
  exact (labelDecorrelatedCovariance_posDef
    (finiteSourceCovarianceMatrix_posDef hm (S ⊔ T) c) _ _ _).isHermitian

end VacuumBellSeparation
