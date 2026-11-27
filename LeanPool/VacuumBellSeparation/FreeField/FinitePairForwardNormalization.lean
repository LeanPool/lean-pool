/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ProductSourceCovariancePerturbation

/-!
# Forward Gaussian normalization from the actual full source perturbation

All finite commutation and covariance compression identities are supplied
by the original canonical source construction. The only factorization
input is the full regional product operator D=R^b Y R^b.

Every declaration states its finite source data and Gaussian hypotheses as
explicit binders, with no section variables or local notation. Test builds
showed that the same Gaussian characteristic hypotheses, introduced as section
variables through `include`, exceed the heartbeat limit even in a trivial
application, while explicit binders
elaborate at once. The statements and
argument order of the public theorems are unchanged.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Gaussian Matrix
open scoped ENNReal InnerProductSpace Matrix.Norms.L2Operator

theorem canonicalPairProductCompression_covariance_perturbation
    {m : ℝ} (hm : 0 < m) {U W : Set (EuclideanSpace ℝ (Fin 3))}
    {S T : Submodule ℝ TimeZeroSource}
    (hUW : Disjoint U W) (hS : IsCanonicalSourceSystem U S)
    (hT : IsCanonicalSourceSystem W T) {d : ℕ}
    (c : Module.Basis (Fin d × Fin 2) ℝ (FiniteSourceSpace hm (S ⊔ T))) :
    compression (canonicalPairProductCompressionIsometry hm hUW hS hT c)
        (complexify (productSourceCovariancePerturbation hm U W)) =
      realMatrixOperator (relativeCovariancePerturbation
        (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm (S ⊔ T) c)
          (finiteSourceLabelSubspace hm (S ⊔ T) c S)
          (finiteSourceLabelSubspace hm (S ⊔ T) c T)
          (canonicalPairLabel_isCompl hm hUW hS hT c))
        (finiteSourceCovarianceMatrix hm (S ⊔ T) c -
          labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm (S ⊔ T) c)
            (finiteSourceLabelSubspace hm (S ⊔ T) c S)
            (finiteSourceLabelSubspace hm (S ⊔ T) c T)
            (canonicalPairLabel_isCompl hm hUW hS hT c))) :=
  finiteProductSourceCompression_covariance_perturbation hm U W (S ⊔ T) c _ _ _ _ _

/-- Keep covariance positivity in the finite real matrix interface, before
introducing density operators or the full completed source carrier. -/
private theorem canonicalPairProductCovariance_isHermitian
    {m : ℝ} (hm : 0 < m) {U W : Set (EuclideanSpace ℝ (Fin 3))}
    {S T : Submodule ℝ TimeZeroSource}
    (hUW : Disjoint U W) (hS : IsCanonicalSourceSystem U S)
    (hT : IsCanonicalSourceSystem W T) {d : ℕ}
    (c : Module.Basis (Fin d × Fin 2) ℝ (FiniteSourceSpace hm (S ⊔ T))) :
    Matrix.IsHermitian
      (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm (S ⊔ T) c)
        (finiteSourceLabelSubspace hm (S ⊔ T) c S)
        (finiteSourceLabelSubspace hm (S ⊔ T) c T)
        (canonicalPairLabel_isCompl hm hUW hS hT c)) :=
  (labelDecorrelatedCovariance_posDef (V := finiteSourceCovarianceMatrix hm (S ⊔ T) c)
    (finiteSourceCovarianceMatrix_posDef hm (S ⊔ T) c)
    (finiteSourceLabelSubspace hm (S ⊔ T) c S)
    (finiteSourceLabelSubspace hm (S ⊔ T) c T)
    (canonicalPairLabel_isCompl hm hUW hS hT c)).isHermitian

/-- The canonical physical compression, proved before any density operator
or normalized perturbation expression enters the elaboration context. -/
private theorem canonicalPairProductCompression_commutation_canonical
    {m : ℝ} (hm : 0 < m) {U W : Set (EuclideanSpace ℝ (Fin 3))}
    {S T : Submodule ℝ TimeZeroSource} [FiniteDimensional ℝ ↥(S ⊔ T)]
    (hUW : Disjoint U W) (hS : IsCanonicalSourceSystem U S)
    (hT : IsCanonicalSourceSystem W T) {d : ℕ}
    (c : Module.Basis (Fin d × Fin 2) ℝ (FiniteSourceSpace hm (S ⊔ T)))
    (hcanonical : finiteSourceSymplecticMatrix hm (S ⊔ T) c = modeSymplecticForm) :
    compression (canonicalPairProductCompressionIsometry hm hUW hS hT c)
        (normalizedCommutation (complexify (productSourceCommutation hm (UA := U) (UB := W)))) =
      (Matrix.toEuclideanCLM (n := Fin d × Fin 2) (𝕜 := ℂ))
        (covarianceCommutationMatrix
          (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm (S ⊔ T) c)
            (finiteSourceLabelSubspace hm (S ⊔ T) c S)
            (finiteSourceLabelSubspace hm (S ⊔ T) c T)
            (canonicalPairLabel_isCompl hm hUW hS hT c))
          modeSymplecticForm) :=
  (canonicalPairProductCompression_normalized_commutation hm hUW hS hT c).trans
    (congrArg
      (fun J : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℝ =>
        (Matrix.toEuclideanCLM (n := Fin d × Fin 2) (𝕜 := ℂ))
          (covarianceCommutationMatrix
            (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm (S ⊔ T) c)
              (finiteSourceLabelSubspace hm (S ⊔ T) c S)
              (finiteSourceLabelSubspace hm (S ⊔ T) c T)
              (canonicalPairLabel_isCompl hm hUW hS hT c)) J)) hcanonical)

/-- Exact comparison with the genuine compressed full-source perturbation. -/
theorem finitePair_forward_intrinsic_compression_norms
    {m : ℝ} (hm : 0 < m) {U W : Set (EuclideanSpace ℝ (Fin 3))}
    {S T : Submodule ℝ TimeZeroSource} [FiniteDimensional ℝ ↥(S ⊔ T)]
    (hUW : Disjoint U W) (hS : IsCanonicalSourceSystem U S)
    (hT : IsCanonicalSourceSystem W T) {d : ℕ}
    (c : Module.Basis (Fin d × Fin 2) ℝ (FiniteSourceSpace hm (S ⊔ T)))
    (hcanonical : finiteSourceSymplecticMatrix hm (S ⊔ T) c = modeSymplecticForm)
    {ρ σ : MultiModeOscillatorSpace d →L[ℂ] MultiModeOscillatorSpace d}
    (hσ : IsFaithfulDensity σ)
    (hGρ : HasGaussianPhysicalCharacteristic ρ (finiteSourceCovarianceMatrix hm (S ⊔ T) c))
    (hGσ : HasGaussianPhysicalCharacteristic σ
      (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm (S ⊔ T) c)
        (finiteSourceLabelSubspace hm (S ⊔ T) c S)
        (finiteSourceLabelSubspace hm (S ⊔ T) c T)
        (canonicalPairLabel_isCompl hm hUW hS hT c)))
    {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    ‖intrinsicGaussianRelativePerturbation ρ σ τ‖ =
        ‖normalizedReserveCompression (canonicalPairProductCompressionIsometry hm hUW hS hT c)
          (complexify (productSourceCovariancePerturbation hm U W)) (normalizedThermal τ
            (compression (canonicalPairProductCompressionIsometry hm hUW hS hT c)
              (normalizedCommutation
                (complexify (productSourceCommutation hm (UA := U) (UB := W))))))‖ ∧
      ENNReal.ofReal (matrixTraceNorm (intrinsicGaussianRelativePerturbation ρ σ τ)) =
        operatorTraceNorm
          (normalizedReserveCompression (canonicalPairProductCompressionIsometry hm hUW hS hT c)
            (complexify (productSourceCovariancePerturbation hm U W)) (normalizedThermal τ
              (compression (canonicalPairProductCompressionIsometry hm hUW hS hT c)
                (normalizedCommutation
                  (complexify (productSourceCommutation hm (UA := U) (UB := W))))))) :=
  intrinsicGaussianRelativePerturbation_compression_norms hσ
    (finiteSourceCovarianceMatrix_isHermitian hm (S ⊔ T) c)
    (canonicalPairProductCovariance_isHermitian hm hUW hS hT c) hGρ hGσ
    (canonicalPairProductCompressionIsometry hm hUW hS hT c)
    (canonicalPairProductCompression_commutation_canonical hm hUW hS hT c hcanonical)
    (canonicalPairProductCompression_covariance_perturbation hm hUW hS hT c).symm hτ₀ hτ₁

/-- A full reserve factorization gives both literal finite Gaussian norms,
without any finite model-identification premise. -/
theorem finitePair_forward_source_factorization_bounds
    {m : ℝ} (hm : 0 < m) {U W : Set (EuclideanSpace ℝ (Fin 3))}
    {S T : Submodule ℝ TimeZeroSource} [FiniteDimensional ℝ ↥(S ⊔ T)]
    (hUW : Disjoint U W) (hS : IsCanonicalSourceSystem U S)
    (hT : IsCanonicalSourceSystem W T) {d : ℕ}
    (c : Module.Basis (Fin d × Fin 2) ℝ (FiniteSourceSpace hm (S ⊔ T)))
    (hcanonical : finiteSourceSymplecticMatrix hm (S ⊔ T) c = modeSymplecticForm)
    {ρ σ : MultiModeOscillatorSpace d →L[ℂ] MultiModeOscillatorSpace d}
    (hσ : IsFaithfulDensity σ)
    (hGρ : HasGaussianPhysicalCharacteristic ρ (finiteSourceCovarianceMatrix hm (S ⊔ T) c))
    (hGσ : HasGaussianPhysicalCharacteristic σ
      (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm (S ⊔ T) c)
        (finiteSourceLabelSubspace hm (S ⊔ T) c S)
        (finiteSourceLabelSubspace hm (S ⊔ T) c T)
        (canonicalPairLabel_isCompl hm hUW hS hT c)))
    (n : ℕ)
    {Y : HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)) →L[ℂ]
      HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W))}
    (hfactor : complexify (productSourceCovariancePerturbation hm U W) =
      reserve (normalizedCommutation
          (complexify (productSourceCommutation hm (UA := U) (UB := W)))) ^
          (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) * Y *
        reserve (normalizedCommutation
          (complexify (productSourceCommutation hm (UA := U) (UB := W)))) ^
          (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)))
    (hcY : IsCompactOperator Y) (hY : IsSelfAdjoint Y) :
    let b : ℝ := ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)
    ‖intrinsicGaussianRelativePerturbation ρ σ b‖ ≤ (thermalConst b)⁻¹ * ‖Y‖ ∧
      ENNReal.ofReal (matrixTraceNorm (intrinsicGaussianRelativePerturbation ρ σ b)) ≤
        ENNReal.ofReal (thermalConst b)⁻¹ * operatorTraceNorm Y :=
  gaussian_high_source_factorization_bounds hσ
    (finiteSourceCovarianceMatrix_isHermitian hm (S ⊔ T) c)
    (canonicalPairProductCovariance_isHermitian hm hUW hS hT c) hGρ hGσ
    (canonicalPairProductCompressionIsometry hm hUW hS hT c)
    (productSource_normalizedCommutation_isSelfAdjoint hm)
    (productSource_normalizedCommutation_norm_le_one hm)
    (canonicalPairProductCompression_commutation_canonical hm hUW hS hT c hcanonical) n
    ((canonicalPairProductCompression_covariance_perturbation hm hUW hS hT c).symm.trans
      (congrArg
        (fun Z : HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W))
            →L[ℂ] HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)) =>
          compression (canonicalPairProductCompressionIsometry hm hUW hS hT c) Z)
        hfactor)) hcY hY

end VacuumBellSeparation
