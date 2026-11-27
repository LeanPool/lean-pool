/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointFiniteCovarianceCompression
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianSourceCompressionBounds
public import LeanPool.VacuumBellSeparation.Gaussian.NuclearNormConvergence
public import LeanPool.VacuumBellSeparation.Constants.Parameters

/-!
# Reverse normalization from the actual joint source difference

The full operator is product covariance minus joint covariance. Whitening
uses the joint covariance, and the reference density in the reverse Rényi
comparison is the actual joint density. Both identities are constructed.

The finite source data and Gaussian hypotheses are explicit binders of each
theorem, with no section variables or local notation; Gaussian characteristic
hypotheses brought in as section variables through `include` exceed the
heartbeat limit (see `FinitePairForwardNormalization`). The statements and
argument order are unchanged.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian Matrix
open scoped ENNReal Matrix.Norms.L2Operator

theorem finite_reverse_source_factorization_bounds
    {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s)
    (S : Submodule ℝ TimeZeroSource)
    {d : ℕ} (c : Module.Basis (Fin d × Fin 2) ℝ (FiniteSourceSpace hμ S))
    (hSU : S ≤ localizedTimeZeroSources (jointSourceRegion s))
    (L R : Submodule ℝ (Fin d × Fin 2 → ℝ)) (hLR : IsCompl L R)
    (hLA : ∀ x ∈ L, finiteSourceCoordinates hμ S c x ∈
      localizedTimeZeroSources (Metric.ball (jointCenterIndex s 0) 1))
    (hRB : ∀ x ∈ R, finiteSourceCoordinates hμ S c x ∈
      localizedTimeZeroSources (Metric.ball (jointCenterIndex s 1) 1))
    (hcanonical : finiteSourceSymplecticMatrix hμ S c = modeSymplecticForm)
    {ρ σ : MultiModeOscillatorSpace d →L[ℂ] MultiModeOscillatorSpace d}
    (hρ : IsFaithfulDensity ρ)
    (hGρ : HasGaussianPhysicalCharacteristic ρ (finiteSourceCovarianceMatrix hμ S c))
    (hGσ : HasGaussianPhysicalCharacteristic σ
      (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hμ S c) L R hLR))
    {a : ℝ} (ha₀ : 0 < a) (ha₁ : a ≤ 1 / 2)
    {Y : ComplexSourceHilbert hμ (jointSourceRegion s) →L[ℂ]
      ComplexSourceHilbert hμ (jointSourceRegion s)}
    (hfactor : complexify (jointDifferenceKernelOperator hμ hs) =
      sourceReserve hμ (jointSourceRegion s) ^ a * Y * sourceReserve hμ (jointSourceRegion s) ^ a)
    (hcY : IsCompactOperator Y) (hY : IsSelfAdjoint Y) :
    ‖intrinsicGaussianRelativePerturbation σ ρ a‖ ≤ (thermalConst a)⁻¹ * ‖Y‖ ∧
      ENNReal.ofReal (matrixTraceNorm (intrinsicGaussianRelativePerturbation σ ρ a)) ≤
        ENNReal.ofReal (thermalConst a)⁻¹ * operatorTraceNorm Y := by
  have hcomp := finiteSourceCompression_normalized_commutation_canonical hμ S hSU c hcanonical
  have hD := (finiteSourceCompression_joint_difference hμ hs S c hSU L R hLR hLA hRB).symm
  rw [hfactor] at hD
  simp only [sourceReserve_eq_normalized_reserve] at hD
  exact gaussian_low_source_factorization_bounds hρ
    (labelDecorrelatedCovariance_posDef (finiteSourceCovarianceMatrix_posDef hμ S c) L R
      hLR).isHermitian
    (finiteSourceCovarianceMatrix_posDef hμ S c).isHermitian hGσ hGρ
    (finiteSourceCompressionIsometry hμ S c hSU)
    (normalizedCommutation_isSelfAdjoint (complexSourceCommutation_mem_skewAdjoint hμ _))
    (norm_normalizedCommutation_le_one (norm_complexSourceCommutation_le_two hμ _))
    hcomp ha₀ ha₁ hD hcY hY

/-- A single genuine nuclear bound controls both actual finite norms. -/
theorem finite_reverse_source_nuclear_bound
    {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s)
    (S : Submodule ℝ TimeZeroSource)
    {d : ℕ} (c : Module.Basis (Fin d × Fin 2) ℝ (FiniteSourceSpace hμ S))
    (hSU : S ≤ localizedTimeZeroSources (jointSourceRegion s))
    (L R : Submodule ℝ (Fin d × Fin 2 → ℝ)) (hLR : IsCompl L R)
    (hLA : ∀ x ∈ L, finiteSourceCoordinates hμ S c x ∈
      localizedTimeZeroSources (Metric.ball (jointCenterIndex s 0) 1))
    (hRB : ∀ x ∈ R, finiteSourceCoordinates hμ S c x ∈
      localizedTimeZeroSources (Metric.ball (jointCenterIndex s 1) 1))
    (hcanonical : finiteSourceSymplecticMatrix hμ S c = modeSymplecticForm)
    {ρ σ : MultiModeOscillatorSpace d →L[ℂ] MultiModeOscillatorSpace d}
    (hρ : IsFaithfulDensity ρ)
    (hGρ : HasGaussianPhysicalCharacteristic ρ (finiteSourceCovarianceMatrix hμ S c))
    (hGσ : HasGaussianPhysicalCharacteristic σ
      (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hμ S c) L R hLR))
    {a ε : ℝ} (ha₀ : 0 < a) (ha₁ : a ≤ 1 / 2) (hε : 0 ≤ ε)
    {Y : ComplexSourceHilbert hμ (jointSourceRegion s) →L[ℂ]
      ComplexSourceHilbert hμ (jointSourceRegion s)}
    (hfactor : complexify (jointDifferenceKernelOperator hμ hs) =
      sourceReserve hμ (jointSourceRegion s) ^ a * Y * sourceReserve hμ (jointSourceRegion s) ^ a)
    (hcY : IsCompactOperator Y) (hY : IsSelfAdjoint Y)
    (htrace : operatorTraceNorm Y ≤ ENNReal.ofReal ε) :
    ‖intrinsicGaussianRelativePerturbation σ ρ a‖ ≤ (thermalConst a)⁻¹ * ε ∧
      matrixTraceNorm (intrinsicGaussianRelativePerturbation σ ρ a) ≤ (thermalConst a)⁻¹ * ε := by
  have ha1 : a < 1 := by linarith
  have hc := thermalConst_pos ha₀ ha1
  have hnorm : ‖Y‖ ≤ ε := (ENNReal.ofReal_le_ofReal_iff hε).mp
    ((ofReal_norm_le_operatorTraceNorm Y).trans htrace)
  obtain ⟨hop, htr⟩ := finite_reverse_source_factorization_bounds hμ hs S c hSU L R hLR
    hLA hRB hcanonical hρ hGρ hGσ ha₀ ha₁ hfactor hcY hY
  refine ⟨hop.trans (mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hc.le)), ?_⟩
  have hh := htr.trans (_root_.mul_le_mul_right htrace (ENNReal.ofReal (thermalConst a)⁻¹))
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (inv_nonneg.mpr hc.le) hε)).mp hh

end VacuumBellSeparation
