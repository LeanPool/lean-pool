/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelProduct
public import LeanPool.VacuumBellSeparation.FreeField.JointDispersionComparison
public import LeanPool.VacuumBellSeparation.FreeField.SourceSpace

/-!
# Actual joint-source control of the product-test Fourier weights

All energies use the original physical Fourier transform with its exact
normalization. The estimates concern the total real test pair on the union,
and hence require neither a regional decomposition nor a synthesis inverse.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MeasureTheory FourierTransform Set
open scoped SchwartzMap FourierTransform ComplexConjugate

/-- Joint field energy given by `((2 * Real.pi) ^ 3)⁻¹ * ∫ p, (dispersion μ p)⁻¹ * ‖spatialFourier
f p‖ ^ 2`. -/
def jointFieldEnergy (μ : ℝ) (f : SpatialTestFunction) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, (dispersion μ p)⁻¹ * ‖spatialFourier f p‖ ^ 2

/-- Joint momentum energy given by `((2 * Real.pi) ^ 3)⁻¹ * ∫ p, dispersion μ p * ‖spatialFourier g
p‖ ^ 2`. -/
def jointMomentumEnergy (μ : ℝ) (g : SpatialTestFunction) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, dispersion μ p * ‖spatialFourier g p‖ ^ 2

theorem jointFieldEnergy_nonneg (μ : ℝ) (f : SpatialTestFunction) :
    0 ≤ jointFieldEnergy μ f := by unfold jointFieldEnergy dispersion; positivity

theorem jointMomentumEnergy_nonneg (μ : ℝ) (g : SpatialTestFunction) :
    0 ≤ jointMomentumEnergy μ g := by unfold jointMomentumEnergy dispersion; positivity

theorem timeZeroFourierCovariance_self_eq_jointEnergies (μ : ℝ) (u : TimeZeroSource) :
    timeZeroFourierCovariance μ u u =
      (jointFieldEnergy μ u.1 + jointMomentumEnergy μ u.2) / 2 := by
  have hi (f : SpatialTestFunction) (w : EuclideanSpace ℝ (Fin 3) → ℝ) :
      (∫ p, (conj (spatialFourier f p) * spatialFourier f p) * (w p : ℂ)) =
        ((∫ p, w p * ‖spatialFourier f p‖ ^ 2 : ℝ) : ℂ) := by
    have he (p : EuclideanSpace ℝ (Fin 3)) :
        (conj (spatialFourier f p) * spatialFourier f p) * (w p : ℂ) =
          ((w p * ‖spatialFourier f p‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']
      push_cast
      ring
    simp_rw [he]
    exact integral_ofReal
  unfold timeZeroFourierCovariance timeZeroFourierDiagonal
  rw [hi, hi]
  simp only [← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re,
    jointFieldEnergy, jointMomentumEnergy, div_eq_mul_inv, mul_inv_rev]
  ring

theorem jointFieldEnergy_le_sourceTest_norm_sq {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (u : SourceTestSpace hμ U) :
    jointFieldEnergy μ u.1.1 ≤ 2 * ‖u‖ ^ 2 := by
  rw [sourceTestSpace_norm_sq, timeZeroFourierCovariance_self_eq_jointEnergies]
  have h := jointMomentumEnergy_nonneg μ u.1.2
  linarith

theorem jointMomentumEnergy_le_sourceTest_norm_sq {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (u : SourceTestSpace hμ U) :
    jointMomentumEnergy μ u.1.2 ≤ 2 * ‖u‖ ^ 2 := by
  rw [sourceTestSpace_norm_sq, timeZeroFourierCovariance_self_eq_jointEnergies]
  have h := jointFieldEnergy_nonneg μ u.1.1
  linarith

theorem jointTestFrequencyWeight_le_inverse_dispersion (p : EuclideanSpace ℝ (Fin 3)) :
    jointTestFrequencyWeight p ≤ (dispersion 1 ((2 * Real.pi) • p))⁻¹ := by
  have hd : 1 ≤ dispersion 1 ((2 * Real.pi) • p) := le_dispersion (by norm_num) _
  have he : dispersion 1 ((2 * Real.pi) • p) ^ 2 =
      1 + (2 * Real.pi) ^ 2 * ‖p‖ ^ 2 := by
    rw [dispersion_sq, norm_smul, Real.norm_of_nonneg (by positivity), mul_pow]
    norm_num
  unfold jointTestFrequencyWeight
  apply inv_anti₀ (by linarith : 0 < dispersion 1 ((2 * Real.pi) • p))
  nlinarith

theorem normalized_inverse_dispersion_energy (μ : ℝ) (f : SpatialTestFunction) :
    (∫ p, (dispersion μ ((2 * Real.pi) • p))⁻¹ * ‖(𝓕 (spatialSchwartz f)) p‖ ^ 2) =
      jointFieldEnergy μ f := by
  have h := Measure.integral_comp_smul volume
    (fun p => (dispersion μ p)⁻¹ * ‖spatialFourier f p‖ ^ 2) (2 * Real.pi)
  rw [finrank_momentum, abs_of_pos (by positivity : 0 < ((2 * Real.pi) ^ 3)⁻¹)] at h
  simpa only [spatialFourier_two_pi, smul_eq_mul, jointFieldEnergy] using h

theorem integral_jointTestWeight_le_fieldEnergy {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialTestFunction) :
    (∫ p, jointTestFrequencyWeight p * ‖(𝓕 (spatialSchwartz f)) p‖ ^ 2) ≤
      max 1 μ * jointFieldEnergy μ f := by
  have hi : Integrable (fun p => (dispersion 1 ((2 * Real.pi) • p))⁻¹ *
      ‖(𝓕 (spatialSchwartz f)) p‖ ^ 2) := by
    have h := (integrable_comp_smul_iff volume
      (fun p => (dispersion 1 p)⁻¹ * ‖spatialFourier f p‖ ^ 2)
      (by positivity : 2 * Real.pi ≠ 0)).mpr
        (integrable_inv_dispersion_fourier_norm_sq (by norm_num : (0 : ℝ) < 1) f)
    simpa only [spatialFourier_two_pi] using h
  calc
    _ ≤ ∫ p, (dispersion 1 ((2 * Real.pi) • p))⁻¹ *
        ‖(𝓕 (spatialSchwartz f)) p‖ ^ 2 := by
      apply integral_mono_ae (integrable_jointTestFrequencyWeight f) hi
      exact Filter.Eventually.of_forall fun p => mul_le_mul_of_nonneg_right
        (jointTestFrequencyWeight_le_inverse_dispersion p) (sq_nonneg _)
    _ = jointFieldEnergy 1 f := normalized_inverse_dispersion_energy 1 f
    _ ≤ _ := by
      unfold jointFieldEnergy
      have h := mul_le_mul_of_nonneg_left (joint_field_mass_comparison hμ f)
        (by positivity : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹)
      simpa only [mul_left_comm] using h

theorem integral_jointTestWeight_le_position_L2 (f : SpatialTestFunction) :
    (∫ p, jointTestFrequencyWeight p * ‖(𝓕 (spatialSchwartz f)) p‖ ^ 2) ≤
      ∫ x, (f.1 x) ^ 2 := by
  calc
    _ ≤ ∫ p, ‖(𝓕 (spatialSchwartz f)) p‖ ^ 2 := by
      apply integral_mono_ae (integrable_jointTestFrequencyWeight f)
        (((𝓕 (spatialSchwartz f)).memLp 2).norm.integrable_sq)
      exact Filter.Eventually.of_forall fun p =>
        mul_le_of_le_one_left (sq_nonneg _) (jointTestFrequencyWeight_le_one p)
    _ = _ := by
      rw [SchwartzMap.integral_norm_sq_fourier]
      simp only [spatialSchwartz_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Uniform field-test estimate in the actual total-source covariance norm. -/
theorem jointTestWeight_first_le_source_norm {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (u : SourceTestSpace hμ U) :
    (∫ p, jointTestFrequencyWeight p * ‖(𝓕 (spatialSchwartz u.1.1)) p‖ ^ 2) ≤
      (2 * max 1 μ) * ‖u‖ ^ 2 := by
  apply (integral_jointTestWeight_le_fieldEnergy hμ u.1.1).trans
  have h := mul_le_mul_of_nonneg_left (jointFieldEnergy_le_sourceTest_norm_sq hμ U u)
    (show 0 ≤ max 1 μ by positivity)
  simpa only [← mul_assoc, mul_comm (max 1 μ) 2] using h

/-- Uniform momentum-test estimate uses the genuine total support volume
bound and the original low-frequency absorption on the two-ball union. -/
theorem jointTestWeight_second_le_source_norm {μ : ℝ} (hμ : 0 < μ)
    (a b : EuclideanSpace ℝ (Fin 3))
    (u : SourceTestSpace hμ (Metric.ball a 1 ∪ Metric.ball b 1)) :
    (∫ p, jointTestFrequencyWeight p * ‖(𝓕 (spatialSchwartz u.1.2)) p‖ ^ 2) ≤
      4 * ‖u‖ ^ 2 := by
  apply (integral_jointTestWeight_le_position_L2 u.1.2).trans
  have h := joint_position_L2_le_weighted_fourier hμ.le u.1.2 a b
    ((subset_tsupport u.1.2.1).trans u.2.2)
  have he : (∫ x, (u.1.2.1 x) ^ 2) ≤ 2 * jointMomentumEnergy μ u.1.2 := by
    simpa only [jointMomentumEnergy, div_eq_mul_inv, mul_assoc] using h
  exact he.trans (by nlinarith [jointMomentumEnergy_le_sourceTest_norm_sq hμ _ u])

end VacuumBellSeparation
