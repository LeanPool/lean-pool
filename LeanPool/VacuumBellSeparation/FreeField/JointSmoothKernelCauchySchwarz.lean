/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelPlancherel
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Actual weighted Fourier Cauchy--Schwarz for Schwartz kernels

The first estimate is a scalar integral statement on the genuine Hilbert
carrier. The polynomial majorant is then the actual mixed-derivative energy.
No source inverse or Hilbert--Schmidt operator is an input.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Weighted Cauchy--Schwarz after actual Plancherel. The lower bound on
the weight also proves integrability of the inverse-weighted test term. -/
theorem weighted_schwartz_pairing_le (K H : SchwartzMap V ℂ)
    (W : V → ℝ) (hWc : Continuous W) (hW : ∀ ξ, 1 ≤ W ξ)
    (hK : Integrable (fun ξ => W ξ * ‖(𝓕 K) ξ‖ ^ 2)) :
    ‖∫ x, conj (H x) * K x‖ ≤
      Real.sqrt (∫ ξ, W ξ * ‖(𝓕 K) ξ‖ ^ 2) *
        Real.sqrt (∫ ξ, (W ξ)⁻¹ * ‖(𝓕 H) ξ‖ ^ 2) := by
  have hWpos (ξ : V) : 0 < W ξ := lt_of_lt_of_le zero_lt_one (hW ξ)
  let a : V → ℝ := fun ξ => Real.sqrt (W ξ) * ‖(𝓕 K) ξ‖
  let b : V → ℝ := fun ξ => (Real.sqrt (W ξ))⁻¹ * ‖(𝓕 H) ξ‖
  have hac : Continuous a := (Real.continuous_sqrt.comp hWc).mul (𝓕 K).continuous.norm
  have hbc : Continuous b := ((Real.continuous_sqrt.comp hWc).inv₀
    (fun ξ => (Real.sqrt_pos.2 (hWpos ξ)).ne')).mul (𝓕 H).continuous.norm
  have ha0 (ξ : V) : 0 ≤ a ξ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hb0 (ξ : V) : 0 ≤ b ξ := mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (norm_nonneg _)
  have ha2 (ξ : V) : (a ξ) ^ 2 = W ξ * ‖(𝓕 K) ξ‖ ^ 2 := by
    dsimp only [a]
    rw [mul_pow, Real.sq_sqrt (hWpos ξ).le]
  have hb2 (ξ : V) : (b ξ) ^ 2 = (W ξ)⁻¹ * ‖(𝓕 H) ξ‖ ^ 2 := by
    dsimp only [b]
    rw [mul_pow, inv_pow, Real.sq_sqrt (hWpos ξ).le]
  have hib : Integrable (fun ξ => (W ξ)⁻¹ * ‖(𝓕 H) ξ‖ ^ 2) := by
    apply (((𝓕 H).memLp 2).norm.integrable_sq).mono'
      (((hWc.inv₀ (fun ξ => (hWpos ξ).ne')).mul ((𝓕 H).continuous.norm.pow 2)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun ξ => by
      change ‖(W ξ)⁻¹ * ‖(𝓕 H) ξ‖ ^ 2‖ ≤ ‖(𝓕 H) ξ‖ ^ 2
      rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (hWpos ξ).le) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) ((inv_le_one₀ (hWpos ξ)).mpr (hW ξ))
  have haLp : MemLp a (ENNReal.ofReal 2) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    apply (memLp_two_iff_integrable_sq hac.aestronglyMeasurable).mpr
    simpa only [ha2] using hK
  have hbLp : MemLp b (ENNReal.ofReal 2) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    apply (memLp_two_iff_integrable_sq hbc.aestronglyMeasurable).mpr
    simpa only [hb2] using hib
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two haLp hbLp
  have haa (ξ : V) : ‖a ξ‖ = a ξ := Real.norm_of_nonneg (ha0 ξ)
  have hbb (ξ : V) : ‖b ξ‖ = b ξ := Real.norm_of_nonneg (hb0 ξ)
  simp only [haa, hbb, Real.rpow_two, ← Real.sqrt_eq_rpow, ha2, hb2] at hcs
  have hab (ξ : V) : a ξ * b ξ = ‖(𝓕 H) ξ‖ * ‖(𝓕 K) ξ‖ := by
    dsimp only [a, b]
    have hs : Real.sqrt (W ξ) ≠ 0 := (Real.sqrt_pos.2 (hWpos ξ)).ne'
    field_simp
  have hp : (∫ x, conj (H x) * K x) = ∫ ξ, conj ((𝓕 H) ξ) * (𝓕 K) ξ := by
    simpa only [RCLike.inner_apply'] using
      (SchwartzMap.integral_inner_fourier_fourier H K).symm
  rw [hp]
  calc
    _ ≤ ∫ ξ, ‖conj ((𝓕 H) ξ) * (𝓕 K) ξ‖ := norm_integral_le_integral_norm _
    _ = ∫ ξ, a ξ * b ξ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        change ‖conj ((𝓕 H) ξ) * (𝓕 K) ξ‖ = a ξ * b ξ
        rw [norm_mul, Complex.norm_conj, hab]
    _ ≤ _ := hcs

/-- Joint kernel polynomial weight given by `(1 + (2 * Real.pi) ^ 2 * ‖ξ.fst‖ ^ 2) * (1 + (2 *
Real.pi) ^ 2 * ‖ξ.snd‖ ^ 2)`. -/
def jointKernelPolynomialWeight (ξ : JointKernelSpace) : ℝ :=
  (1 + (2 * Real.pi) ^ 2 * ‖ξ.fst‖ ^ 2) *
    (1 + (2 * Real.pi) ^ 2 * ‖ξ.snd‖ ^ 2)

theorem jointKernelPolynomialWeight_one_le (ξ : JointKernelSpace) :
    1 ≤ jointKernelPolynomialWeight ξ := by
  unfold jointKernelPolynomialWeight
  have h1 : 0 ≤ (2 * Real.pi) ^ 2 * ‖ξ.fst‖ ^ 2 := by positivity
  have h2 : 0 ≤ (2 * Real.pi) ^ 2 * ‖ξ.snd‖ ^ 2 := by positivity
  nlinarith

theorem continuous_jointKernelPolynomialWeight : Continuous jointKernelPolynomialWeight := by
  unfold jointKernelPolynomialWeight
  fun_prop

/-- The actual kernel pairing is bounded by the explicit sixteen-term
mixed energy and the inverse polynomial Fourier weight of the test. -/
theorem jointKernel_pairing_le (K H : SchwartzMap JointKernelSpace ℂ) :
    ‖∫ x, conj (H x) * K x‖ ≤
      Real.sqrt (jointKernelDerivativeEnergy K) *
        Real.sqrt (∫ ξ, (jointKernelPolynomialWeight ξ)⁻¹ * ‖(𝓕 H) ξ‖ ^ 2) := by
  have h := weighted_schwartz_pairing_le K H jointKernelPolynomialWeight
    continuous_jointKernelPolynomialWeight jointKernelPolynomialWeight_one_le
    (integrable_jointKernel_frequency_weight K)
  simpa only [jointKernelPolynomialWeight, integral_jointKernel_frequency_weight] using h

end VacuumBellSeparation
