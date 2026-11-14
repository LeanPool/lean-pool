/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Schwartz Fourier identities for kinetic energy

Extended Plancherel and the squared directional derivative formula for Schwartz functions use
Mathlib’s `exp(-2πi⟪ξ,x⟫)` convention.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap FourierTransform

namespace LiebThirring.Fourier

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Identify the nonnegative squared-norm integral with its real integral. -/
theorem lintegral_norm_sq_eq_ofReal_integral (f : 𝓢(V, H)) :
    (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2) = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    ((f.memLp 2 (volume : Measure V)).integrable_norm_pow (by decide))
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖f x‖))]
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rfl

/-- Plancherel in nonnegative extended-integral form. -/
theorem lintegral_norm_sq_fourier (f : 𝓢(V, H)) :
    (∫⁻ x, (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2) = ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 := by
  rw [lintegral_norm_sq_eq_ofReal_integral, lintegral_norm_sq_eq_ofReal_integral,
    SchwartzMap.integral_norm_sq_fourier]

omit [CompleteSpace H] in
/-- The squared Fourier norm of a directional derivative, with the `2π` factor. -/
theorem norm_sq_fourier_lineDeriv (f : 𝓢(V, H)) (m x : V) :
    ‖(𝓕 (LineDeriv.lineDerivOp m f)) x‖ ^ 2 =
      (2 * Real.pi) ^ 2 * (inner ℝ x m) ^ 2 * ‖(𝓕 f) x‖ ^ 2 := by
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have hg : (fun x : V => inner ℝ x m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  simp only [SchwartzMap.smulLeftCLM_apply_apply hg, smul_apply,
    norm_smul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The directional derivative energy equals its weighted Fourier integral. -/
theorem lintegral_fderiv_eq_fourier (f : 𝓢(V, H)) (m : V) :
    (∫⁻ x, (‖fderiv ℝ (fun y => f y) x m‖₊ : ℝ≥0∞) ^ 2) =
    ∫⁻ x, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
      ENNReal.ofReal ((inner ℝ x m) ^ 2) * (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2 := by
  calc
    _ = ∫⁻ x, (‖LineDeriv.lineDerivOp m f x‖₊ : ℝ≥0∞) ^ 2 := by
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    _ = ∫⁻ x, (‖(𝓕 (LineDeriv.lineDerivOp m f)) x‖₊ : ℝ≥0∞) ^ 2 :=
      (lintegral_norm_sq_fourier _).symm
    _ = _ := by
      apply lintegral_congr
      intro x
      change ‖(𝓕 (LineDeriv.lineDerivOp m f)) x‖ₑ ^ 2 = _
      rw [← ofReal_norm]
      rw [← ENNReal.ofReal_pow (norm_nonneg _), norm_sq_fourier_lineDeriv,
        ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
        ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rfl

end LiebThirring.Fourier

end
