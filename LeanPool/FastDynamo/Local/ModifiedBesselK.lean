/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Integral modified-Bessel functions of the second kind

This file defines the two second-kind orders used by the Ponomarenko dispersion relation through
their standard hyperbolic integral formulas

`K₀(z) = ∫₀^∞ exp (-z cosh t) dt`,

`K₂(z) = ∫₀^∞ exp (-z cosh t) cosh (2t) dt`.

The kernels are proved integrable throughout the natural half-plane `0 < z.re`. The proof gives
explicit Gaussian majorants: `cosh t ≥ t²/2`, while the extra `cosh (2t)` factor is absorbed by
Young's quadratic inequality. Conjugation identities then certify that both functions are real on
the positive real axis.

Lean's Bochner integral is totalized, so the definitions below are functions on all of `ℂ`; they
represent the standard principal-branch `K₀` and `K₂` only where `0 < z.re`. No identification with
the classical functions is claimed outside that half-plane.
-/

@[expose] public section

noncomputable section

namespace FastDynamo.ModifiedBessel

open Complex MeasureTheory Set
open scoped ComplexConjugate

/-- A quadratic lower bound on the real hyperbolic cosine. -/
lemma sq_div_two_le_cosh (t : ℝ) : t ^ 2 / 2 ≤ Real.cosh t := by
  have hs : |t / 2| ≤ |Real.sinh (t / 2)| := by
    calc
      |t / 2| ≤ Real.sinh |t / 2| := Real.self_le_sinh_iff.mpr (abs_nonneg _)
      _ = |Real.sinh (t / 2)| := (Real.abs_sinh (t / 2)).symm
  have hs_sq : (t / 2) ^ 2 ≤ Real.sinh (t / 2) ^ 2 := (sq_le_sq).mpr hs
  have hc := Real.cosh_two_mul (t / 2)
  have hc_sq := Real.cosh_sq' (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hc
  nlinarith

/-- Young's inequality in the normalization used to absorb the `cosh (2t)` factor. -/
lemma two_abs_le_quadratic {a : ℝ} (ha : 0 < a) (t : ℝ) :
    2 * |t| ≤ a / 4 * t ^ 2 + 4 / a := by
  have ht : |t| ^ 2 = t ^ 2 := sq_abs t
  have hp : 8 * a * |t| ≤ a ^ 2 * t ^ 2 + 16 := by
    nlinarith [sq_nonneg (a * |t| - 4)]
  rw [show a / 4 * t ^ 2 + 4 / a = (a ^ 2 * t ^ 2 + 16) / (4 * a) by
    field_simp [ha.ne']; ring]
  rw [le_div_iff₀ (show 0 < 4 * a by positivity)]
  nlinarith

/-- The elementary exponential upper bound for the real hyperbolic cosine. -/
lemma cosh_le_exp_abs (t : ℝ) : Real.cosh t ≤ Real.exp |t| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp t ≤ Real.exp |t| := Real.exp_le_exp.mpr (le_abs_self t)
  have h2 : Real.exp (-t) ≤ Real.exp |t| := Real.exp_le_exp.mpr (neg_le_abs t)
  nlinarith

/-- The hyperbolic integral kernel for `K₀`. -/
def K0Integrand (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-z * Real.cosh t)

/-- The hyperbolic integral kernel for `K₂`. -/
def K2Integrand (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-z * Real.cosh t) * (Real.cosh (2 * t) : ℂ)

/-- The hyperbolic-integral definition of the order-zero modified Bessel function of the second
kind. It represents the standard function on `0 < z.re`; outside that half-plane it is merely the
totalized Bochner integral. -/
noncomputable def K0 (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), K0Integrand z t

/-- The hyperbolic-integral definition of the order-two modified Bessel function of the second
kind. It represents the standard function on `0 < z.re`; outside that half-plane it is merely the
totalized Bochner integral. -/
noncomputable def K2 (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), K2Integrand z t

/-- The modulus of the `K₀` kernel depends only on the real part of `z`:
`‖exp (-z cosh t)‖ = exp (-(Re z) cosh t)`. -/
lemma norm_K0Integrand (z : ℂ) (t : ℝ) :
    ‖K0Integrand z t‖ = Real.exp (-z.re * Real.cosh t) := by
  simp [K0Integrand, Complex.norm_exp]

/-- The modulus of the `K₂` kernel is `exp (-(Re z) cosh t) · cosh (2t)`, the extra factor being
real and positive. -/
lemma norm_K2Integrand (z : ℂ) (t : ℝ) :
    ‖K2Integrand z t‖ = Real.exp (-z.re * Real.cosh t) * Real.cosh (2 * t) := by
  rw [K2Integrand, norm_mul, Complex.norm_exp]
  simp only [neg_mul, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]

/-- The `K₀` kernel is bounded by an integrable Gaussian whenever `0 < z.re`. -/
lemma norm_K0Integrand_le_gaussian {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    ‖K0Integrand z t‖ ≤ Real.exp (-(z.re / 2) * t ^ 2) := by
  rw [norm_K0Integrand]
  apply Real.exp_le_exp.mpr
  have hc := sq_div_two_le_cosh t
  nlinarith

/-- The `K₂` kernel is bounded by an integrable Gaussian whenever `0 < z.re`. -/
lemma norm_K2Integrand_le_gaussian {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    ‖K2Integrand z t‖ ≤ Real.exp (4 / z.re) * Real.exp (-(z.re / 4) * t ^ 2) := by
  rw [norm_K2Integrand]
  calc
    Real.exp (-z.re * Real.cosh t) * Real.cosh (2 * t)
        ≤ Real.exp (-z.re * Real.cosh t) * Real.exp |2 * t| := by
          gcongr
          exact cosh_le_exp_abs (2 * t)
    _ = Real.exp (-z.re * Real.cosh t + 2 * |t|) := by
          rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), Real.exp_add]
    _ ≤ Real.exp (-(z.re / 4) * t ^ 2 + 4 / z.re) := by
          apply Real.exp_le_exp.mpr
          have hc := sq_div_two_le_cosh t
          have hy := two_abs_le_quadratic hz t
          nlinarith
    _ = Real.exp (4 / z.re) * Real.exp (-(z.re / 4) * t ^ 2) := by
          rw [add_comm, Real.exp_add]

/-- Absolute integrability of the `K₀` kernel in the right half-plane. -/
theorem integrable_K0Integrand {z : ℂ} (hz : 0 < z.re) :
    Integrable (K0Integrand z) := by
  apply Integrable.mono' (integrable_exp_neg_mul_sq (show 0 < z.re / 2 by positivity))
  · exact (by unfold K0Integrand; fun_prop : Continuous (K0Integrand z)).aestronglyMeasurable
  · exact ae_of_all _ (norm_K0Integrand_le_gaussian hz)

/-- Absolute integrability of the `K₂` kernel in the right half-plane. -/
theorem integrable_K2Integrand {z : ℂ} (hz : 0 < z.re) :
    Integrable (K2Integrand z) := by
  have hg : Integrable (fun t : ℝ ↦
      Real.exp (4 / z.re) * Real.exp (-(z.re / 4) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq (show 0 < z.re / 4 by positivity)).const_mul _
  apply Integrable.mono' hg
  · exact (by unfold K2Integrand; fun_prop : Continuous (K2Integrand z)).aestronglyMeasurable
  · exact ae_of_all _ (norm_K2Integrand_le_gaussian hz)

/-- Set-integrability of the `K₀` kernel on its defining ray. -/
theorem integrableOn_K0Integrand {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (K0Integrand z) (Ioi 0) :=
  (integrable_K0Integrand hz).integrableOn

/-- Set-integrability of the `K₂` kernel on its defining ray. -/
theorem integrableOn_K2Integrand {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (K2Integrand z) (Ioi 0) :=
  (integrable_K2Integrand hz).integrableOn

/-- `K₀` commutes with complex conjugation. -/
@[simp] theorem K0_conj (z : ℂ) : K0 (conj z) = conj (K0 z) := by
  rw [K0, K0, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  unfold K0Integrand
  rw [← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_ofReal]

/-- `K₂` commutes with complex conjugation. -/
@[simp] theorem K2_conj (z : ℂ) : K2 (conj z) = conj (K2 z) := by
  rw [K2, K2, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  unfold K2Integrand
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_ofReal]

end FastDynamo.ModifiedBessel
