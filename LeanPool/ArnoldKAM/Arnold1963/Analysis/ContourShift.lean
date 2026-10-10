/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Ring

/-!
One-variable contour shifts and exponential decay bounds for normalized Fourier integrals.
-/

@[expose] public section
noncomputable section
open Complex Set
namespace KamProject.Arnold1963

theorem integral_horizontal_shift {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (T a b : ℝ)
    (hf : DifferentiableOn ℂ f (uIcc 0 T ×ℂ uIcc a b))
    (hperiod : ∀ y ∈ uIcc a b, f ((T : ℂ) + y * I) = f (y * I)) :
    (∫ x : ℝ in 0..T, f (x + a * I)) =
      ∫ x : ℝ in 0..T, f (x + b * I) := by
  have h := integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) * I) ((T : ℂ) + b * I) (by simpa using hf)
  have he : (∫ y : ℝ in a..b, f ((T : ℂ) + y * I)) =
      ∫ y : ℝ in a..b, f (y * I) := intervalIntegral.integral_congr hperiod
  simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, zero_add, add_im, mul_im, add_zero] at h
  rw [he] at h
  have hz : (∫ x : ℝ in 0..T, f (x + a * I)) -
      (∫ x : ℝ in 0..T, f (x + b * I)) = 0 := by
    simpa only [ofReal_zero, zero_add, add_sub_cancel_right] using h
  exact sub_eq_zero.mp hz

theorem integral_fourier_horizontal_shift (f : ℂ → ℂ) (k : ℤ) (y : ℝ)
    (hf : DifferentiableOn ℂ f (uIcc 0 (2 * Real.pi) ×ℂ uIcc 0 y))
    (hperiod : ∀ t ∈ uIcc 0 y,
      f ((2 * Real.pi : ℝ) + t * I) = f (t * I)) :
    (∫ x : ℝ in 0..2 * Real.pi, f x * exp (-I * k * x)) =
      ∫ x : ℝ in 0..2 * Real.pi,
        f (x + y * I) * exp (-I * k * (x + y * I)) := by
  have hg : Differentiable ℂ (fun z : ℂ => exp (-I * k * z)) := by fun_prop
  have hs := integral_horizontal_shift (fun z => f z * exp (-I * k * z))
    (2 * Real.pi) 0 y (hf.mul hg.differentiableOn) (by
      intro t ht
      rw [hperiod t ht]
      have he : -I * (k : ℂ) * ((2 * Real.pi : ℝ) + t * I) =
          -I * k * (t * I) + (-k : ℤ) * (2 * Real.pi * I) := by
        push_cast
        ring
      rw [he, exp_add, exp_int_mul_two_pi_mul_I, mul_one])
  simpa only [ofReal_zero, zero_mul, add_zero] using hs

theorem norm_integral_fourier_le_on_shift (f : ℂ → ℂ) (k : ℤ) (y M : ℝ)
    (hf : DifferentiableOn ℂ f (uIcc 0 (2 * Real.pi) ×ℂ uIcc 0 y))
    (hperiod : ∀ t ∈ uIcc 0 y,
      f ((2 * Real.pi : ℝ) + t * I) = f (t * I))
    (hbound : ∀ x ∈ uIcc 0 (2 * Real.pi), ‖f (x + y * I)‖ ≤ M) :
    ‖∫ x : ℝ in 0..2 * Real.pi, f x * exp (-I * k * x)‖ ≤
      (M * Real.exp ((k : ℝ) * y)) * (2 * Real.pi) := by
  rw [integral_fourier_horizontal_shift f k y hf hperiod]
  have hb : ∀ x ∈ uIoc 0 (2 * Real.pi),
      ‖f (x + y * I) * exp (-I * k * (x + y * I))‖ ≤ M * Real.exp ((k : ℝ) * y) := by
    intro x hx
    have he : (-I * (k : ℂ) * (x + y * I)).re = (k : ℝ) * y := by
      simp [mul_re, mul_im]
    rw [norm_mul, norm_exp, he]
    exact mul_le_mul_of_nonneg_right (hbound x (uIoc_subset_uIcc hx)) (Real.exp_pos _).le
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  simpa only [sub_zero, abs_of_pos hT] using h

theorem norm_normalized_fourierIntegral_le (f : ℂ → ℂ) (k : ℤ) {ρ M : ℝ}
    (hρ : 0 ≤ ρ)
    (hf : DifferentiableOn ℂ f {z | |z.im| ≤ ρ})
    (hperiod : ∀ z : ℂ, |z.im| ≤ ρ → f (z + (2 * Real.pi : ℝ)) = f z)
    (hbound : ∀ z : ℂ, |z.im| ≤ ρ → ‖f z‖ ≤ M) :
    ‖(∫ x : ℝ in 0..2 * Real.pi, f x * exp (-I * k * x)) /
        (2 * Real.pi : ℝ)‖ ≤ M * Real.exp (-|(k : ℝ)| * ρ) := by
  let y : ℝ := if 0 ≤ k then -ρ else ρ
  have hy : |y| ≤ ρ := by dsimp [y]; split_ifs <;> simp [abs_of_nonneg hρ]
  have ht : ∀ t ∈ uIcc 0 y, |t| ≤ ρ := by
    intro t ht
    exact abs_le.mpr (uIcc_subset_Icc ⟨by linarith, hρ⟩ (abs_le.mp hy) ht)
  have hrect : DifferentiableOn ℂ f (uIcc 0 (2 * Real.pi) ×ℂ uIcc 0 y) :=
    hf.mono (fun z hz => ht z.im hz.2)
  have hp : ∀ t ∈ uIcc 0 y, f ((2 * Real.pi : ℝ) + t * I) = f (t * I) := by
    intro t htt
    simpa only [add_comm] using hperiod ((t : ℂ) * I) (by simpa using ht t htt)
  have hb : ∀ x ∈ uIcc 0 (2 * Real.pi), ‖f (x + y * I)‖ ≤ M := by
    intro x _
    exact hbound _ (by simpa using hy)
  have he : (k : ℝ) * y = -|(k : ℝ)| * ρ := by
    dsimp [y]
    split_ifs with hk
    · rw [abs_of_nonneg (by exact_mod_cast hk)]
      ring
    · rw [abs_of_neg (by exact_mod_cast (lt_of_not_ge hk))]
      ring
  have h := norm_integral_fourier_le_on_shift f k y M hrect hp hb
  rw [he] at h
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  exact (div_le_iff₀ hT).mpr h

end KamProject.Arnold1963
