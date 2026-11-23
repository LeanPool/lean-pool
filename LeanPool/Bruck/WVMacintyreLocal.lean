/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.WVMaximumModulus
public import Mathlib.Analysis.Complex.BorelCaratheodory

-- Adapted from QuanyuTang/three-im-one-cm-formalization (Apache-2.0).

/-! # A local monomial approximation from almost affine logarithmic growth -/

@[expose] public section

open Set Metric Filter Topology

namespace Bruck

theorem wv_local_monomial_of_affine_bound {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {zr : ℂ} {x ν ρ ε : ℝ} (hzr : ‖zr‖ = Real.exp x)
    (hmax : ‖H zr‖ = wvMaximumModulus H (Real.exp x)) (hHzr : H zr ≠ 0)
    (hρ : 0 < ρ) (hε : 0 < ε)
    (hflat : ∀ t : ℝ, |t| ≤ ρ →
      wvLogMaximum H (x + t) - wvLogMaximum H x - ν * t ≤ ε) :
    ∀ τ : ℂ, ‖τ‖ ≤ ρ / 2 →
      ‖H (zr * Complex.exp τ) - H zr * Complex.exp ((ν : ℂ) * τ)‖ ≤
        4 * (Real.exp ε - 1) * ‖H zr * Complex.exp ((ν : ℂ) * τ)‖ := by
  let Q : ℂ → ℂ := fun τ =>
    H (zr * Complex.exp τ) / (H zr * Complex.exp ((ν : ℂ) * τ))
  have hden (τ : ℂ) : H zr * Complex.exp ((ν : ℂ) * τ) ≠ 0 :=
    mul_ne_zero hHzr (Complex.exp_ne_zero _)
  have hQ : Differentiable ℂ Q := by
    intro τ
    apply DifferentiableAt.div
    · exact (hH _).comp τ ((Complex.differentiable_exp τ).const_mul zr)
    · fun_prop
    · exact hden τ
  have hQ0 : Q 0 = 1 := by simp only [Q, Complex.exp_zero, mul_zero, mul_one, div_self hHzr]
  have hQnorm (τ : ℂ) (hτ : ‖τ‖ ≤ ρ) : ‖Q τ‖ ≤ Real.exp ε := by
    have ht : |τ.re| ≤ ρ := (Complex.abs_re_le_norm τ).trans hτ
    have hsource := wv_norm_le_maximumModulus hH.continuous
      (show ‖zr * Complex.exp τ‖ = Real.exp (x + τ.re) by
        rw [norm_mul, hzr, Complex.norm_exp, Real.exp_add])
    have hM0 := wvMaximumModulus_pos hH ⟨zr, hHzr⟩ (Real.exp_pos x)
    have hM1 := wvMaximumModulus_pos hH ⟨zr, hHzr⟩ (Real.exp_pos (x + τ.re))
    calc
      ‖Q τ‖ = ‖H (zr * Complex.exp τ)‖ /
          (wvMaximumModulus H (Real.exp x) * Real.exp (ν * τ.re)) := by
        dsimp only [Q]
        rw [norm_div, norm_mul, hmax, Complex.norm_exp, Complex.re_ofReal_mul]
      _ ≤ wvMaximumModulus H (Real.exp (x + τ.re)) /
          (wvMaximumModulus H (Real.exp x) * Real.exp (ν * τ.re)) := by
        exact div_le_div_of_nonneg_right hsource (by positivity)
      _ = Real.exp (wvLogMaximum H (x + τ.re) - wvLogMaximum H x - ν * τ.re) := by
        rw [Real.exp_sub, Real.exp_sub, wvLogMaximum, wvLogMaximum,
          Real.exp_log hM0, Real.exp_log hM1]
        ring
      _ ≤ Real.exp ε := Real.exp_le_exp.mpr (hflat τ.re ht)
  have he : 0 < Real.exp ε - 1 := by linarith [Real.one_lt_exp_iff.mpr hε]
  have hRe : MapsTo (fun τ => Q τ - 1) (ball 0 ρ)
      {w : ℂ | w.re < 2 * (Real.exp ε - 1)} := by
    intro τ hτ
    have hn : ‖τ‖ ≤ ρ := (mem_ball_zero_iff.mp hτ).le
    have hh := hQnorm τ hn
    have hr := Complex.re_le_norm (Q τ)
    simp only [mem_ofPred_eq, Complex.sub_re, Complex.one_re]
    linarith
  have hRe_le : MapsTo (fun τ => Q τ - 1) (ball 0 ρ)
      {w : ℂ | w.re ≤ 2 * (Real.exp ε - 1)} := by
    intro w hw
    have hw' : (Q w - 1).re < 2 * (Real.exp ε - 1) := by
      simpa only [Set.mem_ofPred_eq] using hRe hw
    simpa only [Set.mem_ofPred_eq] using hw'.le
  intro τ hτ
  have hτball : τ ∈ ball 0 ρ := mem_ball_zero_iff.mpr (by linarith)
  have hb := Complex.borelCaratheodory_zero (by linarith : 0 < 2 * (Real.exp ε - 1))
    (hQ.sub_const 1).differentiableOn hRe_le hρ hτball (by rw [hQ0]; simp)
  have hsmall : ‖Q τ - 1‖ ≤ 4 * (Real.exp ε - 1) := by
    apply hb.trans
    apply (div_le_iff₀ (by linarith : 0 < ρ - ‖τ‖)).mpr
    nlinarith
  have hid : H (zr * Complex.exp τ) - H zr * Complex.exp ((ν : ℂ) * τ) =
      (Q τ - 1) * (H zr * Complex.exp ((ν : ℂ) * τ)) := by
    dsimp only [Q]
    field_simp
  rw [hid, norm_mul]
  exact mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)

end Bruck
