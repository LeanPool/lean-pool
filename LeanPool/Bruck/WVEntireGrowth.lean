/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.WVMaximumModulus
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.TaylorSeries

-- Adapted from QuanyuTang/three-im-one-cm-formalization (Apache-2.0).

/-! # Superlinear logarithmic growth of a non-polynomial entire function -/

@[expose] public section

open Set Metric Filter Topology

namespace Bruck

/-- The function differs from the evaluation of every complex polynomial. -/
def WVNonPolynomial (H : ℂ → ℂ) : Prop :=
  ∀ p : Polynomial ℂ, ∃ z, H z ≠ p.eval z

/-- The norm of the Taylor coefficient of degree `n` at zero. -/
noncomputable def wvTaylorNorm (H : ℂ → ℂ) (n : ℕ) : ℝ :=
  ‖iteratedDeriv n H 0‖ / (n.factorial : ℝ)

theorem WVNonPolynomial.exists_nonzero {H : ℂ → ℂ} (h : WVNonPolynomial H) :
    ∃ z, H z ≠ 0 := by
  simpa using h 0

theorem wv_polynomial_of_eventually_zero_derivatives {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (N : ℕ)
    (hzero : ∀ n : ℕ, N ≤ n → iteratedDeriv n H 0 = 0) :
    ∃ p : Polynomial ℂ, ∀ z, H z = p.eval z := by
  classical
  let c : ℕ → ℂ := fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n H 0
  refine ⟨∑ n ∈ Finset.range N, Polynomial.C (c n) * Polynomial.X ^ n, ?_⟩
  intro z
  have ht := Complex.taylorSeries_eq_of_entire' (c := 0) (z := z) hH
  simp only [sub_zero] at ht
  have heq : (∑' n : ℕ, c n * z ^ n) = ∑ n ∈ Finset.range N, c n * z ^ n := by
    apply tsum_eq_sum
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp only [c, hzero n hn, mul_zero, zero_mul]
  have heval :
      (∑ n ∈ Finset.range N, Polynomial.C (c n) * Polynomial.X ^ n).eval z =
        ∑ n ∈ Finset.range N, c n * z ^ n := by
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  exact ht.symm.trans (heq.trans heval.symm)

theorem WVNonPolynomial.exists_large_nonzero_derivative {H : ℂ → ℂ}
    (h : WVNonPolynomial H) (hH : Differentiable ℂ H) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ iteratedDeriv n H 0 ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨p, hp⟩ := wv_polynomial_of_eventually_zero_derivatives hH N hn
  obtain ⟨z, hz⟩ := h p
  exact hz (hp z)

theorem wvTaylorNorm_pos {H : ℂ → ℂ} {n : ℕ}
    (hn : iteratedDeriv n H 0 ≠ 0) : 0 < wvTaylorNorm H n := by
  exact div_pos (norm_pos_iff.mpr hn) (by positivity)

theorem wvTaylorNorm_mul_pow_le_maximum {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (n : ℕ) {r : ℝ} (hr : 0 < r) :
    wvTaylorNorm H n * r ^ n ≤ wvMaximumModulus H r := by
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (c := (0 : ℂ)) (C := wvMaximumModulus H r) n hr hH.diffContOnCl
    (fun z hz => wv_norm_le_maximumModulus hH.continuous
      (by simpa only [mem_sphere_iff_norm, sub_zero] using hz))
  rw [le_div_iff₀ (pow_pos hr n)] at hh
  rw [wvTaylorNorm, div_mul_eq_mul_div, div_le_iff₀ (show 0 < (n.factorial : ℝ) by positivity)]
  nlinarith

theorem wvLogMaximum_ge_taylor_line {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {n : ℕ} (hn : iteratedDeriv n H 0 ≠ 0) (x : ℝ) :
    Real.log (wvTaylorNorm H n) + (n : ℝ) * x ≤ wvLogMaximum H x := by
  have hp := wvTaylorNorm_pos hn
  have hh := Real.log_le_log (mul_pos hp (pow_pos (Real.exp_pos x) n))
    (wvTaylorNorm_mul_pow_le_maximum hH n (Real.exp_pos x))
  rw [Real.log_mul hp.ne' (pow_pos (Real.exp_pos x) n).ne', Real.log_pow, Real.log_exp] at hh
  exact hh

theorem wvLogMaximum_superlinear {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (h : WVNonPolynomial H) (B : ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → B * x + C ≤ wvLogMaximum H x := by
  obtain ⟨N, hN⟩ := exists_nat_gt B
  obtain ⟨n, hnN, hn⟩ := h.exists_large_nonzero_derivative hH N
  refine ⟨Real.log (wvTaylorNorm H n), fun x hx => ?_⟩
  have hnB : B ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hnN)
  have hh := wvLogMaximum_ge_taylor_line hH hn x
  nlinarith [mul_le_mul_of_nonneg_right hnB hx]

/-- The right derivative of the log maximum modulus on logarithmic radii. -/
noncomputable def wvLogSlope (H : ℂ → ℂ) (x : ℝ) : ℝ :=
  derivWithin (wvLogMaximum H) (Ioi x) x

theorem wvLogSlope_monotone {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hne : ∃ z, H z ≠ 0) : Monotone (wvLogSlope H) := by
  have hh := (wvLogMaximum_convex hH hne).monotoneOn_rightDeriv
  have hmono : Monotone (fun x => derivWithin (wvLogMaximum H) (Ioi x) x) := by
    simpa only [interior_univ, monotoneOn_univ] using hh
  intro x y hxy
  simpa only [wvLogSlope] using hmono hxy

theorem wvLogSlope_tendsto_atTop {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (h : WVNonPolynomial H) : Tendsto (wvLogSlope H) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro B
  obtain ⟨C, hC⟩ := wvLogMaximum_superlinear hH h (B + 1)
  filter_upwards [eventually_ge_atTop (max 1 (wvLogMaximum H 0 - C))] with x hx
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hxC : wvLogMaximum H 0 - C ≤ x := (le_max_right _ _).trans hx
  have hc := wvLogMaximum_convex hH h.exists_nonzero
  have hl := hc.slope_le_leftDeriv_of_mem_interior
    (by simp : (0 : ℝ) ∈ (univ : Set ℝ))
    (by simp : x ∈ interior (univ : Set ℝ)) (by linarith : (0 : ℝ) < x)
  have hr := hc.leftDeriv_le_rightDeriv_of_mem_interior
    (by simp : x ∈ interior (univ : Set ℝ))
  have hline := hC x (by linarith)
  have hquot : B ≤ (wvLogMaximum H x - wvLogMaximum H 0) / x := by
    apply (le_div_iff₀ (by linarith : 0 < x)).mpr
    nlinarith
  apply hquot.trans
  simpa only [slope_def_field, sub_zero, wvLogSlope] using hl.trans hr

end Bruck
