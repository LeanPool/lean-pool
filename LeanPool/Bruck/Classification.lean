/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.GlobalGrowth
public import LeanPool.Bruck.HyperOrderComparison
public import LeanPool.Bruck.RadialBound

/-!
# Growth of solutions of the inhomogeneous equation

The contour estimate gives a lower bound at arbitrarily large radii.
Gronwall's inequality gives the matching upper bound for polynomial exponents.
-/

@[expose] public section

open Filter
open scoped ENNReal

namespace Bruck

private theorem tendsto_doubleLog_maximumModulus {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnon : ¬ ∀ z, f z = f 0) :
    Tendsto (fun r => Real.log (Real.log (wvMaximumModulus f r))) atTop atTop :=
  Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp (maximumModulus_tendsto_atTop hf hnon))

/-- An ordinary power lower bound for the exponent yields a hyper-order
lower bound of that degree for every nonconstant solution. -/
theorem le_hyperOrder_of_ode_lower {y h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (hhnon : ¬ ∀ z, h z = h 0) (hy : Differentiable ℂ y)
    (hynon : ¬ ∀ z, y z = y 0) (hODE : ∀ z, deriv y z = Complex.exp (h z) * y z + 1)
    {m : ℕ} {c : ℝ} (hc : 0 < c)
    (hbound : ∀ r ≥ 1, c * r ^ m ≤ wvMaximumModulus h r) :
    (m : ℝ≥0∞) ≤ hyperOrder y := by
  rw [hyperOrder_eq_logOrder_maximumModulus hy hynon]
  by_contra! hlt
  obtain ⟨s, hs, hsm⟩ := exists_between hlt
  have hsTop := (hsm.trans_le le_top).ne
  have hsR : s.toReal < (m : ℝ) := by
    simpa using (ENNReal.toReal_lt_toReal hsTop (ENNReal.natCast_ne_top m)).2 hsm
  have hFpos : ∀ᶠ r in atTop, 0 < Real.log (Real.log (wvMaximumModulus y r)) :=
    (tendsto_doubleLog_maximumModulus hy hynon).eventually_gt_atTop 0
  have hupper := eventually_le_rpow_of_logOrder_lt (s := s.toReal) hFpos
    (by rwa [ENNReal.ofReal_toReal hsTop])
  have hscale : Tendsto (fun r : ℝ => 2 * r) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
  have hconst := (tendsto_rpow_atTop (sub_pos.2 hsR)).eventually_gt_atTop
    ((2 : ℝ) ^ s.toReal * 2200 / c)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1
    ((hscale.eventually hupper).and hconst)
  obtain ⟨r, hr, hr1, hlow⟩ := exists_uniform_maximumModulus_lower_bound hh hhnon threshold
  have hr0 := zero_lt_one.trans_le hr1
  have ⟨hup, hpow⟩ := hthreshold r hr
  change Real.log (Real.log (wvMaximumModulus y (2 * r))) ≤ (2 * r) ^ s.toReal at hup
  change 2 ^ s.toReal * 2200 / c < r ^ ((m : ℝ) - s.toReal) at hpow
  have hMlow := hlow y hy hODE
  have hfirst := Real.log_le_log (Real.exp_pos _) hMlow
  rw [Real.log_exp] at hfirst
  have hsecond := Real.log_le_log (Real.exp_pos _) hfirst
  rw [Real.log_exp] at hsecond
  have habsorb : (2 * r) ^ s.toReal < (c * r ^ m) / 2200 := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr0.le, ← Real.rpow_natCast]
    have hp' := (div_lt_iff₀ hc).1 hpow
    have hmul := mul_lt_mul_of_pos_right hp' (Real.rpow_pos_of_pos hr0 s.toReal)
    have hrewrite : (r ^ ((m : ℝ) - s.toReal) * c) * r ^ s.toReal =
        c * r ^ (m : ℝ) := by
      rw [mul_right_comm, ← Real.rpow_add hr0, sub_add_cancel, mul_comm]
    rw [hrewrite] at hmul
    exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2200)).2 (by
      convert hmul using 1
      ring)
  have hbound' := div_le_div_of_nonneg_right (hbound r hr1) (by norm_num : (0 : ℝ) ≤ 2200)
  linarith

/-- A nonconstant polynomial exponent forces exactly its degree as hyper-order. -/
theorem hyperOrder_eq_natDegree_of_polynomial_ode (P : Polynomial ℂ) (hP : 0 < P.natDegree)
    {y : ℂ → ℂ} (hy : Differentiable ℂ y) (hynon : ¬ ∀ z, y z = y 0)
    (hODE : ∀ z, deriv y z = Complex.exp (P.eval z) * y z + 1) :
    hyperOrder y = (P.natDegree : ℝ≥0∞) := by
  have hnonP := polynomial_eval_nonconstant P hP
  have hpne : P ≠ 0 := by intro h; simp [h] at hP
  have hc : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.2 (Polynomial.leadingCoeff_ne_zero.mpr hpne)
  apply le_antisymm ?_
    (le_hyperOrder_of_ode_lower P.differentiable hnonP hy hynon hODE hc
      fun r hr => polynomial_leadingCoeff_mul_pow_le_maximumModulus P (zero_lt_one.trans_le hr))
  rw [hyperOrder_eq_logOrder_maximumModulus hy hynon]
  obtain ⟨C, hC, hbound⟩ := doubleLog_maximumModulus_le_of_polynomial_ode P hP hy hODE
  let G : ℝ → ℝ := fun r => r ^ (P.natDegree : ℝ)
  have hFpos : ∀ᶠ r in atTop, 0 < Real.log (Real.log (wvMaximumModulus y r)) :=
    (tendsto_doubleLog_maximumModulus hy hynon).eventually_gt_atTop 0
  have hGpos : ∀ᶠ r in atTop, 0 < G r :=
    (eventually_gt_atTop (0 : ℝ)).mono fun _ hr => Real.rpow_pos_of_pos hr _
  have hle := logOrder_le_of_eventually_le_scaled (k := 1) hC one_pos hFpos hGpos (by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop ‖y 0‖,
      (maximumModulus_tendsto_atTop hy hynon).eventually_gt_atTop 1] with r hr hy0 hM
    simpa only [G, one_mul, Real.rpow_natCast] using hbound r hr hy0 hM)
  exact hle.trans (by
    simpa using logOrder_le_of_eventually_rpow (s := (P.natDegree : ℝ)) hGpos
      (Eventually.of_forall fun _ => le_rfl))

/-- A transcendental entire exponent forces infinite hyper-order. -/
theorem hyperOrder_eq_top_of_transcendental_ode {h y : ℂ → ℂ}
    (hh : Differentiable ℂ h) (htrans : WVNonPolynomial h)
    (hy : Differentiable ℂ y) (hynon : ¬ ∀ z, y z = y 0)
    (hODE : ∀ z, deriv y z = Complex.exp (h z) * y z + 1) :
    hyperOrder y = ⊤ := by
  have hhnon : ¬ ∀ z, h z = h 0 := by
    intro hconstant
    obtain ⟨z, hz⟩ := htrans (Polynomial.C (h 0))
    exact hz (by simpa using hconstant z)
  have hall (m : ℕ) : (m : ℝ≥0∞) ≤ hyperOrder y := by
    obtain ⟨c, hc, hlow⟩ := exists_pow_le_maximumModulus_of_nonPolynomial hh htrans m
    exact le_hyperOrder_of_ode_lower hh hhnon hy hynon hODE hc hlow
  by_contra htop
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt htop
  exact (not_lt_of_ge (hall m)) hm

end Bruck
