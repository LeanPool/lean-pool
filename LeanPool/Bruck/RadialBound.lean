/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.WVMaximumModulus
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.ODE.Gronwall

/-! # Growth upper bounds for the inhomogeneous first-order equation -/

public section

open Real Set Filter

namespace Bruck

private theorem gronwallBound_one_le {δ K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε 1 ≤ (δ + ε) * exp K := by
  by_cases hK₀ : K = 0
  · simp [hK₀, gronwallBound_K0]
  have hKpos := lt_of_le_of_ne hK (Ne.symm hK₀)
  have hle : (exp K - 1) / K ≤ exp K := by
    apply (div_le_iff₀ hKpos).2
    have h := mul_le_mul_of_nonneg_right (add_one_le_exp (-K)) (exp_pos K).le
    rw [exp_neg, inv_mul_cancel₀ (exp_ne_zero _)] at h
    nlinarith
  rw [gronwallBound_of_K_ne_0 hK₀]
  simp only [mul_one]
  rw [add_mul, div_mul_eq_mul_div, mul_div_assoc]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hle hε) _

/-- The radial bound for an entire solution of `y' = A * y + 1`.
Apply Grönwall's inequality to the restriction of `y` to a radial segment. -/
theorem wvMaximumModulus_le_of_first_order_ode {A y : ℂ → ℂ}
    (hA : Differentiable ℂ A) (hy : Differentiable ℂ y)
    (hODE : ∀ z, deriv y z = A z * y z + 1)
    {r : ℝ} (hr : 0 < r) :
    wvMaximumModulus y r ≤ (‖y 0‖ + r) * exp (r * wvMaximumModulus A r) := by
  obtain ⟨z, hz, hmax⟩ := wvMaximumModulus_attained hy.continuous hr.le
  let Y : ℝ → ℂ := fun t => y ((t : ℂ) * z)
  have hYd (t : ℝ) : HasDerivAt Y (deriv y ((t : ℂ) * z) * z) t := by
    have hline : HasDerivAt (fun w : ℂ => w * z) z (t : ℂ) := by
      simpa only [id_eq, one_mul] using (hasDerivAt_id (t : ℂ)).mul_const z
    have hcomp : HasDerivAt (fun w : ℂ => y (w * z))
        (deriv y ((t : ℂ) * z) * z) (t : ℂ) :=
      ((hy ((t : ℂ) * z)).hasDerivAt).comp (t : ℂ) hline
    exact hcomp.comp_ofReal
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖deriv y ((t : ℂ) * z) * z‖ ≤ (r * wvMaximumModulus A r) * ‖Y t‖ + r := by
    have hrad : ‖(t : ℂ) * z‖ ≤ r := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1, hz]
      exact mul_le_of_le_one_left hr.le ht.2.le
    have hAnorm := wv_norm_le_maximumModulus_of_le hA hr hrad
    rw [norm_mul, hODE, hz]
    calc
      ‖A ((t : ℂ) * z) * y ((t : ℂ) * z) + 1‖ * r ≤
          (wvMaximumModulus A r * ‖Y t‖ + 1) * r := by
        apply mul_le_mul_of_nonneg_right _ hr.le
        apply (norm_add_le _ _).trans
        rw [norm_mul, norm_one]
        exact add_le_add_left (mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _)) _
      _ = (r * wvMaximumModulus A r) * ‖Y t‖ + r := by ring
  have hYc : Continuous Y := continuous_iff_continuousAt.mpr fun t => (hYd t).continuousAt
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le hYc.continuousOn
    (fun t _ => (hYd t).hasDerivWithinAt) (show ‖Y 0‖ ≤ ‖y 0‖ by simp [Y])
    hbound 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  rw [sub_zero] at hG
  simpa only [Y, Complex.ofReal_one, one_mul, hmax] using
    hG.trans (gronwallBound_one_le
      (mul_nonneg hr.le (wvMaximumModulus_nonneg A r)) hr.le)

/-- A product of a polynomial's coefficient norm sum and a radius power
bounds its norm on the corresponding circle. -/
theorem norm_eval_polynomial_le (P : Polynomial ℂ) {r : ℝ} {z : ℂ}
    (hr : 1 ≤ r) (hz : ‖z‖ = r) :
    ‖P.eval z‖ ≤ (∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖) * r ^ P.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_mul, norm_pow, hz]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))) (norm_nonneg _)

/-- An exponential of a polynomial grows at most as the exponential of
a constant times the radius to that polynomial's degree. -/
theorem wvMaximumModulus_exp_polynomial_le (P : Polynomial ℂ) {r : ℝ} (hr : 1 ≤ r) :
    wvMaximumModulus (fun z => Complex.exp (P.eval z)) r ≤
      exp ((∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖) * r ^ P.natDegree) := by
  obtain ⟨z, hz, hmax⟩ := wvMaximumModulus_attained P.differentiable.cexp.continuous
    ((zero_le_one : (0 : ℝ) ≤ 1).trans hr)
  rw [← hmax, Complex.norm_exp, exp_le_exp]
  exact (Complex.re_le_norm _).trans (norm_eval_polynomial_le P hr hz)

/-- A solution with a polynomial exponent has double-log maximum modulus bounded
by a constant times the radius to that polynomial's degree. -/
theorem doubleLog_maximumModulus_le_of_polynomial_ode (P : Polynomial ℂ)
    (hP : 0 < P.natDegree) {y : ℂ → ℂ} (hy : Differentiable ℂ y)
    (hODE : ∀ z, deriv y z = Complex.exp (P.eval z) * y z + 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → ‖y 0‖ ≤ r → 1 < wvMaximumModulus y r →
      log (log (wvMaximumModulus y r)) ≤ C * r ^ P.natDegree := by
  let C : ℝ := ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C + 4, by positivity, fun r hr hy₀ hyM => ?_⟩
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  let E : ℝ := exp (C * r ^ P.natDegree)
  have hE : 1 ≤ E := one_le_exp (by positivity)
  have hM := wvMaximumModulus_le_of_first_order_ode P.differentiable.cexp hy hODE hrpos
  have hM' : wvMaximumModulus y r ≤ (2 * r) * exp (r * E) := by
    refine hM.trans (mul_le_mul ?_ ?_ (exp_pos _).le (by positivity))
    · linarith
    · exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (wvMaximumModulus_exp_polynomial_le P hr) hrpos.le)
  have hlog := log_le_log (zero_lt_one.trans hyM) hM'
  rw [log_mul (by positivity) (exp_ne_zero _), log_exp] at hlog
  have hlog' : log (wvMaximumModulus y r) ≤ 3 * r * E := by
    have h2r : 2 * r ≤ 2 * r * E := le_mul_of_one_le_right (by positivity) hE
    linarith [log_le_self (show 0 ≤ 2 * r by positivity)]
  have hlog₂ := log_le_log (log_pos hyM) hlog'
  rw [log_mul (by positivity) (show E ≠ 0 from exp_ne_zero _),
    log_mul (by norm_num) hrpos.ne'] at hlog₂
  have hrpow : r ≤ r ^ P.natDegree := by
    simpa only [pow_one] using pow_le_pow_right₀ hr (Nat.succ_le_of_lt hP)
  have hpow : 1 ≤ r ^ P.natDegree := one_le_pow₀ hr
  have hlog3 := log_le_self (show 0 ≤ (3 : ℝ) by norm_num)
  have hlogr := log_le_self hrpos.le
  change log (log (wvMaximumModulus y r)) ≤ (C + 4) * r ^ P.natDegree
  have hlogE : log E = C * r ^ P.natDegree := log_exp _
  rw [hlogE] at hlog₂
  linarith

end Bruck
