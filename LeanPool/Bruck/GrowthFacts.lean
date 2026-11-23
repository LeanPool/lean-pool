/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.WVEntireGrowth
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville

/-! # Bounds on maximum moduli -/

public section

open Asymptotics Bornology Filter Metric Set Topology

namespace Bruck

theorem exists_nonzero_iteratedDeriv_of_nonconstant {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnon : ¬ ∀ z, f z = f 0) :
    ∃ n : ℕ, 0 < n ∧ iteratedDeriv n f 0 ≠ 0 := by
  by_contra! hzero
  apply hnon
  intro z
  rw [← Complex.taylorSeries_eq_of_entire' (c := 0) (z := z) hf, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hzero n (Nat.pos_of_ne_zero hn)]

theorem exists_linear_le_maximumModulus {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnon : ¬ ∀ z, f z = f 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ≥ 1, c * r ≤ wvMaximumModulus f r := by
  obtain ⟨n, hn, hderiv⟩ := exists_nonzero_iteratedDeriv_of_nonconstant hf hnon
  refine ⟨wvTaylorNorm f n, wvTaylorNorm_pos hderiv, fun r hr => ?_⟩
  have hrpow : r ≤ r ^ n := by
    simpa using pow_le_pow_right₀ hr (show 1 ≤ n from hn)
  exact (mul_le_mul_of_nonneg_left hrpow (wvTaylorNorm_pos hderiv).le).trans
    (wvTaylorNorm_mul_pow_le_maximum hf n (zero_lt_one.trans_le hr))

theorem maximumModulus_tendsto_atTop {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnon : ¬ ∀ z, f z = f 0) :
    Tendsto (wvMaximumModulus f) atTop atTop := by
  obtain ⟨c, hc, hlower⟩ := exists_linear_le_maximumModulus hf hnon
  exact tendsto_atTop_mono' atTop ((eventually_ge_atTop 1).mono hlower)
    ((tendsto_const_mul_atTop_of_pos hc).mpr tendsto_id)

theorem exists_pow_le_maximumModulus_of_nonPolynomial {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnon : WVNonPolynomial f) (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ≥ 1, c * r ^ m ≤ wvMaximumModulus f r := by
  obtain ⟨n, hn, hderiv⟩ := hnon.exists_large_nonzero_derivative hf m
  refine ⟨wvTaylorNorm f n, wvTaylorNorm_pos hderiv, fun r hr => ?_⟩
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hn)
    (wvTaylorNorm_pos hderiv).le).trans
      (wvTaylorNorm_mul_pow_le_maximum hf n (zero_lt_one.trans_le hr))

theorem exists_polynomial_of_maximumModulus_le_pow {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C : ℝ} {d : ℕ} (hbound : ∀ᶠ r in atTop, wvMaximumModulus f r ≤ C * r ^ d) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z := by
  have hg : f =O[cobounded ℂ] (· ^ d) := by
    refine isBigO_iff.mpr ⟨C, ?_⟩
    filter_upwards [tendsto_norm_cobounded_atTop.eventually hbound] with z hz
    simpa only [norm_pow] using (wv_norm_le_maximumModulus hf.continuous rfl).trans hz
  obtain ⟨p, _, hp⟩ := hf.exists_eq_polynomial_eval_of_isBigO_pow hg
  exact ⟨p, congrFun hp⟩

private theorem iteratedDeriv_polynomial_eval (p : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n p.eval = ((Polynomial.derivative^[n]) p).eval := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have heq : deriv p.eval = p.derivative.eval := funext fun z => p.deriv (x := z)
    rw [heq, ih]

theorem polynomial_leadingCoeff_mul_pow_le_maximumModulus
    (p : Polynomial ℂ) {r : ℝ} (hr : 0 < r) :
    ‖p.leadingCoeff‖ * r ^ p.natDegree ≤ wvMaximumModulus p.eval r := by
  let n := p.natDegree
  have hderiv : iteratedDeriv n p.eval 0 = (n.factorial : ℂ) * p.leadingCoeff := by
    rw [iteratedDeriv_polynomial_eval]
    change ((Polynomial.derivative^[n]) p).eval 0 = _
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, zero_add,
      Nat.descFactorial_self, nsmul_eq_mul, Polynomial.leadingCoeff]
  have hcoeff : wvTaylorNorm p.eval n = ‖p.leadingCoeff‖ := by
    rw [wvTaylorNorm, hderiv, norm_mul, Complex.norm_natCast]
    exact mul_div_cancel_left₀ _ (by positivity)
  simpa only [hcoeff, n] using wvTaylorNorm_mul_pow_le_maximum p.differentiable n hr

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

theorem wvMaximumModulus_polynomial_le (p : Polynomial ℂ) {r : ℝ} (hr : 1 ≤ r) :
    wvMaximumModulus p.eval r ≤
      (∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖) * r ^ p.natDegree := by
  obtain ⟨z, hz, hmax⟩ :=
    wvMaximumModulus_attained p.differentiable.continuous (zero_le_one.trans hr)
  rw [← hmax]
  exact norm_eval_polynomial_le p hr hz

theorem nonconstant_exp_comp {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnon : ¬ ∀ z, f z = f 0) : ¬ ∀ z, Complex.exp (f z) = Complex.exp (f 0) := by
  intro hconst
  apply hnon
  have heq : (fun z => Complex.exp (f z)) = fun _ : ℂ => Complex.exp (f 0) := funext hconst
  have hderiv (z : ℂ) : deriv f z = 0 := by
    have hh := (Complex.hasDerivAt_exp (f z)).comp z (hf z).hasDerivAt
    change HasDerivAt (fun w => Complex.exp (f w)) _ z at hh
    rw [heq] at hh
    have hprod := hh.deriv
    rw [deriv_const] at hprod
    exact (mul_eq_zero.mp hprod.symm).resolve_left (Complex.exp_ne_zero _)
  intro z
  exact is_const_of_deriv_eq_zero hf hderiv z 0

theorem polynomial_eval_nonconstant_iff (p : Polynomial ℂ) :
    (¬ ∀ z, p.eval z = p.eval 0) ↔ 0 < p.natDegree := by
  constructor
  · intro hnon
    by_contra! hdegree
    apply hnon
    rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hdegree)]
    simp
  · intro hp hconst
    have heq : p = Polynomial.C (p.eval 0) :=
      Polynomial.funext (fun z => by simpa only [Polynomial.eval_C] using hconst z)
    rw [heq, Polynomial.natDegree_C] at hp
    exact lt_irrefl _ hp

theorem maximumModulus_exp_le {f : ℂ → ℂ} (hf : Continuous f)
    {r : ℝ} (hr : 0 ≤ r) :
    wvMaximumModulus (fun z => Complex.exp (f z)) r ≤ Real.exp (wvMaximumModulus f r) := by
  obtain ⟨z, hz, hmax⟩ := wvMaximumModulus_attained (H := fun z => Complex.exp (f z))
    (Complex.continuous_exp.comp hf) hr
  rw [← hmax, Complex.norm_exp]
  exact Real.exp_le_exp.mpr
    ((Complex.re_le_norm _).trans (wv_norm_le_maximumModulus hf hz))

theorem maximumModulus_le_log_maximumModulus_exp {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnon : ¬ ∀ z, f z = f 0) :
    ∀ᶠ r in atTop,
      wvMaximumModulus f r ≤
        2 * Real.log (wvMaximumModulus (fun z => Complex.exp (f z)) (2 * r)) + 3 * ‖f 0‖ := by
  let q : ℂ → ℂ := fun z => Complex.exp (f z)
  have hq : Differentiable ℂ q := Complex.differentiable_exp.comp hf
  have hnonq := nonconstant_exp_comp hf hnon
  have ht := (maximumModulus_tendsto_atTop hq hnonq).comp
    ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id)
  filter_upwards [eventually_ge_atTop (1 : ℝ), ht.eventually_gt_atTop 1] with r hr hM
  change 1 < wvMaximumModulus q (2 * r) at hM
  let L := Real.log (wvMaximumModulus q (2 * r))
  have hL : 0 < L := Real.log_pos hM
  have hr2 : 0 < 2 * r := by linarith
  have hre : MapsTo f (ball 0 (2 * r)) {w : ℂ | w.re ≤ L} := by
    intro z hz
    change (f z).re ≤ L
    have hnorm : ‖q z‖ ≤ wvMaximumModulus q (2 * r) :=
      wv_norm_le_maximumModulus_of_le hq hr2 (mem_ball_zero_iff.mp hz).le
    exact (Real.le_log_iff_exp_le (zero_lt_one.trans hM)).mpr
      (by simpa [q, Complex.norm_exp] using hnorm)
  obtain ⟨z, hz, hzmax⟩ := wvMaximumModulus_attained hf.continuous (zero_le_one.trans hr)
  have hzball : z ∈ ball (0 : ℂ) (2 * r) := mem_ball_zero_iff.mpr (by linarith)
  have hb := Complex.borelCaratheodory hL hf.differentiableOn hre hr2 hzball
  rw [hz, hzmax] at hb
  have hden : 2 * r - r ≠ 0 := by linarith
  have hq1 : 2 * L * r / (2 * r - r) = 2 * L := (div_eq_iff hden).mpr (by ring)
  have hq2 : ‖f 0‖ * (2 * r + r) / (2 * r - r) = 3 * ‖f 0‖ := (div_eq_iff hden).mpr (by ring)
  rw [hq1, hq2] at hb
  exact hb

theorem maximumModulus_deriv_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 < r) :
    wvMaximumModulus (deriv f) r ≤ wvMaximumModulus f (2 * r) / r := by
  have hd : Differentiable ℂ (deriv f) := fun z => (hf.analyticAt z).deriv.differentiableAt
  obtain ⟨z, hz, hmax⟩ := wvMaximumModulus_attained hd.continuous hr.le
  rw [← hmax]
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hf.diffContOnCl
  intro w hw
  have hwz : ‖w - z‖ = r := mem_sphere_iff_norm.mp hw
  refine wv_norm_le_maximumModulus_of_le hf (by positivity) ?_
  linarith [norm_le_norm_sub_add w z]

theorem maximumModulus_le_deriv_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 < r) :
    wvMaximumModulus f r ≤ ‖f 0‖ + r * wvMaximumModulus (deriv f) r := by
  have hd : Differentiable ℂ (deriv f) := fun z => (hf.analyticAt z).deriv.differentiableAt
  obtain ⟨z, hz, hmax⟩ := wvMaximumModulus_attained hf.continuous hr.le
  have hbound (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) r) :
      ‖deriv f w‖ ≤ wvMaximumModulus (deriv f) r :=
    wv_norm_le_maximumModulus_of_le hd hr (mem_closedBall_zero_iff.mp hw)
  have hmean := (convex_closedBall (0 : ℂ) r).norm_image_sub_le_of_norm_deriv_le
    (fun w _ => hf w) hbound (mem_closedBall_self hr.le) (mem_closedBall_zero_iff.mpr hz.le)
  rw [← hmax]
  calc
    ‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
    _ ≤ ‖f 0‖ + r * wvMaximumModulus (deriv f) r := by
      simpa [hz, mul_comm, add_comm] using (add_le_add_right hmean ‖f 0‖)

end Bruck
