/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.WVMaximumModulus
import LeanPool.Bruck.WVMacintyreLocal
import LeanPool.Bruck.WVNormalRadii
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Exponential approximation at maximum-modulus points -/

public section

open Filter Metric Set Topology

namespace Bruck

/-- The radius, maximum point and rescaling for an exponential approximation. -/
structure MaximumData (h : ℂ → ℂ) (r : ℝ) (z : ℂ) (ν : ℝ) : Prop where
  /-- The radius is at least one. -/
  radius_lower : 1 ≤ r
  /-- The maximum modulus is large enough to take a positive logarithm. -/
  modulus_lower : Real.exp 1 < wvMaximumModulus h r
  /-- The candidate maximum point belongs to the circle of radius `r`. -/
  point_on_circle : ‖z‖ = r
  /-- The point attains the maximum modulus on this circle. -/
  point_maximal : ‖h z‖ = wvMaximumModulus h r
  /-- Lower bound on the coordinate rescaling factor. -/
  scale_lower : (1 / 2 : ℝ) ≤ ν
  /-- Upper bound on the coordinate rescaling factor. -/
  scale_upper : ν ≤ 2 * (Real.log (wvMaximumModulus h r)) ^ 2
  /-- Uniform relative error of the exponential approximation on the rescaled disk. -/
  approximation : ∀ ζ : ℂ, ‖ζ‖ ≤ 10 →
    ‖h (z * Complex.exp (ζ / (ν : ℂ))) / (h z * Complex.exp ζ) - 1‖ ≤ 1 / 100

private theorem exists_transcendental_maximum_data {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (hn : WVNonPolynomial h) (bound : ℝ) :
    ∃ (r : ℝ) (z : ℂ) (ν : ℝ),
      bound ≤ r ∧ MaximumData h r z ν := by
  have hc : ContinuousAt (fun η : ℝ => 4 * (Real.exp (7 * η) - 1)) 0 := by
    fun_prop
  obtain ⟨δ, hδ, hδbound⟩ := Metric.continuousAt_iff.mp hc (1 / 100) (by norm_num)
  let η : ℝ := δ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hδclose : dist η 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hη]
    dsimp [η]
    linarith
  have hsmall := hδbound hδclose
  simp only [Real.dist_eq, mul_zero, Real.exp_zero, sub_self, sub_zero] at hsmall
  obtain ⟨x, k, hx, hx2, hM, hρ, _, hν, hνρ, hνupper, hflat⟩ :=
    wv_good_log_radius hh hn (η := η) (B := 20) hη (by norm_num) (max bound 0)
  let ν := wvLogSlope h x
  let ρ := wvGridWidth η (k + 1)
  let r := Real.exp x
  have hr : 0 < r := Real.exp_pos _
  have hr1 : 1 ≤ r := Real.one_le_exp_iff.mpr (by linarith)
  have hbr : bound ≤ r := by
    have hbx : bound ≤ x := (le_max_left _ _).trans hx
    dsimp [r]
    linarith [Real.add_one_le_exp x]
  have hMr : 0 < wvMaximumModulus h r := wvMaximumModulus_pos hh hn.exists_nonzero hr
  have hMe : Real.exp 1 < wvMaximumModulus h r := by
    apply (Real.lt_log_iff_exp_lt hMr).mp
    change 1 < wvLogMaximum h x
    linarith
  obtain ⟨z, hz, hzmax⟩ := wvMaximumModulus_attained hh.continuous hr.le
  have hhz : h z ≠ 0 := by
    intro he
    simp [he, ← hzmax] at hMr
  refine ⟨r, z, ν, hbr, hr1, hMe, hz, hzmax, by dsimp [ν]; linarith, ?_, ?_⟩
  · change ν ≤ 2 * (wvLogMaximum h x) ^ 2
    linarith [sq_nonneg (wvLogMaximum h x)]
  intro ζ hζ
  let τ : ℂ := ζ / (ν : ℂ)
  have hνpos : 0 < ν := by dsimp [ν]; linarith
  have hτ : ‖τ‖ ≤ ρ / 2 := by
    rw [show ‖τ‖ = ‖ζ‖ / ν by
      simp [τ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hνpos]]
    apply (div_le_iff₀ hνpos).mpr
    change 20 ≤ ν * ρ at hνρ
    linarith
  have hνζ : (ν : ℂ) * τ = ζ := by
    have hνne : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hνpos.ne'
    dsimp [τ]
    field_simp
  have hmono := wv_local_monomial_of_affine_bound hh hz hzmax hhz hρ
    (show 0 < 7 * η by positivity) (fun t ht => (le_abs_self _).trans (hflat t ht)) τ hτ
  rw [hνζ] at hmono
  have hden : h z * Complex.exp ζ ≠ 0 := mul_ne_zero hhz (Complex.exp_ne_zero _)
  rw [div_sub_one hden, norm_div]
  exact ((div_le_iff₀ (norm_pos_iff.mpr hden)).mpr hmono).trans
    ((le_abs_self _).trans hsmall.le)

/-- The reverse polynomial records the leading-term normalization at infinity. -/
private theorem eval_eq_reverse_mul_pow (p : Polynomial ℂ) {z : ℂ} (hz : z ≠ 0) :
    p.eval z = p.reverse.eval z⁻¹ * z ^ p.natDegree := by
  let := invertibleOfNonzero hz
  simpa [invOf_eq_inv] using
    (Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) z p).symm

private theorem exists_polynomial_maximum_data {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (pn : Polynomial ℂ) (hp : ∀ z, h z = pn.eval z)
    (hnon : ¬ ∀ z, h z = h 0) (bound : ℝ) :
    ∃ (r : ℝ) (z : ℂ) (ν : ℝ),
      bound ≤ r ∧ MaximumData h r z ν := by
  let d := pn.natDegree
  let a := pn.leadingCoeff
  have hd : 0 < d := by
    refine Nat.pos_of_ne_zero fun hd0 => hnon fun z => ?_
    rw [hp z, hp 0, Polynomial.eq_C_of_natDegree_eq_zero hd0]
    simp
  have ha : a ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro he
    simp [d, he] at hd
  let Q : ℂ → ℂ := fun u => pn.reverse.eval u / a
  have hQ0 : Q 0 = 1 := by
    change pn.reverse.eval 0 / a = 1
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
    exact div_self ha
  have hQc : ContinuousAt Q 0 :=
    (pn.reverse.differentiable.continuous.div_const a).continuousAt
  obtain ⟨δ, hδ, hδsmall⟩ := Metric.continuousAt_iff.mp hQc (1 / 300) (by norm_num)
  have hnear {u : ℂ} (hu : ‖u‖ < δ) : ‖Q u - 1‖ < 1 / 300 := by
    simpa [hQ0, Complex.dist_eq] using hδsmall (by simpa [Complex.dist_eq] using hu)
  have hlower {u : ℂ} (hu : ‖u‖ < δ) : 9 / 10 ≤ ‖Q u‖ := by
    have htr := norm_sub_norm_le (1 : ℂ) (Q u)
    rw [show (1 : ℂ) - Q u = -(Q u - 1) by ring, norm_neg, norm_one] at htr
    linarith [hnear hu]
  have hpQ {v : ℂ} (hv : v ≠ 0) : h v = a * v ^ d * Q v⁻¹ := by
    rw [hp v, eval_eq_reverse_mul_pow pn hv]
    dsimp [d, Q]
    field_simp
  obtain ⟨r, hr⟩ := exists_gt
    (max bound (max 1 (max (Real.exp 10 / δ) (2 * Real.exp ((d : ℝ) + 1) / ‖a‖))))
  have hbr : bound ≤ r := (le_max_left _ _).trans hr.le
  have hr1 : 1 ≤ r := ((le_max_left _ _).trans (le_max_right _ _)).trans hr.le
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrδ : Real.exp 10 / δ < r :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt ((le_max_right _ _).trans_lt hr)
  have hra : 2 * Real.exp ((d : ℝ) + 1) / ‖a‖ < r :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt ((le_max_right _ _).trans_lt hr)
  have hrad : δ⁻¹ < r * Real.exp (-10) := by
    rw [Real.exp_neg]
    apply (lt_div_iff₀ (Real.exp_pos _)).mpr
    rwa [mul_comm, ← div_eq_mul_inv]
  obtain ⟨z, hz, hzmax⟩ := wvMaximumModulus_attained hh.continuous hr0.le
  have hz0 : z ≠ 0 := by
    intro he
    simp [he] at hz
    linarith
  have hinv {v : ℂ} (hv : r * Real.exp (-10) ≤ ‖v‖) : ‖v⁻¹‖ < δ := by
    rw [norm_inv, inv_lt_comm₀ ((inv_pos.mpr hδ).trans_le (hrad.le.trans hv)) hδ]
    exact hrad.trans_le hv
  have hmodexp : r * Real.exp (-10) ≤ r :=
    mul_le_of_le_one_right hr0.le (Real.exp_le_one_iff.mpr (by norm_num))
  have hzinv : ‖z⁻¹‖ < δ := hinv (hz ▸ hmodexp)
  have halower : Real.exp ((d : ℝ) + 1) < wvMaximumModulus h r := by
    have hpow : r ≤ r ^ d := by
      simpa using pow_le_pow_right₀ hr1 (show 1 ≤ d from hd)
    have hra' : 2 * Real.exp ((d : ℝ) + 1) < r * ‖a‖ :=
      (div_lt_iff₀ (norm_pos_iff.mpr ha)).mp hra
    rw [← hzmax, hpQ hz0, norm_mul, norm_mul, norm_pow, hz]
    calc
      Real.exp ((d : ℝ) + 1) < ‖a‖ * r * (1 / 2) := by linarith
      _ ≤ ‖a‖ * r ^ d * ‖Q z⁻¹‖ := by
        gcongr
        linarith [hlower hzinv]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d from hd)
  have hMe := (Real.exp_lt_exp.mpr (show (1 : ℝ) < (d : ℝ) + 1 by linarith)).trans halower
  refine ⟨r, z, d, hbr, hr1, hMe, hz, hzmax, by linarith, ?_, ?_⟩
  · have hml := (Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans halower)).mpr halower
    nlinarith [sq_nonneg (Real.log (wvMaximumModulus h r) - 1)]
  intro ζ hζ
  let τ : ℂ := ζ / (d : ℂ)
  let w : ℂ := z * Complex.exp τ
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hw0 : w ≠ 0 := mul_ne_zero hz0 (Complex.exp_ne_zero _)
  have hτnorm : ‖τ‖ ≤ 10 := by
    have hτeq : ‖τ‖ = ‖ζ‖ / (d : ℝ) := by simp [τ]
    rw [hτeq]
    exact (div_le_self (norm_nonneg _) hd1).trans hζ
  have hτre : -10 ≤ τ.re :=
    neg_le_of_abs_le ((Complex.abs_re_le_norm τ).trans hτnorm)
  have hwinv : ‖w⁻¹‖ < δ := by
    apply hinv
    dsimp [w]
    rw [norm_mul, hz, Complex.norm_exp]
    gcongr
  have hwPow : w ^ d = z ^ d * Complex.exp ζ := by
    dsimp [w]
    rw [mul_pow, ← Complex.exp_nat_mul]
    congr 2
    dsimp [τ]
    field_simp
  have hQz0 : Q z⁻¹ ≠ 0 := by
    intro he
    have hcontr := hlower hzinv
    rw [he, norm_zero] at hcontr
    linarith
  have hzPow : z ^ d ≠ 0 := pow_ne_zero _ hz0
  have hratio : h w / (h z * Complex.exp ζ) = Q w⁻¹ / Q z⁻¹ := by
    rw [hpQ hw0, hpQ hz0, hwPow]
    field_simp [Complex.exp_ne_zero]
  change ‖h w / (h z * Complex.exp ζ) - 1‖ ≤ 1 / 100
  rw [hratio, div_sub_one hQz0, norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hQz0)).mpr
  have htr := norm_sub_le (Q w⁻¹ - 1) (Q z⁻¹ - 1)
  rw [sub_sub_sub_cancel_right] at htr
  linarith [hnear hzinv, hnear hwinv, hlower hzinv]

/-- At arbitrarily large radii, a nonconstant entire function is uniformly
approximated by an exponential in a rescaled coordinate at a maximum point. -/
theorem exists_maximum_data {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (hnon : ¬ ∀ z, h z = h 0) (bound : ℝ) :
    ∃ (r : ℝ) (z : ℂ) (ν : ℝ),
      bound ≤ r ∧ MaximumData h r z ν := by
  by_cases hn : WVNonPolynomial h
  · exact exists_transcendental_maximum_data hh hn bound
  · simp only [WVNonPolynomial, not_forall, not_exists, not_ne_iff] at hn
    obtain ⟨p, hp⟩ := hn
    exact exists_polynomial_maximum_data hh p hp hnon bound

end Bruck
