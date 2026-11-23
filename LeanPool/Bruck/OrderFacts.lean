/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.GrowthFacts
public import LeanPool.Bruck.HyperOrder
import LeanPool.Bruck.HyperOrderComparison
import LeanPool.Bruck.Sharing

/-! # Ordinary order of entire functions -/

@[expose] public section

open Filter
open scoped ENNReal

namespace Bruck

/-- Ordinary order computed using the maximum modulus. -/
noncomputable def ordinaryOrder (f : ℂ → ℂ) : ℝ≥0∞ :=
  logOrder (fun r => Real.log (wvMaximumModulus f r))

private theorem logMaximumModulus_tendsto_atTop {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnon : ¬ ∀ z, f z = f 0) :
    Tendsto (fun r => Real.log (wvMaximumModulus f r)) atTop atTop :=
  Real.tendsto_log_atTop.comp (maximumModulus_tendsto_atTop hf hnon)

theorem ordinaryOrder_deriv_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnon : ¬ ∀ z, f z = f 0) (hdnon : ¬ ∀ z, deriv f z = deriv f 0) :
    ordinaryOrder (deriv f) = ordinaryOrder f := by
  have hd : Differentiable ℂ (deriv f) := hf.deriv
  have hMf := maximumModulus_tendsto_atTop hf hnon
  have hMd := maximumModulus_tendsto_atTop hd hdnon
  apply le_antisymm
  · apply logOrder_log_le_of_eventually_le_affine (a := 1) (k := 2) (c := 0)
      (by norm_num) le_rfl hMd hMf
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have h := maximumModulus_deriv_le hf (zero_lt_one.trans_le hr)
    simpa only [one_mul, add_zero] using h.trans
      (div_le_self (wvMaximumModulus_nonneg f _) hr)
  · obtain ⟨c, hc, hlow⟩ := exists_linear_le_maximumModulus hd hdnon
    let A := max 1 (c⁻¹ + ‖f 0‖)
    have hA1 : 1 ≤ A := le_max_left _ _
    have hA0 : 0 < A := zero_lt_one.trans_le hA1
    have hFpos := (logMaximumModulus_tendsto_atTop hf hnon).eventually_gt_atTop 0
    have hGpos := (logMaximumModulus_tendsto_atTop hd hdnon).eventually_gt_atTop 0
    apply logOrder_le_of_eventually_le_scaled (a := 3) (k := 1)
      (by norm_num) (by norm_num) hFpos hGpos
    filter_upwards [eventually_ge_atTop (1 : ℝ), hMf.eventually_gt_atTop 0,
      hMd.eventually_ge_atTop A] with r hr hMr hAr
    let m := wvMaximumModulus (deriv f) r
    have hm1 : 1 ≤ m := hA1.trans hAr
    have hm0 : 0 < m := zero_lt_one.trans_le hm1
    have hpow1 : 1 ≤ m ^ 2 := one_le_pow₀ hm1
    have hrle : r ≤ m / c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hlow r hr)
    have hpoly : wvMaximumModulus f r ≤ A * m ^ 2 := by
      calc
        wvMaximumModulus f r ≤ ‖f 0‖ + r * m :=
          maximumModulus_le_deriv_bound hf (zero_lt_one.trans_le hr)
        _ ≤ ‖f 0‖ + (m / c) * m := by gcongr
        _ ≤ ‖f 0‖ * m ^ 2 + (m / c) * m :=
          add_le_add (le_mul_of_one_le_right (norm_nonneg _) hpow1) le_rfl
        _ = (c⁻¹ + ‖f 0‖) * m ^ 2 := by rw [div_eq_mul_inv]; ring
        _ ≤ A * m ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg m)
    rw [one_mul]
    change Real.log (wvMaximumModulus f r) ≤ 3 * Real.log m
    calc
      Real.log (wvMaximumModulus f r) ≤ Real.log (A * m ^ 2) := Real.log_le_log hMr hpoly
      _ = Real.log A + 2 * Real.log m := by
        rw [Real.log_mul hA0.ne' (pow_ne_zero _ hm0.ne'), Real.log_pow]
        norm_num
      _ ≤ 3 * Real.log m := by linarith [Real.log_le_log hA0 hAr]

/-- Exponentiation converts the logarithmic order of the maximum modulus
into ordinary order. -/
theorem ordinaryOrder_exp_comp_eq_logOrder {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnon : ¬ ∀ z, f z = f 0) :
    ordinaryOrder (fun z => Complex.exp (f z)) = logOrder (wvMaximumModulus f) := by
  let Q := fun z => Complex.exp (f z)
  have hd : Differentiable ℂ Q := hf.cexp
  have hqnon := nonconstant_exp_comp hf hnon
  have hM := maximumModulus_tendsto_atTop hf hnon
  have hQ := maximumModulus_tendsto_atTop hd hqnon
  have hL := logMaximumModulus_tendsto_atTop hd hqnon
  have hMpos := hM.eventually_gt_atTop 0
  have hLpos := hL.eventually_gt_atTop 0
  change logOrder (fun r => Real.log (wvMaximumModulus Q r)) = logOrder (wvMaximumModulus f)
  apply le_antisymm
  · apply logOrder_le_of_eventually_le_scaled (a := 1) (k := 1)
      (by norm_num) (by norm_num) hLpos hMpos
    filter_upwards [eventually_ge_atTop (0 : ℝ), hQ.eventually_gt_atTop 0] with r hr hqpos
    simpa only [one_mul] using
      (Real.log_le_iff_le_exp hqpos).2 (maximumModulus_exp_le hf.continuous hr)
  · let A := 2 + 3 * ‖f 0‖
    have hA : 0 < A := by dsimp [A]; positivity
    apply logOrder_le_of_eventually_le_scaled (a := A) (k := 2) hA (by norm_num) hMpos hLpos
    have hscale : Tendsto (fun r : ℝ => 2 * r) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
    filter_upwards [maximumModulus_le_log_maximumModulus_exp hf hnon,
      (hL.comp hscale).eventually_ge_atTop 1] with r hBC hlarge
    let m := Real.log (wvMaximumModulus Q (2 * r))
    change 1 ≤ m at hlarge
    calc
      wvMaximumModulus f r ≤ 2 * m + 3 * ‖f 0‖ := hBC
      _ ≤ 2 * m + 3 * ‖f 0‖ * m :=
        add_le_add le_rfl (le_mul_of_one_le_right (by positivity) hlarge)
      _ = A * m := by dsimp only [A]; ring

private theorem logOrder_doubleLog_maximumModulus_exp_eq_ordinaryOrder {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnon : ¬ ∀ z, f z = f 0) :
    logOrder (fun r => Real.log (Real.log
      (wvMaximumModulus (fun z => Complex.exp (f z)) r))) = ordinaryOrder f := by
  let Q := fun z => Complex.exp (f z)
  have hd : Differentiable ℂ Q := hf.cexp
  have hqnon := nonconstant_exp_comp hf hnon
  have hM := maximumModulus_tendsto_atTop hf hnon
  have hQ := maximumModulus_tendsto_atTop hd hqnon
  have hL := logMaximumModulus_tendsto_atTop hd hqnon
  change logOrder (fun r => Real.log (Real.log (wvMaximumModulus Q r))) =
    logOrder (fun r => Real.log (wvMaximumModulus f r))
  apply le_antisymm
  · apply logOrder_log_le_of_eventually_le_affine (a := 1) (k := 1) (c := 0)
      (by norm_num) le_rfl hL hM
    filter_upwards [eventually_ge_atTop (0 : ℝ), hQ.eventually_gt_atTop 0] with r hr hqpos
    simpa only [one_mul, add_zero] using
      (Real.log_le_iff_le_exp hqpos).2 (maximumModulus_exp_le hf.continuous hr)
  · exact logOrder_log_le_of_eventually_le_affine (a := 2) (k := 2) (c := 3 * ‖f 0‖)
      (by norm_num) (by positivity) hM hL
      (maximumModulus_le_log_maximumModulus_exp hf hnon)

/-- The hyper-order of the exponential of a nonconstant entire function
is the ordinary order of that function. -/
theorem hyperOrder_exp_comp_eq_ordinaryOrder {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnon : ¬ ∀ z, f z = f 0) :
    hyperOrder (fun z => Complex.exp (f z)) = ordinaryOrder f :=
  (hyperOrder_eq_logOrder_maximumModulus hf.cexp (nonconstant_exp_comp hf hnon)).trans
    (logOrder_doubleLog_maximumModulus_exp_eq_ordinaryOrder hf hnon)

private theorem logOrder_pow (d : ℕ) : logOrder (fun r : ℝ => r ^ d) = d := by
  have hpow : ∀ᶠ r : ℝ in atTop, r ^ (d : ℝ) ≤ r ^ d :=
    Eventually.of_forall fun r => (Real.rpow_natCast r d).le
  have hpos : ∀ᶠ r : ℝ in atTop, 0 < r ^ d :=
    (eventually_gt_atTop 0).mono fun _ hr => pow_pos hr _
  apply le_antisymm
  · rw [← ENNReal.ofReal_natCast d]
    exact logOrder_le_of_eventually_rpow hpos (Eventually.of_forall fun r =>
      (Real.rpow_natCast r d).symm.le)
  · simpa only [ENNReal.ofReal_natCast] using le_logOrder_of_frequently_rpow hpow.frequently

theorem ordinaryOrder_exp_polynomial_eq_natDegree (p : Polynomial ℂ) (hp : 0 < p.natDegree) :
    ordinaryOrder (fun z => Complex.exp (p.eval z)) = p.natDegree := by
  have hnon := polynomial_eval_nonconstant p hp
  rw [ordinaryOrder_exp_comp_eq_logOrder p.differentiable hnon, ← logOrder_pow p.natDegree]
  have hMpos := (maximumModulus_tendsto_atTop p.differentiable hnon).eventually_gt_atTop 0
  have hpowpos : ∀ᶠ r : ℝ in atTop, 0 < r ^ p.natDegree :=
    (eventually_gt_atTop 0).mono fun _ hr => pow_pos hr _
  apply le_antisymm
  · obtain ⟨C, hC, hupper⟩ := polynomial_maximumModulus_le p
    apply logOrder_le_of_eventually_le_scaled (a := C) (k := 1)
      hC (by norm_num) hMpos hpowpos
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    simpa only [one_mul] using hupper r hr
  · have hp0 : p ≠ 0 := by intro he; simp [he] at hp
    have hc : 0 < ‖p.leadingCoeff‖ := norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp0)
    apply logOrder_le_of_eventually_le_scaled (a := ‖p.leadingCoeff‖⁻¹) (k := 1)
      (inv_pos.mpr hc) (by norm_num) hpowpos hMpos
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    simpa only [one_mul, ← div_eq_inv_mul] using
      (le_div_iff₀ hc).mpr (by simpa [mul_comm] using
        polynomial_leadingCoeff_mul_pow_le_maximumModulus p hr)

private theorem logOrder_log_eq_zero : logOrder Real.log = 0 := by
  apply le_antisymm _ zero_le
  by_contra! hpos
  obtain ⟨a, ha, hasmall⟩ := exists_between hpos
  have hatop : a ≠ ⊤ := (hasmall.trans_le le_top).ne
  have har : 0 < a.toReal := ENNReal.toReal_pos ha.ne' hatop
  have hlo := (eventually_gt_atTop (1 : ℝ)).mono fun _ hr => Real.log_pos hr
  have hevt : ∀ᶠ r : ℝ in atTop, Real.log r ≤ r ^ a.toReal := by
    filter_upwards [(isLittleO_log_rpow_atTop har).bound (show (0 : ℝ) < 1 by norm_num),
      eventually_gt_atTop (0 : ℝ)] with r hr hrpos
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hrpos.le _)] at hr
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hr)
  have hle := logOrder_le_of_eventually_rpow hlo hevt
  rw [ENNReal.ofReal_toReal hatop] at hle
  exact not_lt_of_ge hle hasmall

theorem ordinaryOrder_polynomial_eq_zero (p : Polynomial ℂ) (hp : 0 < p.natDegree) :
    ordinaryOrder p.eval = 0 := by
  apply le_antisymm _ zero_le
  rw [← logOrder_log_eq_zero]
  obtain ⟨C, hc, hu⟩ := polynomial_maximumModulus_le p
  let A := (p.natDegree : ℝ) + |Real.log C|
  have hA : 0 < A := add_pos_of_pos_of_nonneg (by exact_mod_cast hp) (abs_nonneg _)
  have hn := polynomial_eval_nonconstant p hp
  have hM := maximumModulus_tendsto_atTop p.differentiable hn
  have hF := (logMaximumModulus_tendsto_atTop p.differentiable hn).eventually_gt_atTop 0
  have hG := Real.tendsto_log_atTop.eventually_gt_atTop 0
  apply logOrder_le_of_eventually_le_scaled (a := A) (k := 1) hA (by norm_num) hF hG
  filter_upwards [eventually_ge_atTop (1 : ℝ), hM.eventually_gt_atTop 0,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with r hr hMr hL
  have hrpos := zero_lt_one.trans_le hr
  rw [one_mul]
  calc
    Real.log (wvMaximumModulus p.eval r) ≤ Real.log (C * r ^ p.natDegree) :=
      Real.log_le_log hMr (hu r hr)
    _ = Real.log C + (p.natDegree : ℝ) * Real.log r := by
      rw [Real.log_mul hc.ne' (pow_ne_zero _ hrpos.ne'), Real.log_pow]
    _ ≤ A * Real.log r := by
      have h := le_mul_of_one_le_right (abs_nonneg (Real.log C)) hL
      dsimp only [A]
      linarith [le_abs_self (Real.log C)]

/-- Finite-order nowhere-zero entire functions are exponentials of polynomials. -/
theorem exists_exp_polynomial_of_finite_ordinaryOrder {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnz : ∀ z, f z ≠ 0) (hord : ordinaryOrder f < ⊤) :
    ∃ p : Polynomial ℂ, ∀ z, f z = Complex.exp (p.eval z) := by
  obtain ⟨g, hg, hfg⟩ := exists_entire_log hf hnz
  by_cases hnon : ¬ ∀ z, g z = g 0
  · have heq : (fun z => Complex.exp (g z)) = f := funext hfg
    have hfin : logOrder (wvMaximumModulus g) < ⊤ := by
      rwa [← ordinaryOrder_exp_comp_eq_logOrder hg hnon, heq]
    obtain ⟨n, hn⟩ := exists_nat_gt (logOrder (wvMaximumModulus g)).toReal
    have hN : logOrder (wvMaximumModulus g) < ENNReal.ofReal (n : ℝ) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hfin.ne]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 hn
    have hpos := (maximumModulus_tendsto_atTop hg hnon).eventually_gt_atTop 0
    have hbound := eventually_le_rpow_of_logOrder_lt hpos hN
    obtain ⟨p, hp⟩ := exists_polynomial_of_maximumModulus_le_pow hg (C := 1) (d := n)
      (by simpa only [one_mul, Real.rpow_natCast] using hbound)
    exact ⟨p, fun z => by rw [← hp z, hfg]⟩
  · have hc : ∀ z, g z = g 0 := not_not.mp hnon
    exact ⟨Polynomial.C (g 0), fun z => by rw [Polynomial.eval_C, ← hc z, hfg]⟩

end Bruck
