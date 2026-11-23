/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.GrowthFacts
public import LeanPool.Bruck.HyperOrder
public import TauCeti.Analysis.Complex.GrowthOrder
import LeanPool.Bruck.HyperOrderComparison
import TauCeti.Analysis.Complex.GrowthOrder.Exponential

/-! # Ordinary order of entire functions -/

@[expose] public section

open Asymptotics Bornology Filter Set
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
    (hdnon : ¬ ∀ z, deriv f z = deriv f 0) :
    ordinaryOrder (deriv f) = ordinaryOrder f := by
  have hnon : ¬ ∀ z, f z = f 0 := by
    intro hconst
    apply hdnon
    intro z
    rw [show f = fun _ => f 0 from funext hconst]
    simp only [deriv_const]
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

private theorem eventually_log_maximumModulus_exp_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    ∀ᶠ r in atTop, Real.log (wvMaximumModulus (fun z => Complex.exp (f z)) r) ≤
      wvMaximumModulus f r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hpos := wvMaximumModulus_pos hf.cexp ⟨0, Complex.exp_ne_zero (f 0)⟩ hr
  exact (Real.log_le_iff_le_exp hpos).2 (maximumModulus_exp_le hf.continuous hr.le)

/-- Exponentiation converts the logarithmic order of the maximum modulus
into ordinary order. -/
theorem ordinaryOrder_exp_comp_eq_logOrder {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnon : ¬ ∀ z, f z = f 0) :
    ordinaryOrder (fun z => Complex.exp (f z)) = logOrder (wvMaximumModulus f) := by
  have hM := maximumModulus_tendsto_atTop hf hnon
  have hL := logMaximumModulus_tendsto_atTop hf.cexp (nonconstant_exp_comp hf hnon)
  apply le_antisymm
  · apply logOrder_le_of_eventually_le_affine (a := 1) (k := 1) (c := 0)
      (by norm_num) le_rfl (hL.eventually_gt_atTop 0) hM
    simpa only [one_mul, add_zero] using eventually_log_maximumModulus_exp_le hf
  · exact logOrder_le_of_eventually_le_affine (a := 2) (k := 2) (c := 3 * ‖f 0‖)
      (by norm_num) (by positivity) (hM.eventually_gt_atTop 0) hL
      (maximumModulus_le_log_maximumModulus_exp hf hnon)

private theorem logOrder_doubleLog_maximumModulus_exp_eq_ordinaryOrder {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnon : ¬ ∀ z, f z = f 0) :
    logOrder (fun r => Real.log (Real.log
      (wvMaximumModulus (fun z => Complex.exp (f z)) r))) = ordinaryOrder f := by
  let Q := fun z => Complex.exp (f z)
  have hd : Differentiable ℂ Q := hf.cexp
  have hqnon := nonconstant_exp_comp hf hnon
  have hM := maximumModulus_tendsto_atTop hf hnon
  have hL := logMaximumModulus_tendsto_atTop hd hqnon
  change logOrder (fun r => Real.log (Real.log (wvMaximumModulus Q r))) =
    logOrder (fun r => Real.log (wvMaximumModulus f r))
  apply le_antisymm
  · apply logOrder_log_le_of_eventually_le_affine (a := 1) (k := 1) (c := 0)
      (by norm_num) le_rfl hL hM
    simpa only [one_mul, add_zero] using eventually_log_maximumModulus_exp_le hf
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

/-- A numerical bound on ordinary order implies an exponential envelope outside bounded sets. -/
theorem orderLE_of_ordinaryOrder_le {f : ℂ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hf : Differentiable ℂ f) (hnon : ¬ ∀ z, f z = f 0)
    (horder : ordinaryOrder f ≤ ENNReal.ofReal a) : TauCeti.OrderLE f a := by
  rw [TauCeti.orderLE_def]
  intro b hb
  have hpow := eventually_le_rpow_of_logOrder_lt
    ((logMaximumModulus_tendsto_atTop hf hnon).eventually_gt_atTop 0)
    (horder.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).2 hb))
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [tendsto_norm_cobounded_atTop.eventually hpow,
    eventually_cobounded_le_norm (E := ℂ) 1] with z hz hnorm
  have hex : ∃ u, f u ≠ 0 := by
    by_contra! hzero
    exact hnon fun u => by rw [hzero u, hzero 0]
  have hmpos := wvMaximumModulus_pos hf hex (zero_lt_one.trans_le hnorm)
  have hm := (Real.log_le_iff_le_exp hmpos).mp hz
  simpa only [one_mul, Real.norm_of_nonneg (Real.exp_nonneg _)] using
    (wv_norm_le_maximumModulus hf.continuous rfl).trans hm

/-- Exponential envelopes in Tau Ceti bound the numerical ordinary order. -/
theorem ordinaryOrder_le_of_orderLE {f : ℂ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hf : Differentiable ℂ f) (hnon : ¬ ∀ z, f z = f 0)
    (horder : TauCeti.OrderLE f a) : ordinaryOrder f ≤ ENNReal.ofReal a := by
  by_contra! hlt
  obtain ⟨b, hb, hbf⟩ := exists_between hlt
  have hbt := (hbf.trans_le le_top).ne
  have hab : a < b.toReal := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mp
    (by simpa only [ENNReal.ofReal_toReal hbt] using hb)
  obtain ⟨C, hC⟩ := isBigO_iff.mp (horder.isBigO hab)
  let bad : Set ℂ := {z | ¬ ‖f z‖ ≤ C * ‖Real.exp (‖z‖ ^ b.toReal)‖}
  have hbad : IsBounded bad := by
    rw [isBounded_def]
    exact hC.mono fun z hz => by simpa [bad] using hz
  obtain ⟨R, hR⟩ := hbad.exists_norm_le
  let A := max C 1
  have hA : 1 ≤ A := le_max_right _ _
  have hApos := zero_lt_one.trans_le hA
  have hlogA := Real.log_nonneg hA
  have hF := (logMaximumModulus_tendsto_atTop hf hnon).eventually_gt_atTop 0
  have hG : ∀ᶠ r : ℝ in atTop, 0 < r ^ b.toReal :=
    (eventually_gt_atTop 0).mono fun _ hr => Real.rpow_pos_of_pos hr _
  have hcomp : ordinaryOrder f ≤ logOrder (fun r : ℝ => r ^ b.toReal) := by
    apply logOrder_le_of_eventually_le_scaled (a := Real.log A + 1) (k := 1)
      (by positivity) (by norm_num) hF hG
    filter_upwards [eventually_gt_atTop (max R 1), hF] with r hr hMr
    have hr1 := (le_max_right R 1).trans_lt hr
    obtain ⟨z, hz, hzmax⟩ := wvMaximumModulus_attained hf.continuous
      (zero_lt_one.trans hr1).le
    have hpoint : ‖f z‖ ≤ C * ‖Real.exp (‖z‖ ^ b.toReal)‖ := by
      by_contra h
      have hzR := hR z (show z ∈ bad from h)
      exact (not_le_of_gt ((le_max_left R 1).trans_lt hr)) (hz ▸ hzR)
    have hm : wvMaximumModulus f r ≤ A * Real.exp (r ^ b.toReal) := by
      rw [← hzmax]
      rw [hz, Real.norm_of_nonneg (Real.exp_nonneg _)] at hpoint
      exact hpoint.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
    have hmpos := zero_lt_one.trans
      ((Real.log_pos_iff (wvMaximumModulus_nonneg f r)).mp hMr)
    have hlog := Real.log_le_log hmpos hm
    rw [Real.log_mul hApos.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    have hrpow : 1 ≤ r ^ b.toReal := Real.one_le_rpow hr1.le ENNReal.toReal_nonneg
    simp only [one_mul]
    nlinarith [mul_nonneg hlogA (sub_nonneg.mpr hrpow)]
  have hbound := hcomp.trans
    (logOrder_le_of_eventually_rpow hG (Eventually.of_forall fun _ => le_rfl))
  exact (not_le_of_gt hbf) (by simpa only [ENNReal.ofReal_toReal hbt] using hbound)

theorem ordinaryOrder_exp_polynomial_eq_natDegree (p : Polynomial ℂ) (hp : 0 < p.natDegree) :
    ordinaryOrder (fun z => Complex.exp (p.eval z)) = p.natDegree := by
  let f : ℂ → ℂ := fun z => Complex.exp (p.eval z)
  have hf : Differentiable ℂ f := p.differentiable.cexp
  have hn : ¬ ∀ z, f z = f 0 :=
    nonconstant_exp_comp p.differentiable ((polynomial_eval_nonconstant_iff p).mpr hp)
  have hTau : TauCeti.OrderLE f (p.natDegree : ℝ) :=
    TauCeti.orderLE_cexp_polynomial_eval_iff.mpr (by simp)
  have hu := ordinaryOrder_le_of_orderLE (Nat.cast_nonneg p.natDegree) hf hn hTau
  have hu' : ordinaryOrder f ≤ (p.natDegree : ℝ≥0∞) := by simpa using hu
  have htop : ordinaryOrder f ≠ ⊤ :=
    (hu'.trans_lt (lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top _))).ne
  have hTau' := orderLE_of_ordinaryOrder_le (a := (ordinaryOrder f).toReal)
    ENNReal.toReal_nonneg hf hn
    (by rw [ENNReal.ofReal_toReal htop])
  have hdegree := TauCeti.orderLE_cexp_polynomial_eval_iff.mp hTau'
  have hl : (p.natDegree : ℝ) ≤ (ordinaryOrder f).toReal := (Nat.le_floor_iff' hp.ne').mp hdegree
  apply le_antisymm hu'
  simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_toReal htop] using ENNReal.ofReal_mono hl

theorem ordinaryOrder_polynomial_eq_zero (p : Polynomial ℂ) (hp : 0 < p.natDegree) :
    ordinaryOrder p.eval = 0 := by
  apply le_antisymm _ zero_le
  simpa only [ENNReal.ofReal_zero] using ordinaryOrder_le_of_orderLE
    le_rfl p.differentiable ((polynomial_eval_nonconstant_iff p).mpr hp) p.orderLE_eval

/-- Finite-order nowhere-zero entire functions are exponentials of polynomials. -/
theorem exists_exp_polynomial_of_finite_ordinaryOrder {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnz : ∀ z, f z ≠ 0) (hord : ordinaryOrder f < ⊤) :
    ∃ p : Polynomial ℂ, ∀ z, f z = Complex.exp (p.eval z) := by
  by_cases hnon : ¬ ∀ z, f z = f 0
  · have hTau := orderLE_of_ordinaryOrder_le (a := (ordinaryOrder f).toReal)
      ENNReal.toReal_nonneg hf hnon
      (by rw [ENNReal.ofReal_toReal hord.ne])
    obtain ⟨p, _, hp⟩ := hTau.exists_eq_cexp_polynomial_eval_of_forall_ne_zero hf hnz
    exact ⟨p, hp⟩
  · have hc : ∀ z, f z = f 0 := not_not.mp hnon
    exact ⟨Polynomial.C (Complex.log (f 0)), fun z => by
      rw [Polynomial.eval_C, Complex.exp_log (hnz 0), hc z]⟩

end Bruck
