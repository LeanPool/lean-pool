/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.LogarithmicCorrection
public import LeanPool.Bruck.NearIdentity
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Quantitative inverse at a maximum-modulus point

The logarithmic error determines an inverse on a disk centered at the
negative imaginary axis. Its logarithmic derivative is uniformly small.
-/

@[expose] public section

open Metric Set
open scoped Topology

namespace Bruck

private theorem distortion_bound {ν R : ℝ} {w D second : ℂ}
    (hν : 1 / 2 ≤ ν) (hR : 0 < R) (hw : 9 / 10 * R < ‖w‖)
    (hD : 1 / 2 ≤ ‖D‖) (hsecond : ‖second‖ ≤ 1 / 5) :
    ‖1 / ((ν : ℂ) * w * D) - 1 / w - second / (w * D ^ 2)‖ ≤ 10 / R := by
  have hνp : 0 < ν := by linarith
  have hnormW : 0 < ‖w‖ := by linarith
  have hnormD : 0 < ‖D‖ := by linarith
  have first_bound : 1 / (ν * ‖w‖ * ‖D‖) ≤ 4 / ‖w‖ := by
    rw [show ν * ‖w‖ * ‖D‖ = ν * ‖D‖ * ‖w‖ by ring, ← div_div]
    gcongr
    apply (div_le_iff₀ (mul_pos hνp hnormD)).2
    nlinarith only [mul_le_mul hν hD (by positivity) hνp.le]
  have second_bound : ‖second‖ / (‖w‖ * ‖D‖ ^ 2) ≤ 4 / ‖w‖ := by
    rw [mul_comm ‖w‖, ← div_div]
    gcongr
    apply (div_le_iff₀ (pow_pos hnormD 2)).2
    nlinarith only [hsecond, mul_le_mul hD hD (by norm_num) hnormD.le]
  calc
    _ ≤ ‖1 / ((ν : ℂ) * w * D)‖ + ‖1 / w‖ + ‖second / (w * D ^ 2)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 4 / ‖w‖ + 1 / ‖w‖ + 4 / ‖w‖ := by
      simp only [norm_div, norm_one, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hνp.le, norm_pow]
      exact add_le_add (add_le_add first_bound le_rfl) second_bound
    _ = 9 / ‖w‖ := by ring
    _ ≤ 10 / R := by
      rw [div_le_div_iff₀ hnormW hR]
      linarith only [hw]

/-- Pointwise bounds and derivative information for a quantitative inverse branch. -/
structure InverseBranchData (h χ q : ℂ → ℂ) (pointBound radius : ℝ) (w : ℂ) : Prop where
  /-- Bound on the norm of the inverse image. -/
  image_bound : ‖χ w‖ ≤ 2 * pointBound
  /-- The inverse branch maps to the specified point under the original function. -/
  right_inverse : h (χ w) = w
  /-- The function `q` is the derivative of the inverse branch. -/
  hasDerivAt : HasDerivAt χ (q w) w
  /-- The derivative of the branch is nonzero. -/
  derivative_ne_zero : q w ≠ 0
  /-- The derivative of the branch is complex differentiable. -/
  differentiable_derivative : DifferentiableAt ℂ q w
  /-- Bound on the logarithmic derivative of the branch derivative. -/
  log_deriv_bound : ‖deriv q w / q w‖ ≤ 10 / radius

/-- The inverse branch from an exponential approximation. The radius
is the modulus of the image of the center of the chart. -/
theorem exists_quantitative_inverse {h : ℂ → ℂ}
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (hh₀ : h z₀ ≠ 0) {ν : ℝ} (hν : 1 / 2 ≤ ν)
    (hh : DifferentiableOn ℂ h ((fun ζ => z₀ * Complex.exp (ζ / (ν : ℂ))) '' ball 0 10))
    (happrox : ∀ ζ : ℂ, ‖ζ‖ ≤ 10 →
      ‖h (z₀ * Complex.exp (ζ / (ν : ℂ))) / (h z₀ * Complex.exp ζ) - 1‖ ≤ 1 / 100) :
    let R := ‖h z₀‖
    let c := -(R : ℂ) * Complex.I
    ∃ χ q : ℂ → ℂ,
      (∀ w ∈ ball c (R / 10), InverseBranchData h χ q ‖z₀‖ R w) ∧
      ‖z₀‖ / (2 * ν * R) ≤ ‖q c‖ ∧ ‖q c‖ ≤ 2 * ‖z₀‖ / (ν * R) := by
  dsimp only
  set R := ‖h z₀‖
  set c := -(R : ℂ) * Complex.I
  have hR : 0 < R := norm_pos_iff.2 hh₀
  have hνp : 0 < ν := by linarith
  have hνc : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hνp.ne'
  have hc : ‖c‖ = R := by simp [c, Complex.norm_real, abs_of_pos hR]
  have hcne : c ≠ 0 := by intro he; rw [he, norm_zero] at hc; linarith
  let F : ℂ → ℂ := fun ζ =>
    h (z₀ * Complex.exp (ζ / (ν : ℂ))) / (h z₀ * Complex.exp ζ)
  have hchart : Differentiable ℂ (fun ζ => z₀ * Complex.exp (ζ / (ν : ℂ))) :=
    (Complex.differentiable_exp.comp (differentiable_id.div_const (ν : ℂ))).const_mul z₀
  have hF : DifferentiableOn ℂ F (ball 0 10) :=
    (hh.comp hchart.differentiableOn (fun _ hz => mem_image_of_mem _ hz)).div
      (Complex.differentiable_exp.const_mul (h z₀)).differentiableOn
      (fun ζ _ => mul_ne_zero hh₀ (Complex.exp_ne_zero ζ))
  obtain ⟨J, hJ⟩ := exists_logarithmic_correction hF happrox
  obtain ⟨B, hB⟩ := exists_inverse_add (fun z hz => (hJ z hz).differentiable)
    (fun z hz => (hJ z hz).norm_bound) (fun z hz => (hJ z hz).deriv_bound)
  let δ : ℂ := (Complex.arg (c / h z₀) : ℂ) * Complex.I
  have hratio : ‖c / h z₀‖ = 1 := by rw [norm_div, hc, ← show R = ‖h z₀‖ from rfl, div_self hR.ne']
  have hδexp : Complex.exp δ = c / h z₀ := by
    simpa only [hratio, Complex.ofReal_one, one_mul, δ] using
      Complex.norm_mul_exp_arg_mul_I (c / h z₀)
  have hδre : δ.re = 0 := by simp [δ, Complex.mul_re]
  have hδnorm : ‖δ‖ ≤ Real.pi := by
    simpa [δ, norm_mul, Complex.norm_real] using Complex.abs_arg_le_pi (c / h z₀)
  let L : ℂ → ℂ := fun w => δ + Complex.log (w / c)
  have hwCL (w : ℂ) (hw : w ∈ ball c (R / 10)) : ‖w / c - 1‖ < 1 / 10 := by
    have hdist := mem_ball_iff_norm.mp hw
    rw [show w / c - 1 = (w - c) / c by field_simp, norm_div, hc, div_lt_iff₀ hR]
    linarith
  have hwnorm (w : ℂ) (hw : w ∈ ball c (R / 10)) : 9 / 10 * R < ‖w‖ := by
    have hdist := mem_ball_iff_norm.mp hw
    have htri := norm_sub_le w (w - c)
    rw [show w - (w - c) = c by ring, hc] at htri
    linarith
  have hwne (w : ℂ) (hw : w ∈ ball c (R / 10)) : w ≠ 0 :=
    norm_pos_iff.1 ((by positivity : 0 < 9 / 10 * R).trans (hwnorm w hw))
  have hL (w : ℂ) (hw : w ∈ ball c (R / 10)) : L w ∈ ball 0 8 := by
    apply mem_ball_zero_iff.2
    have hlog := norm_log_le_of_norm_sub_one_le_half ((hwCL w hw).le.trans (by norm_num))
    have htri := norm_add_le δ (Complex.log (w / c))
    change ‖L w‖ < 8
    linarith [hδnorm, hwCL w hw, Real.pi_lt_four]
  have hLexp (w : ℂ) (hw : w ∈ ball c (R / 10)) :
      h z₀ * Complex.exp (L w) = w := by
    change h z₀ * Complex.exp (δ + Complex.log (w / c)) = w
    rw [Complex.exp_add, hδexp, Complex.exp_log (div_ne_zero (hwne w hw) hcne)]
    field_simp
  have hLderiv (w : ℂ) (hw : w ∈ ball c (R / 10)) : HasDerivAt L w⁻¹ w := by
    have hslit := slitPlane_of_close_one ((hwCL w hw).trans (by norm_num))
    have hdiv := (hasDerivAt_id w).div_const c
    have hderiv := ((Complex.hasDerivAt_log hslit).comp w hdiv).const_add δ
    have heq : (w / c)⁻¹ * (1 / c) = w⁻¹ := by
      field_simp [hcne, hwne w hw]
    simpa only [heq, L, Function.comp_apply, id_eq] using hderiv
  let ζ : ℂ → ℂ := fun w => B (L w)
  let D : ℂ → ℂ := fun w => 1 + deriv J (ζ w)
  let χ : ℂ → ℂ := fun w => z₀ * Complex.exp (ζ w / (ν : ℂ))
  let q : ℂ → ℂ := fun w => χ w / ((ν : ℂ) * w * D w)
  have hζ (w : ℂ) (hw : w ∈ ball c (R / 10)) : ζ w ∈ ball 0 9 := (hB _ (hL w hw)).mem_disk
  have hDlo (w : ℂ) (hw : w ∈ ball c (R / 10)) : 9 / 10 ≤ ‖D w‖ := by
    have htri := norm_sub_le (D w) (deriv J (ζ w))
    rw [show D w - deriv J (ζ w) = 1 by simp [D], norm_one] at htri
    linarith [(hJ _ (hζ w hw)).deriv_bound]
  have hDhi (w : ℂ) (hw : w ∈ ball c (R / 10)) : ‖D w‖ ≤ 11 / 10 := by
    exact (norm_add_le (1 : ℂ) (deriv J (ζ w))).trans
      (by rw [norm_one]; linarith [(hJ _ (hζ w hw)).deriv_bound])
  have hDne (w : ℂ) (hw : w ∈ ball c (R / 10)) : D w ≠ 0 :=
    norm_pos_iff.1 ((by norm_num : (0 : ℝ) < 9 / 10).trans_le (hDlo w hw))
  have hχne (w : ℂ) : χ w ≠ 0 := mul_ne_zero hz₀ (Complex.exp_ne_zero _)
  have hχD (w : ℂ) (hw : w ∈ ball c (R / 10)) : HasDerivAt χ (q w) w := by
    have hBderiv : HasDerivAt (fun u => ζ u / (ν : ℂ))
        ((D w)⁻¹ * w⁻¹ / (ν : ℂ)) w :=
      ((hB _ (hL w hw)).hasDerivAt.comp w (hLderiv w hw)).div_const (ν : ℂ)
    have hderiv : HasDerivAt χ (χ w * ((D w)⁻¹ * w⁻¹ / (ν : ℂ))) w := by
      simpa only [χ, mul_assoc] using (hBderiv.cexp.const_mul z₀)
    have hqeq : q w = χ w * ((D w)⁻¹ * w⁻¹ / (ν : ℂ)) := by
      change χ w / ((ν : ℂ) * w * D w) = _
      field_simp [hνc, hwne w hw, hDne w hw]
    rwa [hqeq]
  have hχright (w : ℂ) (hw : w ∈ ball c (R / 10)) : h (χ w) = w := by
    have hac : ζ w + J (ζ w) = L w := (hB _ (hL w hw)).right_inverse
    have hFrel : Complex.exp (J (ζ w)) = F (ζ w) := (hJ _ (hζ w hw)).exp_eq
    calc
      h (χ w) = F (ζ w) * (h z₀ * Complex.exp (ζ w)) := by
        simp only [F, χ, div_mul_cancel₀ _ (mul_ne_zero hh₀ (Complex.exp_ne_zero _))]
      _ = h z₀ * Complex.exp (ζ w + J (ζ w)) := by rw [← hFrel, Complex.exp_add]; ring
      _ = w := by rw [hac, hLexp w hw]
  have hnormχ (w : ℂ) : ‖χ w‖ = ‖z₀‖ * Real.exp ((ζ w).re / ν) := by
    simp [χ, Complex.norm_exp, Complex.div_ofReal_re]
  have hζre (w : ℂ) (hw : w ∈ ball c (R / 10)) : (ζ w).re ≤ 1 / 5 := by
    have hdist := (hB _ (hL w hw)).displacement_bound
    have hre := (abs_le.mp (Complex.abs_re_le_norm (ζ w - L w))).2
    rw [Complex.sub_re] at hre
    have hn : ‖w / c‖ ≤ 11 / 10 := by
      have htri := norm_add_le (w / c - 1) (1 : ℂ)
      rw [sub_add_cancel, norm_one] at htri
      linarith [hwCL w hw]
    have hlog := Real.log_le_sub_one_of_pos (norm_pos_iff.2 (div_ne_zero (hwne w hw) hcne))
    rw [show (L w).re = Real.log ‖w / c‖ by simp [L, Complex.add_re, hδre, Complex.log_re]] at hre
    linarith
  have hχnorm (w : ℂ) (hw : w ∈ ball c (R / 10)) : ‖χ w‖ ≤ 2 * ‖z₀‖ := by
    rw [hnormχ]
    have hh := hζre w hw
    have hb : (ζ w).re / ν ≤ 2 / 5 := (div_le_iff₀ hνp).2 (by linarith)
    calc
      _ ≤ ‖z₀‖ * Real.exp (2 / 5) := by gcongr
      _ ≤ 2 * ‖z₀‖ := by
        have h := Real.exp_bound_div_one_sub_of_interval (x := 2 / 5) (by norm_num) (by norm_num)
        norm_num at h
        nlinarith [norm_nonneg z₀, mul_nonneg (norm_nonneg z₀) (sub_nonneg.2 h)]
  have hqne (w : ℂ) (hw : w ∈ ball c (R / 10)) : q w ≠ 0 :=
    div_ne_zero (hχne w) (mul_ne_zero (mul_ne_zero hνc (hwne w hw)) (hDne w hw))
  have hderivQ (w : ℂ) (hw : w ∈ ball c (R / 10)) :
      DifferentiableAt ℂ q w ∧
        deriv q w / q w =
          1 / ((ν : ℂ) * w * D w) - 1 / w - deriv (deriv J) (ζ w) / (w * (D w)^2) := by
    have hζd : HasDerivAt ζ ((D w)⁻¹ * w⁻¹) w :=
      (hB _ (hL w hw)).hasDerivAt.comp w (hLderiv w hw)
    have hDd : HasDerivAt D (deriv (deriv J) (ζ w) * ((D w)⁻¹ * w⁻¹)) w :=
      (((hJ _ (hζ w hw)).differentiable_deriv).hasDerivAt.comp w hζd).const_add 1
    let νw : ℂ → ℂ := fun u => (ν : ℂ) * u
    have hνw : HasDerivAt νw ((ν : ℂ) * 1) w := (hasDerivAt_id w).const_mul (ν : ℂ)
    have hνwne : νw w ≠ 0 := mul_ne_zero hνc (hwne w hw)
    have hden := mul_ne_zero hνwne (hDne w hw)
    have hχd := hχD w hw
    have hχdifferentiable := hχd.differentiableAt
    have hdenDifferentiable := (hνw.mul hDd).differentiableAt
    refine ⟨hχdifferentiable.div hdenDifferentiable hden, ?_⟩
    change logDeriv (χ / (νw * D)) w = _
    rw [logDeriv_div w (hχne w) hden hχdifferentiable hdenDifferentiable,
      logDeriv_mul w hνwne (hDne w hw) hνw.differentiableAt hDd.differentiableAt]
    have first : logDeriv χ w = 1 / ((ν : ℂ) * w * D w) := by
      rw [logDeriv_apply, hχd.deriv]
      change (χ w / ((ν : ℂ) * w * D w)) / χ w = _
      field_simp [hχne w]
    have last : logDeriv D w = deriv (deriv J) (ζ w) / (w * (D w) ^ 2) := by
      rw [logDeriv_apply, hDd.deriv]
      field_simp [hwne w hw, hDne w hw]
    rw [first, last, show logDeriv νw w = 1 / w from
      (logDeriv_const_mul (f := id) w _ hνc).trans (logDeriv_id w)]
    ring
  have hdistortion (w : ℂ) (hw : w ∈ ball c (R / 10)) :
      ‖deriv q w / q w‖ ≤ 10 / R := by
    rw [(hderivQ w hw).2]
    exact distortion_bound hν hR (hwnorm w hw)
      ((by norm_num : (1 / 2 : ℝ) ≤ 9 / 10).trans (hDlo w hw)) (hJ _ (hζ w hw)).second_deriv_bound
  refine ⟨χ, q, fun w hw => ⟨hχnorm w hw, hχright w hw, hχD w hw, hqne w hw,
    (hderivQ w hw).1, hdistortion w hw⟩, ?_⟩
  have hcc : c ∈ ball c (R / 10) := mem_ball_self (by positivity)
  have hLc : L c = δ := by simp [L, hcne]
  have hζcre : |(ζ c).re| ≤ 1 / 10 := by
    have habs := Complex.abs_re_le_norm (ζ c - L c)
    have hcap : (L c).re = 0 := hLc ▸ hδre
    rw [Complex.sub_re, hcap, sub_zero] at habs
    exact habs.trans (hB _ (hL c hcc)).displacement_bound
  have hrelo : -(1 / 5 : ℝ) ≤ (ζ c).re / ν := by
    apply (le_div_iff₀ hνp).2
    linarith [(abs_le.mp hζcre).1]
  have hrehi : (ζ c).re / ν ≤ 1 / 5 := by
    apply (div_le_iff₀ hνp).2
    linarith [(abs_le.mp hζcre).2]
  have hχlo : (4 / 5 : ℝ) * ‖z₀‖ ≤ ‖χ c‖ := by
    have he : (4 / 5 : ℝ) ≤ Real.exp (-(1 / 5 : ℝ)) := by
      linarith [Real.add_one_le_exp (-(1 / 5 : ℝ))]
    rw [hnormχ, mul_comm (4 / 5 : ℝ)]
    exact mul_le_mul_of_nonneg_left (he.trans (Real.exp_le_exp.mpr hrelo)) (norm_nonneg z₀)
  have hχhi : ‖χ c‖ ≤ (5 / 4 : ℝ) * ‖z₀‖ := by
    have he : Real.exp (1 / 5) ≤ (5 / 4 : ℝ) := by
      convert Real.exp_bound_div_one_sub_of_interval (x := 1 / 5)
        (by norm_num) (by norm_num) using 1
      norm_num
    rw [hnormχ, mul_comm (5 / 4 : ℝ)]
    exact mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr hrehi).trans he) (norm_nonneg z₀)
  have hDn : 0 < ‖D c‖ := norm_pos_iff.2 (hDne c hcc)
  rw [show ‖q c‖ = ‖χ c‖ / (ν * R * ‖D c‖) by
    simp only [q, norm_div, norm_mul, hc, Complex.norm_real, Real.norm_of_nonneg hνp.le]]
  have hscale : 0 < ν * R := mul_pos hνp hR
  have hnz : 0 ≤ ‖z₀‖ := norm_nonneg z₀
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 2 * ν * R) (by positivity : 0 < ν * R * ‖D c‖)]
    have hb₁ : ‖z₀‖ * ‖D c‖ ≤ (11 / 10 : ℝ) * ‖z₀‖ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hDhi c hcc) hnz
    have hb₂ : ‖z₀‖ * ‖D c‖ ≤ 2 * ‖χ c‖ := by linarith
    nlinarith only [mul_le_mul_of_nonneg_right hb₂ hscale.le]
  · rw [div_le_div_iff₀ (by positivity : 0 < ν * R * ‖D c‖) hscale]
    have hb₁ : (9 / 10 : ℝ) * ‖z₀‖ ≤ ‖z₀‖ * ‖D c‖ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hDlo c hcc) hnz
    have hb₂ : ‖χ c‖ ≤ 2 * (‖z₀‖ * ‖D c‖) := by linarith
    nlinarith only [mul_le_mul_of_nonneg_right hb₂ hscale.le]

end Bruck
