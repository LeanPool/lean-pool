/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.Contour

/-! # A local double-exponential bound for solutions of the differential equation -/

@[expose] public section

namespace Bruck

open Complex Set Metric Filter

private theorem logarithmic_derivative_distortion {q : ℂ → ℂ} {z w : ℂ} {r L : ℝ}
    (hr : 0 < r) (hw : w ∈ ball z r)
    (hq : ∀ u ∈ ball z r, q u ≠ 0 ∧ DifferentiableAt ℂ q u ∧ ‖deriv q u / q u‖ ≤ L)
    (hs : L * ‖w - z‖ ≤ 1) :
    ‖q w - q z‖ ≤ (2 * (L * ‖w - z‖)) * ‖q z‖ := by
  have hz := mem_ball_self hr (x := z)
  have hd : DifferentiableOn ℂ q (ball z r) := fun u hu => (hq u hu).2.1.differentiableWithinAt
  have hd' : DifferentiableOn ℂ (fun u => deriv q u / q u) (ball z r) :=
    (hd.deriv isOpen_ball).div hd (fun u hu => (hq u hu).1)
  obtain ⟨P, hP₀, hP⟩ := hd'.isExactOn_ball.with_val_at z (0 : ℂ)
  have hPbound : ‖P w‖ ≤ L * ‖w - z‖ := by
    have hp := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun u hu => (hP u hu).differentiableAt)
      (fun u hu => by rw [(hP u hu).deriv]; exact (hq u hu).2.2)
      (convex_ball z r) hz hw
    simpa only [hP₀, sub_zero] using hp
  let A : ℂ → ℂ := fun u => q u * exp (-P u)
  have hA (u : ℂ) (hu : u ∈ ball z r) : HasDerivAt A 0 u := by
    convert ((hq u hu).2.1.hasDerivAt).mul ((hP u hu).neg.cexp) using 1
    field_simp [(hq u hu).1]
    ring
  have hAeq : A w = q z := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun u hu => (hA u hu).differentiableAt)
      (C := 0) (fun u hu => by simp [(hA u hu).deriv]) (convex_ball z r) hz hw
    have ha : A w = A z := sub_eq_zero.mp (by simpa using h)
    simpa [A, hP₀] using ha
  have hqeq : q w = q z * exp (P w) := calc
    _ = A w * exp (P w) := by
      dsimp [A]
      rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    _ = _ := by rw [hAeq]
  calc
    ‖q w - q z‖ = ‖q z‖ * ‖exp (P w) - 1‖ := by rw [hqeq, ← mul_sub_one, norm_mul]
    _ ≤ ‖q z‖ * (2 * ‖P w‖) :=
      mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_le (hPbound.trans hs)) (norm_nonneg _)
    _ ≤ _ := by rw [mul_comm _ ‖q z‖]; gcongr

private theorem contour_phase (c : ℂ) (R : ℝ) :
    ∃ b : ℝ, |b + R| ≤ Real.pi ∧ c * exp ((b : ℂ) * I) = (‖c‖ : ℂ) := by
  let a := c * exp ((-R : ℝ) * I)
  let b := -R - arg a
  refine ⟨b, ?_, ?_⟩
  · dsimp [b]
    rw [show -R - arg a + R = -arg a by ring, abs_neg]
    exact Complex.abs_arg_le_pi _
  · dsimp only [b]
    rw [ofReal_sub, sub_mul, exp_sub, ← mul_div_assoc]
    change a / exp ((arg a : ℂ) * I) = _
    have ha : ‖a‖ = ‖c‖ := by
      dsimp only [a]
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    apply (div_eq_iff (Complex.exp_ne_zero _)).mpr
    rw [← ha]
    exact (Complex.norm_mul_exp_arg_mul_I a).symm

private theorem norm_contourPoint_sub_center (u v R : ℝ) :
    ‖contourPoint u v - (-(R : ℂ) * I)‖ ≤ |u| + |v + R| := by
  rw [contourPoint]
  have h : (u : ℂ) + (v : ℂ) * I - -(R : ℂ) * I = (u : ℂ) + ((v + R : ℝ) : ℂ) * I := by
    rw [ofReal_add]
    ring
  rw [h]
  simpa only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs] using
    norm_add_le (u : ℂ) (((v + R : ℝ) : ℂ) * I)

private theorem contour_scale_aux {c : ℂ} {R : ℝ} (hR : 8800 ≤ R)
    (hc : 0 < ‖c‖) (hclog : -(R / 4400) ≤ Real.log ‖c‖) :
    Real.exp (Real.exp (R / 2200)) ≤
      Real.pi / 2 * ‖c‖ * Real.exp (‖c‖ * Real.exp (R / 1100) / 2) := by
  let t := R / 4400
  have ht : 2 ≤ t := by dsimp [t]; linarith
  have hc' : Real.exp (-t) ≤ ‖c‖ := by
    rw [← Real.exp_log hc]
    exact Real.exp_le_exp.mpr hclog
  have hexp : Real.exp (3 * t) ≤ ‖c‖ * Real.exp (R / 1100) := by
    have he : 3 * t = -t + R / 1100 := by dsimp [t]; ring
    rw [he, Real.exp_add]
    exact mul_le_mul_of_nonneg_right hc' (Real.exp_nonneg _)
  have hmul : Real.exp (3 * t) = Real.exp t * Real.exp (2 * t) := by
    rw [show 3 * t = t + 2 * t by ring, Real.exp_add]
  have hsmall : Real.exp (2 * t) ≤ -t + ‖c‖ * Real.exp (R / 1100) / 2 := by
    have h₁ : 3 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have h₂ := Real.add_one_le_exp (2 * t)
    have h₃ := mul_le_mul_of_nonneg_right h₁ (Real.exp_nonneg (2 * t))
    rw [← hmul] at h₃
    linarith
  have ht' : R / 2200 = 2 * t := by dsimp [t]; ring
  calc
    _ ≤ Real.exp (-t + ‖c‖ * Real.exp (R / 1100) / 2) := by
      rw [ht']
      exact Real.exp_le_exp.mpr hsmall
    _ = Real.exp (-t) * Real.exp (‖c‖ * Real.exp (R / 1100) / 2) := Real.exp_add _ _
    _ ≤ ‖c‖ * Real.exp (‖c‖ * Real.exp (R / 1100) / 2) :=
      mul_le_mul_of_nonneg_right hc' (Real.exp_nonneg _)
    _ ≤ _ := by
      have hp : 1 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hc.le hp) (Real.exp_nonneg _)

/-- For all sufficiently large `R`, the inverse-chart equation has a large value at
one of two points in the disk. The points depend only on `q` and `R`. -/
theorem local_quantitative_growth :
    ∀ᶠ R : ℝ in atTop, ∀ q : ℂ → ℂ,
      let z : ℂ := -(R : ℂ) * I
      let D := ball z (R / 10)
      (∀ w ∈ D, q w ≠ 0 ∧ DifferentiableAt ℂ q w ∧ ‖deriv q w / q w‖ ≤ 10 / R) →
      R⁻¹ ^ 2 ≤ ‖q z‖ → ‖q z‖ ≤ R ^ 2 →
      ∃ w₀ ∈ D, ∃ w₁ ∈ D, ∀ Y : ℂ → ℂ,
        (∀ w ∈ D, HasDerivAt Y (q w * (exp w * Y w + 1)) w) →
        Real.exp (Real.exp (R / 2200)) ≤ max ‖Y w₀‖ ‖Y w₁‖ := by
  let A := Real.log 4 + 3 * Real.pi
  let η := min contourTolerance (1 / 1100)
  have hη : 0 < η := lt_min contourTolerance_pos (by norm_num)
  have hηT : η ≤ contourTolerance := min_le_left _ _
  have hη₀ : η ≤ 1 / 1100 := min_le_right _ _
  have hlog₄ : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA : 0 < A := by dsimp [A]; linarith [Real.pi_pos]
  have hlog := Real.isLittleO_log_id_atTop.def (show 0 < η / 80 by positivity)
  filter_upwards [hlog, eventually_ge_atTop (8800 : ℝ), eventually_ge_atTop (40 * A / η)]
    with R hl hR hRA
  intro q z D hq hlow hupp
  have hRpos : 0 < R := by linarith
  let c := q z
  have hc : 0 < ‖c‖ := lt_of_lt_of_le (by positivity : 0 < R⁻¹ ^ 2) hlow
  have hR1 : 1 ≤ R := by linarith
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  rw [Real.norm_eq_abs, abs_of_nonneg hlogR, id_eq, Real.norm_eq_abs, abs_of_pos hRpos] at hl
  have hA' : A ≤ η * R / 40 := by
    have h := (div_le_iff₀ hη).mp hRA
    linarith
  have hbound : A + 2 * Real.log R ≤ η * R / 20 := by linarith
  have hbound' : A + 2 * Real.log R ≤ R / 1100 := by
    have h := mul_le_mul_of_nonneg_right hη₀ hRpos.le
    linarith
  have hcloglo : -2 * Real.log R ≤ Real.log ‖c‖ := by
    have h := Real.log_le_log (show 0 < R⁻¹ ^ 2 by positivity) hlow
    rw [Real.log_pow, Real.log_inv] at h
    push_cast at h
    linarith
  have hcloghi : Real.log ‖c‖ ≤ 2 * Real.log R := by
    have h := Real.log_le_log hc hupp
    simpa [Real.log_pow] using h
  have hclog : -(R / 4400) ≤ Real.log ‖c‖ := by
    have h := mul_le_mul_of_nonneg_right hη₀ hRpos.le
    linarith
  obtain ⟨b, hbR, hphase⟩ := contour_phase c R
  let x := Real.log (4 / ‖c‖)
  let X := R / 1100
  have hxSize : ‖c‖ * Real.exp x = 4 := by
    dsimp [x]
    rw [Real.exp_log (by positivity)]
    field_simp [hc.ne']
  have hxAbs : |x| ≤ Real.log 4 + 2 * Real.log R := by
    rw [show x = Real.log 4 - Real.log ‖c‖ from Real.log_div (by norm_num) hc.ne']
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hxX : x ≤ X := by
    have h := (le_abs_self x).trans hxAbs
    dsimp [X, A] at *
    linarith [Real.pi_pos]
  have hbabs (v : ℝ) (hv : v ∈ Icc b (b + 2 * Real.pi)) : |v + R| ≤ 3 * Real.pi := by
    have h := abs_le.mp hbR
    exact abs_le.mpr ⟨by linarith [h.1, hv.1, Real.pi_pos], by linarith [h.2, hv.2]⟩
  have hdist (u : ℝ) (hu : u ∈ Icc x X) (v : ℝ) (hv : v ∈ Icc b (b + 2 * Real.pi)) :
      ‖contourPoint u v - z‖ ≤ 2 * X := by
    have huabs : |u| ≤ X := by
      refine abs_le.mpr ⟨?_, hu.2⟩
      have h := neg_le_abs x
      dsimp [X, A] at *
      linarith [hu.1, Real.pi_pos]
    have hi := norm_contourPoint_sub_center u v R
    change ‖contourPoint u v - z‖ ≤ |u| + |v + R| at hi
    dsimp [X, A] at *
    linarith [hbabs v hv]
  have hrect (u : ℝ) (hu : u ∈ Icc x X) (v : ℝ) (hv : v ∈ Icc b (b + 2 * Real.pi)) :
      contourPoint u v ∈ D := by
    change dist (contourPoint u v) z < R / 10
    rw [dist_eq_norm]
    have h := hdist u hu v hv
    dsimp [X] at h
    linarith
  have hb : b ∈ Icc b (b + 2 * Real.pi) := left_mem_Icc.mpr (by linarith [Real.pi_pos])
  have hb' : b + 2 * Real.pi ∈ Icc b (b + 2 * Real.pi) :=
    right_mem_Icc.mpr (by linarith [Real.pi_pos])
  have hX : X ∈ Icc x X := right_mem_Icc.mpr hxX
  have hx : x ∈ Icc x X := left_mem_Icc.mpr hxX
  refine ⟨contourPoint X b, hrect X hX b hb, contourPoint X (b + 2 * Real.pi), hrect X hX _ hb', ?_⟩
  intro Y hY
  have hqDiff (u : ℝ) (hu : u ∈ Icc x X) (v : ℝ) (hv : v ∈ Icc b (b + 2 * Real.pi)) :
      ‖q (contourPoint u v) - c‖ ≤ ‖c‖ / 10 := by
    have hC : (10 / R) * ‖contourPoint u v - z‖ ≤ 1 / 55 := calc
      _ ≤ (10 / R) * (2 * X) := mul_le_mul_of_nonneg_left (hdist u hu v hv) (by positivity)
      _ = _ := by dsimp [X]; field_simp; norm_num
    have hrel := logarithmic_derivative_distortion (by positivity : 0 < R / 10) (hrect u hu v hv) hq
      (hC.trans (by norm_num))
    exact hrel.trans (by nlinarith [mul_le_mul_of_nonneg_right hC hc.le])
  have hqVert (v : ℝ) (hv : v ∈ Icc b (b + 2 * Real.pi)) :
      ‖q (contourPoint x v) - c‖ ≤ contourTolerance * ‖c‖ := by
    have h := norm_contourPoint_sub_center x v R
    have hdV : ‖contourPoint x v - z‖ ≤ η * R / 20 := by
      change ‖contourPoint x v - z‖ ≤ |x| + |v + R| at h
      dsimp [A] at hbound
      linarith [hxAbs, hbabs v hv]
    have hC : 2 * ((10 / R) * ‖contourPoint x v - z‖) ≤ η := calc
      _ ≤ 2 * ((10 / R) * (η * R / 20)) := by gcongr
      _ = _ := by field_simp; norm_num
    have hsmall : (10 / R) * ‖contourPoint x v - z‖ ≤ 1 := by linarith
    have hrel :=
      logarithmic_derivative_distortion (by positivity : 0 < R / 10) (hrect x hx v hv) hq hsmall
    exact hrel.trans (mul_le_mul_of_nonneg_right (hC.trans hηT) hc.le)
  have hdiff : DifferentiableOn ℂ q D := fun w hw => (hq w hw).2.1.differentiableWithinAt
  exact (contour_scale_aux hR hc hclog).trans
    (rectangle_forcing hxX hxSize hphase hrect hdiff hqDiff hqVert hY)

end Bruck
