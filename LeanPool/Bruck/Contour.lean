/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # The rectangular contour estimate for `Y' = q (exp(w) Y + 1)` -/

@[expose] public section

namespace Bruck

open Complex Set Metric

/-- The point with real coordinate `u` and imaginary coordinate `v`. -/
def contourPoint (u v : ℝ) : ℂ := (u : ℂ) + (v : ℂ) * I

/-- The tighter relative error required on the vertical edge. -/
noncomputable def contourTolerance : ℝ := 1 / (1024 * Real.exp 5)

theorem contourTolerance_pos : 0 < contourTolerance := by
  unfold contourTolerance
  positivity

private theorem contourTolerance_le : contourTolerance ≤ 1 / 1024 := by
  have h : 1 ≤ Real.exp 5 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  unfold contourTolerance
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)

private theorem exp_contourPoint (u v : ℝ) :
    exp (contourPoint u v) = (Real.exp u : ℂ) * exp ((v : ℂ) * I) := by
  rw [contourPoint, exp_add, ofReal_exp]

private theorem exp_contourPoint_add_period (u v : ℝ) :
    exp (contourPoint u (v + 2 * Real.pi)) = exp (contourPoint u v) := by
  rw [exp_contourPoint, exp_contourPoint, ofReal_add, add_mul, exp_add, ofReal_mul,
    ofReal_ofNat, Complex.exp_two_pi_mul_I, mul_one]

private theorem norm_exp_contourPoint (u v : ℝ) : ‖exp (contourPoint u v)‖ = Real.exp u := by
  rw [Complex.norm_exp]
  simp [contourPoint, Complex.mul_re]

private theorem hasDerivAt_contour_vertical {f : ℂ → ℂ} {u v : ℝ} {d : ℂ}
    (hf : HasDerivAt f d (contourPoint u v)) :
    HasDerivAt (fun t : ℝ => f (contourPoint u t)) (d * I) v := by
  have hv : HasDerivAt (fun z : ℂ => (u : ℂ) + z * I) I (v : ℂ) := by
    simpa using ((hasDerivAt_id (v : ℂ)).mul_const I).const_add (u : ℂ)
  exact (hf.comp (v : ℂ) hv).comp_ofReal

private theorem hasDerivAt_contour_horizontal {f : ℂ → ℂ} {u v : ℝ} {d : ℂ}
    (hf : HasDerivAt f d (contourPoint u v)) :
    HasDerivAt (fun t : ℝ => f (contourPoint t v)) d u := by
  have hu := (hasDerivAt_id (u : ℂ)).add_const ((v : ℂ) * I)
  simpa [contourPoint] using (hf.comp (u : ℂ) hu).comp_ofReal

private theorem contour_vertical_sub_le {f f' : ℂ → ℂ} {x b B L : ℝ}
    (hf : ∀ v ∈ Icc b B, HasDerivAt f (f' (contourPoint x v)) (contourPoint x v))
    (hL : ∀ v ∈ Icc b B, ‖f' (contourPoint x v)‖ ≤ L) {v : ℝ} (hv : v ∈ Icc b B) :
    ‖f (contourPoint x v) - f (contourPoint x b)‖ ≤ L * (v - b) := by
  apply norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hasDerivAt_contour_vertical (hf t ht)).hasDerivWithinAt) _ v hv
  intro t ht
  simpa using hL t (Ico_subset_Icc_self ht)

private theorem periodic_model_primitive (c : ℂ) :
    ∃ F : ℂ → ℂ, (∀ w, HasDerivAt F (c * exp (-(c * exp w))) w) ∧
      (∀ x b, F (contourPoint x (b + 2 * Real.pi)) - F (contourPoint x b) =
        c * ((2 * Real.pi : ℝ) : ℂ) * I) := by
  let p : ℂ → ℂ := fun z => exp (-z)
  have hp : Differentiable ℂ p := by fun_prop
  have hslope : Differentiable ℂ (dslope p 0) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp)).mpr hp.differentiableOn
  obtain ⟨P, hP⟩ := hslope.isExactOn_univ
  let F : ℂ → ℂ := fun w => c * (w + P (c * exp w))
  refine ⟨F, ?_, ?_⟩
  · intro w
    have h := (hP (c * exp w) (mem_univ _)).comp w ((Complex.hasDerivAt_exp w).const_mul c)
    have hd := ((hasDerivAt_id w).add h).const_mul c
    have hs : (c * exp w) * dslope p 0 (c * exp w) = exp (-(c * exp w)) - 1 := by
      simpa [p, smul_eq_mul] using sub_smul_dslope p 0 (c * exp w)
    convert hd using 1
    · rfl
    · rw [mul_comm (dslope p 0 (c * exp w)), hs]
      ring
  · intro x b
    dsimp [F]
    rw [exp_contourPoint_add_period]
    push_cast
    unfold contourPoint
    push_cast
    ring

private theorem vertical_S_estimate {S q : ℂ → ℂ} {c : ℂ} {x b : ℝ}
    (hS : ∀ v ∈ Icc b (b + 2 * Real.pi),
      HasDerivAt S (q (contourPoint x v) * exp (contourPoint x v)) (contourPoint x v))
    (hS₀ : S (contourPoint x b) = 4)
    (hsize : ‖c‖ * Real.exp x = 4) (hphase : c * exp (contourPoint x b) = 4)
    (hq : ∀ v ∈ Icc b (b + 2 * Real.pi),
      ‖q (contourPoint x v) - c‖ ≤ contourTolerance * ‖c‖) :
    ∀ v ∈ Icc b (b + 2 * Real.pi),
      ‖S (contourPoint x v) - c * exp (contourPoint x v)‖ ≤ 8 * Real.pi * contourTolerance := by
  intro v hv
  have hD (u : ℝ) (hu : u ∈ Icc b (b + 2 * Real.pi)) :
      HasDerivAt (fun w => S w - c * exp w)
        ((q (contourPoint x u) - c) * exp (contourPoint x u)) (contourPoint x u) := by
    simpa only [sub_mul, ← Pi.sub_def] using (hS u hu).sub ((Complex.hasDerivAt_exp _).const_mul c)
  have hnorm (u : ℝ) (hu : u ∈ Icc b (b + 2 * Real.pi)) :
      ‖(q (contourPoint x u) - c) * exp (contourPoint x u)‖ ≤ 4 * contourTolerance := by
    rw [norm_mul, norm_exp_contourPoint]
    calc
      _ ≤ (contourTolerance * ‖c‖) * Real.exp x :=
        mul_le_mul_of_nonneg_right (hq u hu) (Real.exp_nonneg _)
      _ = 4 * contourTolerance := by rw [mul_assoc, hsize, mul_comm]
  have hh := contour_vertical_sub_le (f' := fun w => (q w - c) * exp w) hD hnorm hv
  rw [hS₀, hphase, sub_self, sub_zero] at hh
  calc
    _ ≤ 4 * contourTolerance * (v - b) := hh
    _ ≤ 4 * contourTolerance * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left (by linarith [hv.2]) (by positivity [contourTolerance_pos])
    _ = _ := by ring

private theorem vertical_S_error_le : 8 * Real.pi * contourTolerance ≤ 1 / 5 := by
  calc
    _ ≤ 32 * contourTolerance :=
      mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) contourTolerance_pos.le
    _ ≤ 32 * (1 / 1024) := by linarith [contourTolerance_le]
    _ ≤ _ := by norm_num

private theorem vertical_integrating_factor_estimate {S q G : ℂ → ℂ} {c : ℂ} {x b : ℝ}
    (hG : ∀ v ∈ Icc b (b + 2 * Real.pi), HasDerivAt G
      (exp (-S (contourPoint x v)) * q (contourPoint x v)) (contourPoint x v))
    (hsize : ‖c‖ * Real.exp x = 4)
    (hS : ∀ v ∈ Icc b (b + 2 * Real.pi),
      ‖S (contourPoint x v) - c * exp (contourPoint x v)‖ ≤ 8 * Real.pi * contourTolerance)
    (hq : ∀ v ∈ Icc b (b + 2 * Real.pi),
      ‖q (contourPoint x v) - c‖ ≤ contourTolerance * ‖c‖) :
    (3 * Real.pi / 2) * ‖c‖ ≤ ‖G (contourPoint x (b + 2 * Real.pi)) - G (contourPoint x b)‖ := by
  obtain ⟨F, hF, hperiod⟩ := periodic_model_primitive c
  have hD (v : ℝ) (hv : v ∈ Icc b (b + 2 * Real.pi)) :
      HasDerivAt (fun w => G w - F w)
        (exp (-S (contourPoint x v)) * q (contourPoint x v) -
          c * exp (-(c * exp (contourPoint x v)))) (contourPoint x v) :=
    (hG v hv).sub (hF _)
  have hnorm (v : ℝ) (hv : v ∈ Icc b (b + 2 * Real.pi)) :
      ‖exp (-S (contourPoint x v)) * q (contourPoint x v) -
        c * exp (-(c * exp (contourPoint x v)))‖ ≤ ‖c‖ / 4 := by
    let w := contourPoint x v
    let m := c * exp w
    change ‖exp (-S w) * q w - c * exp (-m)‖ ≤ _
    have hm : ‖m‖ = 4 := by rw [show m = c * exp w from rfl, norm_mul, norm_exp_contourPoint, hsize]
    have hSm : ‖S w - m‖ ≤ 8 * Real.pi * contourTolerance := hS v hv
    have hS' : ‖S w‖ ≤ 5 := calc
      ‖S w‖ ≤ ‖S w - m‖ + ‖m‖ := norm_le_norm_sub_add _ _
      _ ≤ 5 := by rw [hm]; linarith [hSm.trans vertical_S_error_le]
    have hexS : ‖exp (-S w)‖ ≤ Real.exp 5 :=
      (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by simpa using hS'))
    have hexm : ‖exp (-m)‖ ≤ Real.exp 5 :=
      (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by rw [norm_neg, hm]; norm_num))
    have hdiff : ‖exp (-S w) - exp (-m)‖ ≤
        Real.exp 5 * (64 * contourTolerance) := by
      have hneg : ‖-S w + m‖ = ‖S w - m‖ := by
        rw [show -S w + m = -(S w - m) by ring, norm_neg]
      have hsplit : exp (-S w) - exp (-m) = exp (-m) * (exp (-S w + m) - 1) := by
        rw [mul_sub, mul_one, ← exp_add]
        congr 2
        ring
      rw [hsplit, norm_mul]
      have hsmall : ‖-S w + m‖ ≤ 1 := by rw [hneg]; linarith [hSm.trans vertical_S_error_le]
      have hab := (Complex.norm_exp_sub_one_le hsmall).trans
        (mul_le_mul_of_nonneg_left (hneg.le.trans hSm) (by norm_num))
      have hab' : ‖exp (-S w + m) - 1‖ ≤ 64 * contourTolerance :=
        hab.trans (by
          nlinarith only [mul_nonneg (sub_nonneg.mpr Real.pi_lt_four.le)
            contourTolerance_pos.le])
      exact mul_le_mul hexm hab' (norm_nonneg _) (Real.exp_nonneg _)
    have hsplit : exp (-S w) * q w - c * exp (-m) =
        exp (-S w) * (q w - c) + c * (exp (-S w) - exp (-m)) := by ring
    have het : Real.exp 5 * contourTolerance = 1 / 1024 := by
      unfold contourTolerance
      field_simp [ne_of_gt (Real.exp_pos 5)]
    rw [hsplit]
    calc
      _ ≤ ‖exp (-S w) * (q w - c)‖ + ‖c * (exp (-S w) - exp (-m))‖ := norm_add_le _ _
      _ ≤ Real.exp 5 * (contourTolerance * ‖c‖) + ‖c‖ * (Real.exp 5 * (64 * contourTolerance)) := by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul hexS (hq v hv) (norm_nonneg _) (Real.exp_nonneg _))
          (mul_le_mul_of_nonneg_left hdiff (norm_nonneg _))
      _ = (65 / 1024) * ‖c‖ := by
        calc
          _ = 65 * (Real.exp 5 * contourTolerance) * ‖c‖ := by ring
          _ = _ := by rw [het]; ring
      _ ≤ _ := by linarith only [norm_nonneg c]
  let P₀ := contourPoint x b
  let P₁ := contourPoint x (b + 2 * Real.pi)
  have hP₁ : b + 2 * Real.pi ∈ Icc b (b + 2 * Real.pi) := by
    exact right_mem_Icc.mpr (by linarith [Real.pi_pos])
  have herr := contour_vertical_sub_le (f' := fun w => exp (-S w) * q w - c * exp (-(c * exp w)))
    hD hnorm hP₁
  have herr' : ‖(G P₁ - G P₀) - (F P₁ - F P₀)‖ ≤ Real.pi / 2 * ‖c‖ := by
    calc
      _ = ‖(G P₁ - F P₁) - (G P₀ - F P₀)‖ := by congr 1; ring
      _ ≤ ‖c‖ / 4 * (b + 2 * Real.pi - b) := herr
      _ = _ := by ring
  have hnormF : ‖F P₁ - F P₀‖ = (2 * Real.pi) * ‖c‖ := by
    rw [hperiod, norm_mul, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi), mul_comm]
  have htriangle := norm_le_norm_sub_add (F P₁ - F P₀) (G P₁ - G P₀)
  rw [norm_sub_rev (F P₁ - F P₀), hnormF] at htriangle
  linarith

private theorem horizontal_estimate {S q G : ℂ → ℂ} {c : ℂ} {x X v : ℝ}
    (hxX : x ≤ X) (hsize : ‖c‖ * Real.exp x = 4)
    (hphase : c * exp ((v : ℂ) * I) = (‖c‖ : ℂ))
    (hS₀ : 2 ≤ (S (contourPoint x v)).re)
    (hS : ∀ u ∈ Icc x X,
      HasDerivAt S (q (contourPoint u v) * exp (contourPoint u v)) (contourPoint u v))
    (hG : ∀ u ∈ Icc x X, HasDerivAt G
      (exp (-S (contourPoint u v)) * q (contourPoint u v)) (contourPoint u v))
    (hq : ∀ u ∈ Icc x X, ‖q (contourPoint u v) - c‖ ≤ ‖c‖ / 10) :
    ‖c‖ * Real.exp X / 2 ≤ (S (contourPoint X v)).re ∧
      ‖G (contourPoint X v) - G (contourPoint x v)‖ ≤ ‖c‖ * Real.exp (-2) := by
  let L : ℝ → ℝ := fun u => ‖c‖ * Real.exp u / 2
  have hL (u : ℝ) : HasDerivAt L (L u) u :=
    ((Real.hasDerivAt_exp u).const_mul ‖c‖).div_const 2
  have hLx : L x = 2 := by dsimp [L]; linarith
  have hLmin (u : ℝ) (hu : u ∈ Icc x X) : 2 ≤ L u := by
    rw [← hLx]
    dsimp [L]
    gcongr
    exact hu.1
  have hrealQ (u : ℝ) (hu : u ∈ Icc x X) :
      L u ≤ (q (contourPoint u v) * exp (contourPoint u v)).re := by
    let w := contourPoint u v
    have hphase' : c * exp w = ((‖c‖ * Real.exp u : ℝ) : ℂ) := calc
      _ = (Real.exp u : ℂ) * (c * exp ((v : ℂ) * I)) := by
        rw [exp_contourPoint]; ring
      _ = _ := by rw [hphase, ofReal_mul, mul_comm]
    have herror : ‖(q w - c) * exp w‖ ≤ (‖c‖ / 10) * Real.exp u := by
      rw [norm_mul, norm_exp_contourPoint]
      exact mul_le_mul_of_nonneg_right (hq u hu) (Real.exp_nonneg _)
    have hsplit : q w * exp w = c * exp w + (q w - c) * exp w := by ring
    change L u ≤ (q w * exp w).re
    rw [hsplit, Complex.add_re, hphase', Complex.ofReal_re]
    have hRe := (neg_le_abs ((q w - c) * exp w).re).trans (abs_re_le_norm _)
    dsimp [L]
    nlinarith only [hRe, herror, mul_nonneg (norm_nonneg c) (Real.exp_nonneg u)]
  let P : ℝ → ℝ := fun u => (S (contourPoint u v)).re - L u
  have hP (u : ℝ) (hu : u ∈ Icc x X) :
      HasDerivAt P ((q (contourPoint u v) * exp (contourPoint u v)).re - L u) u := by
    have hh := (hasDerivAt_id (u : ℂ)).add_const ((v : ℂ) * I)
    change HasDerivAt ((fun u : ℝ => (S (contourPoint u v)).re) - L)
      ((q (contourPoint u v) * exp (contourPoint u v)).re - L u) u
    simpa [contourPoint] using ((hS u hu).comp (u : ℂ) hh).real_of_complex.sub (hL u)
  have hmono : MonotoneOn P (Icc x X) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact fun u hu => (hP u hu).continuousAt.continuousWithinAt
    · exact fun u hu => (hP u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hP u (interior_subset hu)).deriv]
      exact sub_nonneg.mpr (hrealQ u (interior_subset hu))
  have hrealS (u : ℝ) (hu : u ∈ Icc x X) : L u ≤ (S (contourPoint u v)).re := by
    have h := hmono (left_mem_Icc.mpr hxX) hu hu.1
    change (S (contourPoint x v)).re - L x ≤ (S (contourPoint u v)).re - L u at h
    linarith
  refine ⟨hrealS _ (right_mem_Icc.mpr hxX), ?_⟩
  let f : ℝ → ℂ := fun u => G (contourPoint u v) - G (contourPoint x v)
  let B : ℝ → ℝ := fun u => ‖c‖ * (Real.exp (-2) - Real.exp (-L u))
  have hB (u : ℝ) : HasDerivAt B (‖c‖ * Real.exp (-L u) * L u) u := by
    convert ((hasDerivAt_const u (Real.exp (-2))).sub ((hL u).neg.exp)).const_mul ‖c‖ using 1
    simp only [Pi.neg_apply]
    ring
  have hf (u : ℝ) (hu : u ∈ Icc x X) : HasDerivAt f
      (exp (-S (contourPoint u v)) * q (contourPoint u v)) u :=
    (hasDerivAt_contour_horizontal (hG u hu)).sub_const _
  have hbound : ‖f X‖ ≤ B X := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun u hu => (hf u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hf u (Ico_subset_Icc_self hu)).hasDerivWithinAt) ?_ hB ?_
      (right_mem_Icc.mpr hxX)
    · simp [f, B, hLx]
    · intro u hu
      have hu' : u ∈ Icc x X := Ico_subset_Icc_self hu
      have hq' : ‖q (contourPoint u v)‖ ≤ 2 * ‖c‖ := by
        have h := norm_le_norm_sub_add (q (contourPoint u v)) c
        linarith [hq u hu', norm_nonneg c]
      rw [norm_mul, Complex.norm_exp, neg_re]
      calc
        _ ≤ Real.exp (-L u) * (2 * ‖c‖) :=
          mul_le_mul (Real.exp_le_exp.mpr (neg_le_neg (hrealS u hu'))) hq'
            (norm_nonneg _) (Real.exp_nonneg _)
        _ = (‖c‖ * Real.exp (-L u)) * 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hLmin u hu') (by positivity)
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (sub_le_self _ (Real.exp_nonneg _)) (norm_nonneg _))

private theorem derivative_integrating_factor {q S Y : ℂ → ℂ} {w : ℂ}
    (hS : HasDerivAt S (q w * exp w) w)
    (hY : HasDerivAt Y (q w * (exp w * Y w + 1)) w) :
    HasDerivAt (fun z => exp (-S z) * Y z) (exp (-S w) * q w) w := by
  convert ((hS.neg.cexp).mul hY) using 1
  simp only [Pi.neg_apply]
  ring

/-- A solution must have a large value at one of the two right corners of the rectangle. -/
theorem rectangle_forcing {z₀ c : ℂ} {r x X b : ℝ} {q : ℂ → ℂ}
    (hxX : x ≤ X) (hsize : ‖c‖ * Real.exp x = 4)
    (hphase : c * exp ((b : ℂ) * I) = (‖c‖ : ℂ))
    (hrect : ∀ u ∈ Icc x X, ∀ v ∈ Icc b (b + 2 * Real.pi),
      contourPoint u v ∈ ball z₀ r)
    (hdiff : DifferentiableOn ℂ q (ball z₀ r))
    (hq : ∀ u ∈ Icc x X, ∀ v ∈ Icc b (b + 2 * Real.pi),
      ‖q (contourPoint u v) - c‖ ≤ ‖c‖ / 10)
    (hqVert : ∀ v ∈ Icc b (b + 2 * Real.pi),
      ‖q (contourPoint x v) - c‖ ≤ contourTolerance * ‖c‖)
    {Y : ℂ → ℂ} (hY : ∀ w ∈ ball z₀ r, HasDerivAt Y (q w * (exp w * Y w + 1)) w) :
    (Real.pi / 2) * ‖c‖ * Real.exp (‖c‖ * Real.exp X / 2) ≤
      max ‖Y (contourPoint X b)‖ ‖Y (contourPoint X (b + 2 * Real.pi))‖ := by
  let b' := b + 2 * Real.pi
  have hbb' : b ≤ b' := by dsimp [b']; linarith [Real.pi_pos]
  have hb : b ∈ Icc b b' := left_mem_Icc.mpr hbb'
  have hb' : b' ∈ Icc b b' := right_mem_Icc.mpr hbb'
  have hx : x ∈ Icc x X := left_mem_Icc.mpr hxX
  obtain ⟨S, hS₀, hS⟩ :=
    ((hdiff.mul Complex.differentiable_exp.differentiableOn).isExactOn_ball).with_val_at
    (contourPoint x b) (4 : ℂ)
  let G : ℂ → ℂ := fun w => exp (-S w) * Y w
  have hG (w : ℂ) (hw : w ∈ ball z₀ r) : HasDerivAt G (exp (-S w) * q w) w :=
    derivative_integrating_factor (hS w hw) (hY w hw)
  have hphase₀ : c * exp (contourPoint x b) = 4 := calc
    _ = (Real.exp x : ℂ) * (c * exp ((b : ℂ) * I)) := by rw [exp_contourPoint]; ring
    _ = (4 : ℂ) := by rw [hphase, mul_comm, ← ofReal_mul, hsize]; norm_num
  have hphase' : c * exp ((b' : ℂ) * I) = (‖c‖ : ℂ) := by
    unfold b'
    rw [ofReal_add, add_mul, exp_add, ofReal_mul, ofReal_ofNat,
      Complex.exp_two_pi_mul_I, mul_one, hphase]
  have hvS := vertical_S_estimate (fun v hv => hS _ (hrect x hx v hv)) hS₀ hsize hphase₀ hqVert
  have hvG :=
    vertical_integrating_factor_estimate (fun v hv => hG _ (hrect x hx v hv)) hsize hvS hqVert
  have hS₁ : 2 ≤ (S (contourPoint x b')).re := by
    have h := (hvS b' hb').trans vertical_S_error_le
    have hper : exp (contourPoint x b') = exp (contourPoint x b) := exp_contourPoint_add_period x b
    rw [hper, hphase₀] at h
    have h' := (neg_le_abs (S (contourPoint x b') - 4).re).trans (abs_re_le_norm _)
    norm_num [Complex.sub_re] at h'
    linarith
  have hH₀ := horizontal_estimate hxX hsize hphase (by rw [hS₀]; norm_num)
    (fun u hu => hS _ (hrect u hu b hb)) (fun u hu => hG _ (hrect u hu b hb))
    (fun u hu => hq u hu b hb)
  have hH₁ := horizontal_estimate hxX hsize hphase' hS₁
    (fun u hu => hS _ (hrect u hu b' hb')) (fun u hu => hG _ (hrect u hu b' hb'))
    (fun u hu => hq u hu b' hb')
  let W₀ := contourPoint X b
  let W₁ := contourPoint X b'
  let P₀ := contourPoint x b
  let P₁ := contourPoint x b'
  have hdiff : ‖G P₁ - G P₀‖ ≤ ‖G W₀ - G P₀‖ + ‖G W₁ - G W₀‖ + ‖G W₁ - G P₁‖ := by
    calc
      _ = ‖(G W₀ - G P₀) + (G W₁ - G W₀) + -(G W₁ - G P₁)‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (by rw [norm_neg]; gcongr; exact norm_add_le _ _)
  have he : Real.exp (-2) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    rw [Real.exp_neg, show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr (by linarith)
  have hc : ‖c‖ * Real.exp (-2) ≤ (1 / 2) * ‖c‖ := by
    rw [mul_comm]
    gcongr
  have hGmin : Real.pi * ‖c‖ ≤ ‖G W₁ - G W₀‖ := by
    have hlarge : 0 ≤ (Real.pi / 2 - 1) * ‖c‖ :=
      mul_nonneg (by linarith [Real.pi_gt_three]) (norm_nonneg _)
    change _ ≤ ‖G P₁ - G P₀‖ at hvG
    have h₀ := hH₀.2.trans hc
    change ‖G W₀ - G P₀‖ ≤ _ at h₀
    have h₁ := hH₁.2.trans hc
    change ‖G W₁ - G P₁‖ ≤ _ at h₁
    linarith
  let L := ‖c‖ * Real.exp X / 2
  let M := max ‖Y W₀‖ ‖Y W₁‖
  have hGnorm (w : ℂ) (hw : L ≤ (S w).re) (hYw : ‖Y w‖ ≤ M) :
      ‖G w‖ ≤ Real.exp (-L) * M := by
    rw [show G w = exp (-S w) * Y w from rfl, norm_mul, Complex.norm_exp, neg_re]
    exact mul_le_mul (Real.exp_le_exp.mpr (neg_le_neg hw)) hYw (norm_nonneg _) (Real.exp_nonneg _)
  have hW₀ := hGnorm W₀ hH₀.1 (le_max_left _ _)
  have hW₁ := hGnorm W₁ hH₁.1 (le_max_right _ _)
  have hM : Real.pi * ‖c‖ ≤ 2 * (Real.exp (-L) * M) := by
    have h := hGmin.trans (norm_sub_le _ _)
    linarith
  have h := mul_le_mul_of_nonneg_right hM (Real.exp_nonneg L)
  have hCanc : Real.exp (-L) * Real.exp L = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hright : 2 * (Real.exp (-L) * M) * Real.exp L = 2 * M := by
    calc
      _ = 2 * M * (Real.exp (-L) * Real.exp L) := by ring
      _ = _ := by rw [hCanc, mul_one]
  rw [hright] at h
  change Real.pi / 2 * ‖c‖ * Real.exp L ≤ M
  nlinarith only [h]

end Bruck
