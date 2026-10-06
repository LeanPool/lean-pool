/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Profile
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Local energy estimate for a parabolic differential inequality

Smooth compactly supported spatial and time weights for the local energy estimate
`lem:caccioppoli`, with explicit derivative bounds.
-/

public section

open CKN CKN.Foundation.Parabolic Set Filter Polynomial
open scoped Topology
noncomputable section

namespace ESS

private theorem fderiv_coord_sub_const_apply_basisVec
    (i j : Fin 3) (c x : Vec3) :
    (fderiv ℝ (fun y : Vec3 => y i - c i) x) (basisVec j) =
      if j = i then 1 else 0 := by
  rw [fderiv_sub_const]
  change (fderiv ℝ (⇑(ContinuousLinearMap.proj (R := ℝ) i)) x) (basisVec j) = _
  rw [ContinuousLinearMap.fderiv]
  simp [basisVec_apply, eq_comm]

private theorem fderiv_coord_sub_const_sq_apply_basisVec
    (i j : Fin 3) (c x : Vec3) :
    (fderiv ℝ (fun y : Vec3 => (y i - c i) ^ 2) x) (basisVec j) =
      2 * (x i - c i) * (if j = i then 1 else 0) := by
  rw [fderiv_fun_pow]
  · simp [fderiv_coord_sub_const_apply_basisVec, pow_one, smul_eq_mul]
  · fun_prop

private theorem fderiv_euclideanSqDist_basis {x₀ x : Vec3} (j : Fin 3) :
    (fderiv ℝ (fun y : Vec3 => euclideanSqDist y x₀) x) (basisVec j) =
      2 * (x j - x₀ j) := by
  have hfun : (fun y : Vec3 => euclideanSqDist y x₀) =
      fun y => ∑ i : Fin 3, (y i - x₀ i)^2 := by
    funext y
    simp only [euclideanSqDist, vecNormSq_eq_sum_sq, Pi.sub_apply]
  rw [hfun, fderiv_fun_sum]
  · simp [fderiv_coord_sub_const_sq_apply_basisVec]
  · intro i hi
    fun_prop

private theorem expNegInvGlue_hasDerivAt (x : ℝ) :
    HasDerivAt expNegInvGlue
      (x⁻¹ ^ 2 * expNegInvGlue x) x := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) x
  simp only [Polynomial.derivative_one, sub_zero, mul_one,
    Polynomial.eval_one, one_mul, Polynomial.eval_pow,
    Polynomial.eval_X] at h
  exact h

private theorem mul_exp_neg_le (s : ℝ) :
    s * Real.exp (-s) ≤ Real.exp (-1) := by
  have hle : s ≤ Real.exp (s - 1) := by
    have h := Real.add_one_le_exp (s - 1)
    linarith only [h]
  calc
    s * Real.exp (-s) ≤ Real.exp (s - 1) * Real.exp (-s) :=
      mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
    _ = Real.exp (-1) := by
      rw [← Real.exp_add]
      ring_nf

private theorem expNegInvGlue_deriv_le (x : ℝ) :
    x⁻¹ ^ 2 * expNegInvGlue x ≤ 4 * Real.exp (-2) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [expNegInvGlue.zero_of_nonpos hx, mul_zero]
    positivity
  · have hgx : expNegInvGlue x = Real.exp (-x⁻¹) := by
      simp only [expNegInvGlue, ite_eq_right (not_le.mpr hx)]
    rw [hgx]
    let t := x⁻¹
    have ht0 : 0 < t := inv_pos.mpr hx
    let a := (t / 2) * Real.exp (-(t / 2))
    have ha0 : 0 ≤ a := by positivity
    have hale : a ≤ Real.exp (-1) := mul_exp_neg_le (t / 2)
    have hsq : a * a ≤ Real.exp (-1) * Real.exp (-1) :=
      mul_self_le_mul_self ha0 hale
    have e2 : Real.exp (-(t / 2)) * Real.exp (-(t / 2)) = Real.exp (-t) := by
      rw [← Real.exp_add]
      ring_nf
    have haa : a * a = (t ^ 2 * Real.exp (-t)) / 4 := by
      rw [show a = (t / 2) * Real.exp (-(t / 2)) from rfl,
        mul_mul_mul_comm, e2]
      ring
    have hee : Real.exp (-1) * Real.exp (-1) = Real.exp (-2) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hee, haa] at hsq
    linarith only [hsq]

private theorem smoothTransition_hasDerivAt (x : ℝ) :
    HasDerivAt Real.smoothTransition
      ((x⁻¹ ^ 2 * expNegInvGlue x * expNegInvGlue (1 - x) +
          expNegInvGlue x * ((1 - x)⁻¹ ^ 2 * expNegInvGlue (1 - x))) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) x := by
  have ha := expNegInvGlue_hasDerivAt x
  have hb := (expNegInvGlue_hasDerivAt (1 - x)).comp x
    ((hasDerivAt_id x).const_sub 1)
  have hD := ha.add hb
  have hDne : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  have hq := ha.div hD hDne
  simp only [Pi.add_apply, Function.comp_apply] at hq
  convert hq using 1 <;> first | rfl | ring

private theorem expNegInvGlue_ge_of_half_le {y : ℝ} (hy : 1 / 2 ≤ y) :
    Real.exp (-2) ≤ expNegInvGlue y := by
  have hy0 : 0 < y := by linarith only [hy]
  have hgy : expNegInvGlue y = Real.exp (-y⁻¹) := by
    simp only [expNegInvGlue, ite_eq_right (not_le.mpr hy0)]
  rw [hgy]
  apply Real.exp_le_exp.mpr
  have hmul : y⁻¹ * y = 1 := inv_mul_cancel₀ hy0.ne'
  have hinv : y⁻¹ ≤ 2 := by
    nlinarith only [
      mul_nonneg (inv_pos.mpr hy0).le
        (show (0 : ℝ) ≤ y - 1 / 2 by linarith only [hy]),
      hmul]
  linarith only [hinv]

private theorem smoothTransition_denom_ge (x : ℝ) :
    Real.exp (-2) ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  rcases le_total (1 / 2 : ℝ) x with hx | hx
  · have ha := expNegInvGlue_ge_of_half_le hx
    have hb := expNegInvGlue.nonneg (1 - x)
    linarith only [ha, hb]
  · have hx' : (1 / 2 : ℝ) ≤ 1 - x := by linarith only [hx]
    have hb := expNegInvGlue_ge_of_half_le hx'
    have ha := expNegInvGlue.nonneg x
    linarith only [hb, ha]

private theorem smoothTransition_abs_deriv_le_four (x : ℝ) :
    |deriv Real.smoothTransition x| ≤ 4 := by
  rw [(smoothTransition_hasDerivAt x).deriv]
  let a := expNegInvGlue x
  let b := expNegInvGlue (1 - x)
  let P := x⁻¹ ^ 2 * expNegInvGlue x
  let Q := (1 - x)⁻¹ ^ 2 * expNegInvGlue (1 - x)
  have ha0 : 0 ≤ a := expNegInvGlue.nonneg x
  have hb0 : 0 ≤ b := expNegInvGlue.nonneg (1 - x)
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hPle : P ≤ 4 * Real.exp (-2) := expNegInvGlue_deriv_le x
  have hQle : Q ≤ 4 * Real.exp (-2) := expNegInvGlue_deriv_le (1 - x)
  have hab : Real.exp (-2) ≤ a + b := by
    simpa [a, b] using smoothTransition_denom_ge x
  have habpos : 0 < a + b := lt_of_lt_of_le (Real.exp_pos _) hab
  have hden : 0 < (a + b) ^ 2 := by positivity
  have hnum0 : 0 ≤ (P * b + a * Q) / (a + b) ^ 2 := by positivity
  rw [abs_of_nonneg hnum0, div_le_iff₀ hden]
  have hstep1 : P * b + a * Q ≤ 4 * Real.exp (-2) * (a + b) := by
    calc
      P * b + a * Q ≤ (4 * Real.exp (-2)) * b + a * (4 * Real.exp (-2)) :=
        add_le_add (mul_le_mul_of_nonneg_right hPle hb0)
          (mul_le_mul_of_nonneg_left hQle ha0)
      _ = 4 * Real.exp (-2) * (a + b) := by ring
  have hstep2 : 4 * Real.exp (-2) * (a + b) ≤ 4 * (a + b) ^ 2 := by
    calc
      4 * Real.exp (-2) * (a + b) = Real.exp (-2) * (4 * (a + b)) := by ring
      _ ≤ (a + b) * (4 * (a + b)) :=
        mul_le_mul_of_nonneg_right hab (by positivity)
      _ = 4 * (a + b) ^ 2 := by ring
  calc
    P * b + a * Q ≤ 4 * Real.exp (-2) * (a + b) := hstep1
    _ ≤ 4 * (a + b) ^ 2 := hstep2

/-- A compactly supported spatial weight for `lem:caccioppoli`. -/
@[expose] def caccioppoliSpatialWeight (x₀ : Vec3) (r : ℝ) (y : Vec3) : ℝ :=
  CKN.smoothTransitionProfile ((199 / 100 * r - vec3EuclideanNorm (y - x₀)) /
    (99 / 100 * r))

private theorem caccioppoliSpatialWeight_eq_one {x₀ y : Vec3} {r : ℝ} (hr : 0 < r)
    (hy : vec3EuclideanNorm (y - x₀) < r) : caccioppoliSpatialWeight x₀ r y = 1 := by
  apply CKN.smoothTransitionProfile.one_of_one_le
  have hgap : 0 < (99 / 100 : ℝ) * r := by positivity
  rw [le_div_iff₀ hgap]
  norm_num
  linarith only [hy]

private theorem caccioppoliSpatialWeight_smooth (x₀ : Vec3) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (caccioppoliSpatialWeight x₀ r) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let d : Vec3 → ℝ := fun y => vec3EuclideanNorm (y - x₀)
  have hdsq : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => euclideanSqDist y x₀) :=
    contDiff_euclideanSqDist_left x₀
  have hdcont : Continuous d := by
    have hsqrt : Continuous (fun y : Vec3 => Real.sqrt (euclideanSqDist y x₀)) :=
      Real.continuous_sqrt.comp hdsq.continuous
    have heq : d = fun y => Real.sqrt (euclideanSqDist y x₀) := by
      funext y
      simp [d, vec3EuclideanNorm, euclideanSqDist, vecNormSq_eq_sum_sq]
    rw [heq]
    exact hsqrt
  by_cases hx : d x < r
  · have hset : {y : Vec3 | d y < r} ∈ 𝓝 x :=
      (isOpen_lt hdcont continuous_const).mem_nhds hx
    have heq : (caccioppoliSpatialWeight x₀ r) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [hset] with y hy
      exact caccioppoliSpatialWeight_eq_one hr hy
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hx' : r ≤ d x := le_of_not_gt hx
    have hsqpos : 0 < euclideanSqDist x x₀ := by
      have hdpos : 0 < d x := lt_of_lt_of_le hr hx'
      have hddef : d x = Real.sqrt (euclideanSqDist x x₀) := by
        simp [d, vec3EuclideanNorm, euclideanSqDist, vecNormSq_eq_sum_sq]
      rw [hddef] at hdpos
      exact Real.sqrt_pos.1 hdpos
    have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) d x := by
      have hsqrt := Real.contDiffAt_sqrt (n := (⊤ : ℕ∞)) (ne_of_gt hsqpos)
      have hcomp := hsqrt.comp x hdsq.contDiffAt
      have heq : d = fun y => Real.sqrt (euclideanSqDist y x₀) := by
        funext y
        simp [d, vec3EuclideanNorm, euclideanSqDist, vecNormSq_eq_sum_sq]
      rw [heq]
      exact hcomp
    have harg : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y => (199 / 100 * r - d y) / (99 / 100 * r)) x := by
      exact (contDiffAt_const.sub hnorm).div_const _
    have hcomp := CKN.smoothTransitionProfile.smooth.contDiffAt.comp x harg
    change ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : Vec3 => CKN.smoothTransitionProfile
        ((199 / 100 * r - vec3EuclideanNorm (y - x₀)) / (99 / 100 * r))) x
    exact hcomp

private theorem caccioppoliSpatialWeight_coord_deriv {x₀ y : Vec3} {r : ℝ} (hr : 0 < r)
    (hy : r ≤ vec3EuclideanNorm (y - x₀)) (i : Fin 3) :
    (classicalGradient (caccioppoliSpatialWeight x₀ r) y) i =
      -(deriv CKN.smoothTransitionProfile
          ((199 / 100 * r - vec3EuclideanNorm (y - x₀)) / (99 / 100 * r))) /
        ((99 / 100 * r) * vec3EuclideanNorm (y - x₀)) * (y i - x₀ i) := by
  let q : Vec3 → ℝ := fun z => euclideanSqDist z x₀
  let d : Vec3 → ℝ := fun z => vec3EuclideanNorm (z - x₀)
  let a : ℝ := (99 / 100 : ℝ) * r
  have ha : a ≠ 0 := ne_of_gt (by dsimp [a]; positivity)
  have hsqpos : 0 < q y := by
    have hdpos : 0 < d y := lt_of_lt_of_le hr hy
    have hddef : d y = Real.sqrt (q y) := by
      simp [d, q, vec3EuclideanNorm, euclideanSqDist, vecNormSq_eq_sum_sq]
    rw [hddef] at hdpos
    exact Real.sqrt_pos.1 hdpos
  have hqD : HasFDerivAt q (fderiv ℝ q y) y :=
    (contDiff_euclideanSqDist_left x₀).differentiable (by simp) y |>.hasFDerivAt
  have hdD : HasFDerivAt d ((1 / (2 * Real.sqrt (q y))) • fderiv ℝ q y) y := by
    have hs := hqD.sqrt (ne_of_gt hsqpos)
    have heq : (fun z => Real.sqrt (q z)) = d := by
      funext z
      simp [d, q, vec3EuclideanNorm, euclideanSqDist, vecNormSq_eq_sum_sq]
    rw [heq] at hs
    exact hs
  have hdistCoord (j : Fin 3) : (fderiv ℝ d y) (basisVec j) =
      (y j - x₀ j) / d y := by
    rw [hdD.fderiv]
    change (1 / (2 * Real.sqrt (q y))) *
      (fderiv ℝ (fun z : Vec3 => euclideanSqDist z x₀) y) (basisVec j) = _
    rw [fderiv_euclideanSqDist_basis]
    dsimp [d, q]
    have hdsqrt : vec3EuclideanNorm (y - x₀) = Real.sqrt (euclideanSqDist y x₀) := by
      simp only [vec3EuclideanNorm, euclideanSqDist, vecNormSq_eq_sum_sq]
    rw [← hdsqrt]
    field_simp [ne_of_gt (lt_of_lt_of_le hr hy)]
  have hargD : HasFDerivAt
      (fun z : Vec3 => (199 / 100 * r - d z) / a)
      ((a⁻¹) • (-fderiv ℝ d y)) y := by
    have hsub := hdD.const_sub (199 / 100 * r)
    rw [← hdD.fderiv] at hsub
    have hscale := hsub.const_smul a⁻¹
    change HasFDerivAt (fun z : Vec3 => a⁻¹ • (199 / 100 * r - d z)) _ y at hscale
    have hfun : (fun z : Vec3 => a⁻¹ • (199 / 100 * r - d z)) =
        (fun z => (199 / 100 * r - d z) / a) := by
      funext z
      simp [div_eq_mul_inv, smul_eq_mul, mul_comm]
    rw [hfun] at hscale
    exact hscale
  have hprofD := (CKN.smoothTransitionProfile.smooth.differentiable
      (by simp) ((199 / 100 * r - d y) / a)).hasDerivAt
  have hprofF := hprofD.hasFDerivAt
  have hetaD := hprofF.comp y hargD
  have hetaCoord : (fderiv ℝ (caccioppoliSpatialWeight x₀ r) y) (basisVec i) =
      -(deriv CKN.smoothTransitionProfile
          ((199 / 100 * r - d y) / a)) / (a * d y) * (y i - x₀ i) := by
    change (fderiv ℝ (CKN.smoothTransitionProfile ∘ fun z : Vec3 =>
      (199 / 100 * r - d z) / a) y) (basisVec i) = _
    rw [hetaD.fderiv]
    change (ContinuousLinearMap.toSpanSingleton ℝ
      (deriv CKN.smoothTransitionProfile ((199 / 100 * r - d y) / a)))
      ((a⁻¹ • -fderiv ℝ d y) (basisVec i)) = _
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      smul_apply, neg_apply]
    rw [hdistCoord i]
    field_simp [ha, ne_of_gt (lt_of_lt_of_le hr hy)]
  simpa [classicalGradient_apply, caccioppoliSpatialWeight, d, a, div_eq_mul_inv] using hetaCoord

private theorem caccioppoliSpatialWeight_gradient_bound (x₀ : Vec3) {r : ℝ} (hr : 0 < r)
    (y : Vec3) :
    vec3EuclideanNorm (classicalGradient (caccioppoliSpatialWeight x₀ r) y) ≤
      (400 / 99) / r := by
  let d : ℝ := vec3EuclideanNorm (y - x₀)
  by_cases hy : d < r
  · have hloc : (caccioppoliSpatialWeight x₀ r) =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
      have hcont : Continuous (fun z : Vec3 => vec3EuclideanNorm (z - x₀)) := by
        have hc := (contDiff_euclideanSqDist_left x₀).continuous
        have hsqrt : Continuous (fun z : Vec3 => Real.sqrt (euclideanSqDist z x₀)) :=
          Real.continuous_sqrt.comp hc
        have heq : (fun z : Vec3 => vec3EuclideanNorm (z - x₀)) =
            fun z => Real.sqrt (euclideanSqDist z x₀) := by
          funext z
          simp only [vec3EuclideanNorm, euclideanSqDist, vecNormSq_eq_sum_sq]
        rw [heq]
        exact hsqrt
      have hset : {z : Vec3 | vec3EuclideanNorm (z - x₀) < r} ∈ 𝓝 y :=
        (isOpen_lt hcont continuous_const).mem_nhds hy
      filter_upwards [hset] with z hz
      exact caccioppoliSpatialWeight_eq_one hr hz
    have hfd : fderiv ℝ (caccioppoliSpatialWeight x₀ r) y = 0 := by
      have hc : HasFDerivAt (fun _ : Vec3 => (1 : ℝ)) 0 y :=
        hasFDerivAt_const (𝕜 := ℝ) (E := Vec3) (F := ℝ) (1 : ℝ) y
      exact (hc.congr_of_eventuallyEq hloc).fderiv
    have hg : classicalGradient (caccioppoliSpatialWeight x₀ r) y = 0 := by
      funext j
      rw [classicalGradient_apply, hfd]
      simp
    rw [hg]
    simp only [vec3EuclideanNorm, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, Real.sqrt_zero, ge_iff_le]
    positivity
  · have hy' : r ≤ d := le_of_not_gt hy
    have hformula := caccioppoliSpatialWeight_coord_deriv hr hy'
    have hgradEq : classicalGradient (caccioppoliSpatialWeight x₀ r) y =
        (-(deriv CKN.smoothTransitionProfile
          ((199 / 100 * r - d) / ((99 / 100) * r))) /
          (((99 / 100) * r) * d)) • (y - x₀) := by
      funext i
      rw [classicalGradient_apply]
      have hi := hformula i
      simpa [d, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hi
    rw [hgradEq, vec3EuclideanNorm_smul]
    have hdpos : 0 < d := lt_of_lt_of_le hr hy'
    have hderiv : |deriv CKN.smoothTransitionProfile
        ((199 / 100 * r - d) / ((99 / 100) * r))| ≤ 4 := by
      simpa only [CKN.smoothTransitionProfile] using
        smoothTransition_abs_deriv_le_four
          ((199 / 100 * r - d) / ((99 / 100) * r))
    have hgap : 0 < (99 / 100 : ℝ) * r := by positivity
    have hbound : |deriv CKN.smoothTransitionProfile
        ((199 / 100 * r - d) / ((99 / 100) * r)) /
          (((99 / 100) * r) * d)| ≤ 4 / ((99 / 100) * r * d) := by
      rw [abs_div, abs_of_pos (mul_pos hgap hdpos)]
      exact div_le_div_of_nonneg_right hderiv (le_of_lt (mul_pos hgap hdpos))
    have hdnorm : vec3EuclideanNorm (y - x₀) = d := rfl
    rw [hdnorm]
    calc
      |-deriv CKN.smoothTransitionProfile
          ((199 / 100 * r - d) / ((99 / 100) * r)) /
          (((99 / 100) * r) * d)| * d ≤
          (4 / ((99 / 100) * r * d)) * d :=
        mul_le_mul_of_nonneg_right (by
          rw [abs_div, abs_neg, abs_of_pos (mul_pos hgap hdpos)]
          exact div_le_div_of_nonneg_right hderiv (le_of_lt (mul_pos hgap hdpos)))
          (le_of_lt hdpos)
      _ = (400 / 99) / r := by
        field_simp [ne_of_gt hr, ne_of_gt hdpos]
        ring

private theorem caccioppoliSpatialWeight_nonneg (x₀ : Vec3) (r : ℝ) (y : Vec3) :
    0 ≤ caccioppoliSpatialWeight x₀ r y :=
  CKN.smoothTransitionProfile.nonneg _

private theorem caccioppoliSpatialWeight_le_one (x₀ : Vec3) (r : ℝ) (y : Vec3) :
    caccioppoliSpatialWeight x₀ r y ≤ 1 :=
  CKN.smoothTransitionProfile.le_one _

private theorem vec3Norm_eq_vecEuclideanNorm (v : Vec3) :
    vec3EuclideanNorm v = CKN.vecEuclideanNorm v := by
  simp [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot, pow_two]

private theorem caccioppoliSpatialWeight_support_subset_closed (x₀ : Vec3) {r : ℝ}
    (hr : 0 < r) :
    Function.support (caccioppoliSpatialWeight x₀ r) ⊆
      CKN.euclideanClosedBall x₀ ((199 / 100) * r) := by
  let R : ℝ := (199 / 100) * r
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hclosed : Function.support (caccioppoliSpatialWeight x₀ r) ⊆
      CKN.euclideanClosedBall x₀ R := by
    intro y hy
    by_contra hnot
    have hdyC : R < CKN.vecEuclideanNorm (y - x₀) := by
      by_contra h
      have hle : CKN.vecEuclideanNorm (y - x₀) ≤ R := le_of_not_gt h
      exact hnot ((CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR).2 hle)
    have hdy : R < vec3EuclideanNorm (y - x₀) := by
      simpa [vec3Norm_eq_vecEuclideanNorm] using hdyC
    have hzero : caccioppoliSpatialWeight x₀ r y = 0 := by
      unfold caccioppoliSpatialWeight
      apply CKN.smoothTransitionProfile.zero_of_nonpos
      apply div_nonpos_of_nonpos_of_nonneg
      · change (199 / 100 : ℝ) * r - vec3EuclideanNorm (y - x₀) ≤ 0
        dsimp [R] at hdy
        linarith only [hdy]
      · positivity
    exact (Function.mem_support.mp hy) hzero
  simpa [R] using hclosed

private theorem caccioppoliSpatialWeight_tsupport_subset_outer (x₀ : Vec3) {r : ℝ}
    (hr : 0 < r) :
    tsupport (caccioppoliSpatialWeight x₀ r) ⊆ vec3Ball x₀ (2 * r) := by
  let R : ℝ := (199 / 100) * r
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hRf : R < 2 * r := by dsimp [R]; nlinarith only [hr]
  have hclosed : IsClosed (CKN.euclideanClosedBall x₀ R) :=
    CKN.isClosed_euclideanClosedBall x₀ R
  have hts : tsupport (caccioppoliSpatialWeight x₀ r) ⊆
      CKN.euclideanClosedBall x₀ R := by
    change closure (Function.support (caccioppoliSpatialWeight x₀ r)) ⊆ _
    exact closure_minimal (caccioppoliSpatialWeight_support_subset_closed x₀ hr) hclosed
  intro y hy
  change vec3EuclideanNorm (y - x₀) < 2 * r
  have hnormC : CKN.vecEuclideanNorm (y - x₀) ≤ R :=
    (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR).1 (hts hy)
  have hnorm3 : vec3EuclideanNorm (y - x₀) ≤ R := by
    simpa [vec3Norm_eq_vecEuclideanNorm] using hnormC
  exact hnorm3.trans_lt hRf

private theorem caccioppoliSpatialWeight_hasCompactSupport (x₀ : Vec3) {r : ℝ}
    (hr : 0 < r) : HasCompactSupport (caccioppoliSpatialWeight x₀ r) := by
  let R : ℝ := (199 / 100) * r
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply HasCompactSupport.intro
    (CKN.isCompact_euclideanClosedBall x₀ hR)
  intro y hy
  by_contra hne
  exact hy (caccioppoliSpatialWeight_support_subset_closed x₀ hr (Function.mem_support.mpr hne))

/-- The lower time cutoff in the compactly supported Caccioppoli weight. -/
@[expose] def lowerTimeCutoff (t ε s : ℝ) : ℝ :=
  CKN.smoothTransitionProfile ((s - (t + ε)) / ε)

/-- The upper time cutoff in the compactly supported Caccioppoli weight. -/
@[expose] def upperTimeCutoff (t r s : ℝ) : ℝ :=
  CKN.smoothTransitionProfile ((t + 3 * r ^ 2 - s) / ((199 / 100) * r ^ 2))

/-- A compactly supported time weight for `lem:caccioppoli`. -/
@[expose] def caccioppoliTimeWeight (t r ε s : ℝ) : ℝ :=
  lowerTimeCutoff t ε s * upperTimeCutoff t r s

private theorem caccioppoliTimeWeight_smooth (t r ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (caccioppoliTimeWeight t r ε) := by
  have hargLow : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => (s - (t + ε)) / ε) := by fun_prop
  have hargHigh : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => (t + 3 * r ^ 2 - s) / ((199 / 100) * r ^ 2)) := by fun_prop
  have hlow : ContDiff ℝ (⊤ : ℕ∞) (lowerTimeCutoff t ε) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (CKN.smoothTransitionProfile ∘ fun s : ℝ => (s - (t + ε)) / ε)
    exact CKN.smoothTransitionProfile.smooth.comp hargLow
  have hhigh : ContDiff ℝ (⊤ : ℕ∞) (upperTimeCutoff t r) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (CKN.smoothTransitionProfile ∘ fun s : ℝ =>
        (t + 3 * r ^ 2 - s) / ((199 / 100) * r ^ 2))
    exact CKN.smoothTransitionProfile.smooth.comp hargHigh
  exact hlow.mul hhigh

private theorem lowerTimeCutoff_eq_zero {t ε s : ℝ} (hε : 0 < ε)
    (hs : s ≤ t + ε) : lowerTimeCutoff t ε s = 0 := by
  unfold lowerTimeCutoff
  apply CKN.smoothTransitionProfile.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith only [hs]
  · exact hε.le

private theorem upperTimeCutoff_eq_zero {t r s : ℝ} (hr : 0 < r)
    (hs : t + 3 * r ^ 2 ≤ s) : upperTimeCutoff t r s = 0 := by
  unfold upperTimeCutoff
  apply CKN.smoothTransitionProfile.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith only [hs]
  · positivity

private theorem lowerTimeCutoff_eq_one {t ε s : ℝ} (hε : 0 < ε)
    (hs : t + 2 * ε ≤ s) : lowerTimeCutoff t ε s = 1 := by
  unfold lowerTimeCutoff
  apply CKN.smoothTransitionProfile.one_of_one_le
  rw [le_div_iff₀ hε]
  linarith only [hs]

private theorem upperTimeCutoff_eq_one {t r s : ℝ} (hr : 0 < r)
    (hs : s ≤ t + (101 / 100) * r ^ 2) : upperTimeCutoff t r s = 1 := by
  unfold upperTimeCutoff
  apply CKN.smoothTransitionProfile.one_of_one_le
  have hden : 0 < (199 / 100 : ℝ) * r ^ 2 := by positivity
  rw [one_le_div hden]
  nlinarith only [hs]

private theorem caccioppoliTimeWeight_nonneg_le_one
    (t r ε s : ℝ) : 0 ≤ caccioppoliTimeWeight t r ε s ∧
      caccioppoliTimeWeight t r ε s ≤ 1 := by
  constructor
  · exact mul_nonneg (CKN.smoothTransitionProfile.nonneg _)
      (CKN.smoothTransitionProfile.nonneg _)
  · calc
      lowerTimeCutoff t ε s * upperTimeCutoff t r s ≤
          1 * upperTimeCutoff t r s :=
        mul_le_mul_of_nonneg_right (CKN.smoothTransitionProfile.le_one _)
          (CKN.smoothTransitionProfile.nonneg _)
      _ ≤ 1 * 1 :=
        mul_le_mul_of_nonneg_left (CKN.smoothTransitionProfile.le_one _) (by norm_num)
      _ = 1 := by norm_num

private theorem caccioppoliTimeWeight_support_subset (t r ε : ℝ)
    (hε : 0 < ε) (hr : 0 < r) :
    Function.support (caccioppoliTimeWeight t r ε) ⊆
      Icc (t + ε) (t + 3 * r ^ 2) := by
  intro s hs
  change caccioppoliTimeWeight t r ε s ≠ 0 at hs
  have hl : lowerTimeCutoff t ε s ≠ 0 := by
    intro h
    exact hs (by simp [caccioppoliTimeWeight, h])
  have hu : upperTimeCutoff t r s ≠ 0 := by
    intro h
    exact hs (by simp [caccioppoliTimeWeight, h])
  have hargLow : 0 < (s - (t + ε)) / ε := by
    by_contra h
    exact hl (lowerTimeCutoff_eq_zero hε (by
      have hq : (s - (t + ε)) / ε ≤ 0 := le_of_not_gt h
      have hnum : s - (t + ε) ≤ 0 := by simpa using (div_le_iff₀ hε).1 hq
      linarith only [hnum]))
  have hargHigh : 0 <
      (t + 3 * r ^ 2 - s) / ((199 / 100) * r ^ 2) := by
    by_contra h
    exact hu (upperTimeCutoff_eq_zero hr (by
      have hd : 0 < (199 / 100 : ℝ) * r ^ 2 := by positivity
      have hq : (t + 3 * r ^ 2 - s) / ((199 / 100) * r ^ 2) ≤ 0 := le_of_not_gt h
      have hnum : t + 3 * r ^ 2 - s ≤ 0 := by simpa using (div_le_iff₀ hd).1 hq
      linarith only [hnum]))
  constructor
  · have hnum := (div_pos_iff_of_pos_right hε).1 hargLow
    linarith only [hnum]
  · have hd : 0 < (199 / 100 : ℝ) * r ^ 2 := by positivity
    have hnum := (div_pos_iff_of_pos_right hd).1 hargHigh
    linarith only [hnum]

private theorem caccioppoliTimeWeight_tsupport_subset (t r ε : ℝ)
    (hε : 0 < ε) (hr : 0 < r) :
    tsupport (caccioppoliTimeWeight t r ε) ⊆
      Icc (t + ε) (t + 3 * r ^ 2) := by
  change closure (Function.support (caccioppoliTimeWeight t r ε)) ⊆ _
  exact closure_minimal (caccioppoliTimeWeight_support_subset t r ε hε hr)
    isClosed_Icc

private theorem caccioppoliTimeWeight_hasCompactSupport (t r ε : ℝ)
    (hε : 0 < ε) (hr : 0 < r) :
    HasCompactSupport (caccioppoliTimeWeight t r ε) := by
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (caccioppoliTimeWeight_support_subset t r ε hε hr)

private theorem caccioppoliTimeWeight_eq_one {t r ε s : ℝ}
    (hε : 0 < ε) (hr : 0 < r)
    (hs₁ : t + 2 * ε ≤ s) (hs₂ : s ≤ t + r ^ 2) :
    caccioppoliTimeWeight t r ε s = 1 := by
  rw [caccioppoliTimeWeight, lowerTimeCutoff_eq_one hε hs₁]
  have hsupper : s ≤ t + (101 / 100) * r ^ 2 := by
    have hrSq : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith only [hs₂, hrSq]
  rw [upperTimeCutoff_eq_one hr hsupper, mul_one]

private theorem lowerTimeCutoff_hasDerivAt {t ε s : ℝ} (hε : 0 < ε) :
    HasDerivAt (lowerTimeCutoff t ε)
      (deriv CKN.smoothTransitionProfile ((s - (t + ε)) / ε) / ε) s := by
  have hp := (CKN.smoothTransitionProfile.smooth.differentiable
    (by simp) ((s - (t + ε)) / ε)).hasDerivAt
  have ha : HasDerivAt (fun q : ℝ => (q - (t + ε)) / ε) (1 / ε) s := by
    have h := (hasDerivAt_id s).sub_const (t + ε)
    convert h.div_const ε using 1
    · funext q
      simp [div_eq_mul_inv]
  have hc := hp.comp s ha
  convert hc using 1
  · funext q
    simp [lowerTimeCutoff, div_eq_mul_inv]
  · field_simp [hε.ne']

private theorem upperTimeCutoff_hasDerivAt {t r s : ℝ} (hr : 0 < r) :
    HasDerivAt (upperTimeCutoff t r)
      (-(deriv CKN.smoothTransitionProfile
          ((t + 3 * r ^ 2 - s) / ((199 / 100) * r ^ 2))) /
        ((199 / 100) * r ^ 2)) s := by
  have hp := (CKN.smoothTransitionProfile.smooth.differentiable
    (by simp) ((t + 3 * r ^ 2 - s) / ((199 / 100) * r ^ 2))).hasDerivAt
  have ha : HasDerivAt
      (fun q : ℝ => (t + 3 * r ^ 2 - q) / ((199 / 100) * r ^ 2))
      (-1 / ((199 / 100) * r ^ 2)) s := by
    have h := (hasDerivAt_const s (t + 3 * r ^ 2)).sub (hasDerivAt_id s)
    convert h.div_const ((199 / 100) * r ^ 2) using 1
    · funext q
      simp [div_eq_mul_inv]
    · norm_num
  have hc := hp.comp s ha
  convert hc using 1
  · funext q
    simp [upperTimeCutoff, div_eq_mul_inv]
  · field_simp [ne_of_gt hr]

private theorem smoothTransitionProfile_deriv_zero_of_one_lt {q : ℝ} (hq : 1 < q) :
    deriv CKN.smoothTransitionProfile q = 0 := by
  have hev : CKN.smoothTransitionProfile =ᶠ[𝓝 q] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hq] with y hy
    exact CKN.smoothTransitionProfile.one_of_one_le hy.le
  have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 q := hasDerivAt_const q (1 : ℝ)
  exact (hc.congr_of_eventuallyEq hev).deriv

private theorem smoothTransitionProfile_deriv_nonneg (q : ℝ) :
    0 ≤ deriv CKN.smoothTransitionProfile q :=
  Real.smoothTransition.monotone.deriv_nonneg

private theorem smoothTransitionProfile_deriv_abs_le_eight (q : ℝ) :
    |deriv CKN.smoothTransitionProfile q| ≤ 8 :=
  CKN.smoothTransitionProfile.abs_deriv_le_eight q

private theorem caccioppoliTimeWeight_hasDerivAt {t r ε s : ℝ}
    (hε : 0 < ε) (hr : 0 < r) :
    HasDerivAt (caccioppoliTimeWeight t r ε)
      (deriv (lowerTimeCutoff t ε) s * upperTimeCutoff t r s +
        lowerTimeCutoff t ε s * deriv (upperTimeCutoff t r) s) s := by
  have hl := lowerTimeCutoff_hasDerivAt (t := t) (ε := ε) (s := s) hε
  have hu := upperTimeCutoff_hasDerivAt (t := t) (r := r) (s := s) hr
  have hp := hl.mul hu
  have hcoef : deriv (lowerTimeCutoff t ε) s * upperTimeCutoff t r s +
      lowerTimeCutoff t ε s * deriv (upperTimeCutoff t r) s =
      deriv CKN.smoothTransitionProfile ((s - (t + ε)) / ε) / ε *
        upperTimeCutoff t r s + lowerTimeCutoff t ε s *
          ((-(deriv CKN.smoothTransitionProfile
            ((t + 3 * r ^ 2 - s) / ((199 / 100) * r ^ 2))) /
            ((199 / 100) * r ^ 2))) := by
    rw [hl.deriv, hu.deriv]
  change HasDerivAt (lowerTimeCutoff t ε * upperTimeCutoff t r)
    (deriv (lowerTimeCutoff t ε) s * upperTimeCutoff t r s +
      lowerTimeCutoff t ε s * deriv (upperTimeCutoff t r) s) s
  rw [hcoef]
  exact hp

private theorem caccioppoliTimeWeight_deriv_bounds {t r ε s : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hεsmall : 4 * ε < r ^ 2) :
    (s ≤ t + r ^ 2 → 0 ≤ deriv (caccioppoliTimeWeight t r ε) s) ∧
    (t + r ^ 2 ≤ s → deriv (caccioppoliTimeWeight t r ε) s ≤ 0 ∧
      |deriv (caccioppoliTimeWeight t r ε) s| ≤
        (800 / 199) / r ^ 2) := by
  have hupperden : 0 < (199 / 100 : ℝ) * r ^ 2 := by positivity
  have hlowerden : 0 < ε := hε
  have hlowerFactor (hs : s ≤ t + r ^ 2) :
      0 ≤ deriv (lowerTimeCutoff t ε) s := by
    rw [(lowerTimeCutoff_hasDerivAt hε).deriv]
    apply div_nonneg
    · exact smoothTransitionProfile_deriv_nonneg _
    · exact hε.le
  have hupperConst (hs : s ≤ t + r ^ 2) :
      upperTimeCutoff t r s = 1 ∧ deriv (upperTimeCutoff t r) s = 0 := by
    have hrSq : 0 < r ^ 2 := sq_pos_of_pos hr
    have harg : 1 < (t + 3 * r ^ 2 - s) / ((199 / 100) * r ^ 2) := by
      rw [one_lt_div hupperden]
      nlinarith only [hs, hrSq]
    refine ⟨?_, ?_⟩
    · unfold upperTimeCutoff
      exact CKN.smoothTransitionProfile.one_of_one_le harg.le
    · rw [(upperTimeCutoff_hasDerivAt hr).deriv]
      rw [smoothTransitionProfile_deriv_zero_of_one_lt harg]
      simp
  have hlowerConst (hs : t + r ^ 2 ≤ s) :
      lowerTimeCutoff t ε s = 1 ∧ deriv (lowerTimeCutoff t ε) s = 0 := by
    have harg : 1 < (s - (t + ε)) / ε := by
      rw [one_lt_div hε]
      nlinarith only [hs, hεsmall]
    refine ⟨?_, ?_⟩
    · unfold lowerTimeCutoff
      exact CKN.smoothTransitionProfile.one_of_one_le harg.le
    · rw [(lowerTimeCutoff_hasDerivAt hε).deriv]
      rw [smoothTransitionProfile_deriv_zero_of_one_lt harg]
      simp
  refine ⟨?_, ?_⟩
  · intro hs
    rw [(caccioppoliTimeWeight_hasDerivAt hε hr).deriv]
    rcases hupperConst hs with ⟨hu, hdu⟩
    rw [hu, hdu]
    simpa using mul_nonneg (hlowerFactor hs) (by norm_num : 0 ≤ (1 : ℝ))
  · intro hs
    have htheta : deriv (caccioppoliTimeWeight t r ε) s =
        deriv (upperTimeCutoff t r) s := by
      rw [(caccioppoliTimeWeight_hasDerivAt hε hr).deriv]
      rcases hlowerConst hs with ⟨hl, hdl⟩
      rw [hl, hdl]
      ring
    rw [htheta, (upperTimeCutoff_hasDerivAt hr).deriv]
    have hprofile : 0 ≤ deriv CKN.smoothTransitionProfile
        ((t + 3 * r ^ 2 - s) / ((199 / 100) * r ^ 2)) :=
      smoothTransitionProfile_deriv_nonneg _
    have hprofileAbs : |deriv CKN.smoothTransitionProfile
        ((t + 3 * r ^ 2 - s) / ((199 / 100) * r ^ 2))| ≤ 8 :=
      smoothTransitionProfile_deriv_abs_le_eight _
    constructor
    · apply div_nonpos_of_nonpos_of_nonneg
      · exact neg_nonpos.mpr hprofile
      · exact hupperden.le
    · have hdiv : |(-deriv CKN.smoothTransitionProfile
          ((t + 3 * r ^ 2 - s) / ((199 / 100) * r ^ 2)) /
            ((199 / 100) * r ^ 2))| ≤ 8 / ((199 / 100) * r ^ 2) := by
        rw [abs_div, abs_neg, abs_of_pos hupperden]
        exact div_le_div_of_nonneg_right (by linarith only [hprofileAbs]) hupperden.le
      calc
        |(-deriv CKN.smoothTransitionProfile
            ((t + 3 * r ^ 2 - s) / ((199 / 100) * r ^ 2)) /
              ((199 / 100) * r ^ 2))| ≤ 8 / ((199 / 100) * r ^ 2) := hdiv
        _ = (800 / 199) / r ^ 2 := by
          field_simp [ne_of_gt hr]
          ring

/-- Properties of the spatial weight used in the local energy estimate. -/
theorem caccioppoliSpatialWeight_properties (x₀ : Vec3) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (caccioppoliSpatialWeight x₀ r) ∧
    HasCompactSupport (caccioppoliSpatialWeight x₀ r) ∧
    tsupport (caccioppoliSpatialWeight x₀ r) ⊆ vec3Ball x₀ (2 * r) ∧
    (∀ y, vec3EuclideanNorm (y - x₀) < r →
      caccioppoliSpatialWeight x₀ r y = 1) ∧
    (∀ y, 0 ≤ caccioppoliSpatialWeight x₀ r y ∧
      caccioppoliSpatialWeight x₀ r y ≤ 1 ∧
      vec3EuclideanNorm (classicalGradient (caccioppoliSpatialWeight x₀ r) y) ≤
        (400 / 99) / r) := by
  refine ⟨caccioppoliSpatialWeight_smooth x₀ hr,
    caccioppoliSpatialWeight_hasCompactSupport x₀ hr,
    caccioppoliSpatialWeight_tsupport_subset_outer x₀ hr, ?_, ?_⟩
  · intro y hy
    exact caccioppoliSpatialWeight_eq_one hr hy
  · intro y
    exact ⟨caccioppoliSpatialWeight_nonneg x₀ r y,
      caccioppoliSpatialWeight_le_one x₀ r y,
      caccioppoliSpatialWeight_gradient_bound x₀ hr y⟩

/-- Properties of the time weight used in the local energy estimate. -/
theorem caccioppoliTimeWeight_properties {t r ε : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hεsmall : 4 * ε < r ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (caccioppoliTimeWeight t r ε) ∧
    HasCompactSupport (caccioppoliTimeWeight t r ε) ∧
    tsupport (caccioppoliTimeWeight t r ε) ⊆ Icc (t + ε) (t + 3 * r ^ 2) ∧
    (∀ s, t + 2 * ε ≤ s → s ≤ t + r ^ 2 →
      caccioppoliTimeWeight t r ε s = 1) ∧
    (∀ s, 0 ≤ caccioppoliTimeWeight t r ε s ∧
      caccioppoliTimeWeight t r ε s ≤ 1) ∧
    (∀ s, s ≤ t + r ^ 2 → 0 ≤ deriv (caccioppoliTimeWeight t r ε) s) ∧
    (∀ s, t + r ^ 2 ≤ s →
      deriv (caccioppoliTimeWeight t r ε) s ≤ 0 ∧
      |deriv (caccioppoliTimeWeight t r ε) s| ≤ (800 / 199) / r ^ 2) := by
  have hlow : ∀ s, s ≤ t + r ^ 2 →
      0 ≤ deriv (caccioppoliTimeWeight t r ε) s := by
    intro s hs
    exact (caccioppoliTimeWeight_deriv_bounds (t := t) (r := r) (ε := ε)
      (s := s) hε hr hεsmall).1 hs
  have hhigh : ∀ s, t + r ^ 2 ≤ s →
      deriv (caccioppoliTimeWeight t r ε) s ≤ 0 ∧
        |deriv (caccioppoliTimeWeight t r ε) s| ≤ (800 / 199) / r ^ 2 := by
    intro s hs
    exact (caccioppoliTimeWeight_deriv_bounds (t := t) (r := r) (ε := ε)
      (s := s) hε hr hεsmall).2 hs
  refine ⟨caccioppoliTimeWeight_smooth t r ε,
    caccioppoliTimeWeight_hasCompactSupport t r ε hε hr,
    caccioppoliTimeWeight_tsupport_subset t r ε hε hr, ?_, ?_, hlow, hhigh⟩
  · intro s hs₁ hs₂
    exact caccioppoliTimeWeight_eq_one hε hr hs₁ hs₂
  · intro s
    exact caccioppoliTimeWeight_nonneg_le_one t r ε s


end ESS
