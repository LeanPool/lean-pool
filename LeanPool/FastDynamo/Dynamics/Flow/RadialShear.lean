/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.ParameterizedHelicalProfile

/-!
# The radial shear bound of the smoothed helical profile

The Lipschitz estimate for the explicit particle flow of `prop:particle-flow` rests on the
uniform shear bound `eq:omega-shear-bound`,

```
  sup_{n ≥ 0} sup_{r ≥ 0} r |ω_n'(r)| ≤ |Ω| sup_{s ≥ 0} s |χ_h'(s)| ,
```

which enters through the differential of the cell rotation displayed in the proof of
`prop:particle-flow`,
`D_y (R_{t ω_n(r)} z) = R_{t ω_n(r)} [id + t ω_n'(r) J z ⊗ e_r]`.  The right-hand factor of the
first display is a property of the radial cutoff `χ_h` alone; this module isolates it.

In the formalisation `χ_h` is `parameterizedRadialCutoff h`, a function of `‖w‖²` obtained from
`Real.smoothTransition` (`Local/ParameterizedRadialSmoothing.lean`).  Because it factors through
the squared radius, its differential is the rank-one map `w ↦ 2 σ_h(w) ⟪w, ·⟫` for a scalar slope
`σ_h`, so the scale-invariant quantity `‖w‖ ‖∇χ_h(w)‖` equals `2 ‖w‖² |σ_h(w)|`.  The slope is
continuous and vanishes for `‖w‖ ≥ 1 + h`
(`parameterizedRadialProfile_slope_zero`), so the quantity is a continuous function supported in
the closed ball of radius `1 + h` and its supremum over that ball is attained.  That supremum is
`radialShearBound h`.

## Contents

* `parameterizedRadialRealSlope`, the real form of `parameterizedRadialSlope`, with its
  continuity and its vanishing outside the closed ball of radius `1 + h`.
* `hasFDerivAt_parameterizedRadialCutoff` and `norm_fderiv_parameterizedRadialCutoff`: the
  differential of the cutoff and its norm.
* `radialShearProfile`, the scale-invariant shear quantity, and `radialShearBound`, its supremum.
* `norm_mul_norm_fderiv_parameterizedRadialCutoff_le`, the Lean form of `eq:omega-shear-bound`.

The module imports only the parameterized radial smoothing
layer, so that the cell-level shear bounds can be assembled on top of it.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Metric Set
open scoped RealInnerProductSpace

variable (h : PonomarenkoSmoothingWidth)

/-! ## The real radial slope -/

/-- The real-valued slope in the factorisation `∇χ_h(w) = 2 σ_h(w) ⟪w, ·⟫` of the width-`h`
radial cutoff through the squared radius.  It is the real part of the complex
`parameterizedRadialSlope` of the profile interface, and is the Lean form of the derivative
`χ_h'` of `eq:omega-shear-bound`. -/
def parameterizedRadialRealSlope (w : WholePlane) : ℝ :=
  -(deriv Real.smoothTransition (parameterizedRadialArgument h w)) / (4 * (h : ℝ))

/-- The complex slope of the width-`h` profile is the coercion of the real slope. -/
theorem parameterizedRadialSlope_eq_ofReal (w : WholePlane) :
    parameterizedRadialSlope h w = (parameterizedRadialRealSlope h w : ℂ) := by
  unfold parameterizedRadialSlope parameterizedRadialRealSlope
  push_cast
  ring

/-- The real radial slope vanishes at and outside the cutoff radius `1 + h`; this is
`parameterizedRadialProfile_slope_zero` transported to the real form. -/
theorem parameterizedRadialRealSlope_eq_zero_of_radius_le_norm {w : WholePlane}
    (hw : 1 + (h : ℝ) ≤ ‖w‖) : parameterizedRadialRealSlope h w = 0 := by
  have hz : parameterizedRadialSlope h w = 0 := parameterizedRadialProfile_slope_zero h hw
  rw [parameterizedRadialSlope_eq_ofReal] at hz
  exact_mod_cast hz

/-- The argument `w ↦ ((1 + h)² - ‖w‖²)/(4h)` fed to `Real.smoothTransition` is continuous. -/
theorem continuous_parameterizedRadialArgument :
    Continuous (parameterizedRadialArgument h) := by
  unfold parameterizedRadialArgument
  exact (continuous_const.sub (continuous_norm.pow 2)).div_const _

/-- The real radial slope is continuous: `Real.smoothTransition` is smooth, so its derivative is
continuous, and the squared-radius argument is continuous. -/
theorem continuous_parameterizedRadialRealSlope :
    Continuous (parameterizedRadialRealSlope h) := by
  unfold parameterizedRadialRealSlope
  exact ((((Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)).comp
    (continuous_parameterizedRadialArgument h)).neg).div_const _

/-! ## The differential of the radial cutoff -/

/-- The differential of the squared-radius argument: `∇((1 + h)² - ‖w‖²)/(4h) =
-(2/(4h)) ⟪w, ·⟫`. -/
theorem hasFDerivAt_parameterizedRadialArgument (w : WholePlane) :
    HasFDerivAt (parameterizedRadialArgument h)
      ((-(2 / (4 * (h : ℝ)))) • innerSL ℝ w) w := by
  have hfun : parameterizedRadialArgument h =
      fun y : WholePlane => (4 * (h : ℝ))⁻¹ • ((1 + (h : ℝ)) ^ 2 - ‖y‖ ^ 2) := by
    funext y
    simp only [parameterizedRadialArgument, smul_eq_mul]
    ring
  rw [hfun]
  refine (((hasStrictFDerivAt_norm_sq w).hasFDerivAt.const_sub
    ((1 + (h : ℝ)) ^ 2)).const_smul (4 * (h : ℝ))⁻¹).congr_fderiv ?_
  ext z
  simp only [smul_apply, neg_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The differential of the width-`h` radial cutoff is the rank-one map
`2 σ_h(w) ⟪w, ·⟫`: the cutoff factors through the squared radius, so its gradient is radial.
This is the Lean form of the chain rule behind `eq:omega-shear-bound`. -/
theorem hasFDerivAt_parameterizedRadialCutoff (w : WholePlane) :
    HasFDerivAt (parameterizedRadialCutoff h)
      ((2 * parameterizedRadialRealSlope h w) • innerSL ℝ w) w := by
  have hs : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (parameterizedRadialArgument h w))
      (parameterizedRadialArgument h w) :=
    (((@Real.smoothTransition.contDiff 1).differentiable (by simp))
      (parameterizedRadialArgument h w)).hasDerivAt
  have hcomp := hs.comp_hasFDerivAt w (hasFDerivAt_parameterizedRadialArgument h w)
  have heq : Real.smoothTransition ∘ parameterizedRadialArgument h =
      parameterizedRadialCutoff h := rfl
  rw [heq] at hcomp
  refine hcomp.congr_fderiv ?_
  ext z
  simp only [smul_apply, smul_eq_mul, parameterizedRadialRealSlope]
  ring

/-- The differential of the width-`h` radial cutoff, as an equation for `fderiv`. -/
theorem fderiv_parameterizedRadialCutoff (w : WholePlane) :
    fderiv ℝ (parameterizedRadialCutoff h) w =
      (2 * parameterizedRadialRealSlope h w) • innerSL ℝ w :=
  (hasFDerivAt_parameterizedRadialCutoff h w).fderiv

/-- The operator norm of the gradient of the width-`h` cutoff: `‖∇χ_h(w)‖ = 2 |σ_h(w)| ‖w‖`,
since `‖⟪w, ·⟫‖ = ‖w‖`. -/
theorem norm_fderiv_parameterizedRadialCutoff (w : WholePlane) :
    ‖fderiv ℝ (parameterizedRadialCutoff h) w‖ =
      2 * |parameterizedRadialRealSlope h w| * ‖w‖ := by
  rw [fderiv_parameterizedRadialCutoff, norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
    abs_mul]
  norm_num

/-! ## The shear profile and its supremum -/

/-- The scale-invariant shear quantity `2 ‖w‖² |σ_h(w)|`, the Lean form of `s |χ_h'(s)|` at
`s = ‖w‖` (`eq:omega-shear-bound`).  It equals `‖w‖ ‖∇χ_h(w)‖`. -/
def radialShearProfile (w : WholePlane) : ℝ :=
  2 * ‖w‖ ^ 2 * |parameterizedRadialRealSlope h w|

/-- `‖w‖ ‖∇χ_h(w)‖` is exactly the shear quantity `2 ‖w‖² |σ_h(w)|`. -/
theorem norm_mul_norm_fderiv_parameterizedRadialCutoff_eq (w : WholePlane) :
    ‖w‖ * ‖fderiv ℝ (parameterizedRadialCutoff h) w‖ = radialShearProfile h w := by
  rw [norm_fderiv_parameterizedRadialCutoff, radialShearProfile]
  ring

/-- The shear quantity is continuous, the radial slope being continuous. -/
theorem continuous_radialShearProfile : Continuous (radialShearProfile h) := by
  unfold radialShearProfile
  exact (continuous_const.mul (continuous_norm.pow 2)).mul
    (continuous_parameterizedRadialRealSlope h).abs

/-- The shear quantity vanishes at and outside the cutoff radius `1 + h`, so it is supported in
the closed ball of radius `1 + h`. -/
theorem radialShearProfile_eq_zero_of_radius_le_norm {w : WholePlane}
    (hw : 1 + (h : ℝ) ≤ ‖w‖) : radialShearProfile h w = 0 := by
  simp [radialShearProfile, parameterizedRadialRealSlope_eq_zero_of_radius_le_norm h hw]

/-- The shear quantity is bounded above on the closed ball of radius `1 + h`, being continuous
on a compact set. -/
theorem bddAbove_image_radialShearProfile :
    BddAbove (radialShearProfile h '' closedBall (0 : WholePlane) (1 + (h : ℝ))) :=
  (isCompact_closedBall _ _).bddAbove_image (continuous_radialShearProfile h).continuousOn

/-- `sup_w ‖w‖ ‖∇χ_h(w)‖`, the Lean form of `sup_{s ≥ 0} s |χ_h'(s)|` of `eq:omega-shear-bound`.
The supremum is taken over the closed ball of radius `1 + h`, outside which the
shear quantity vanishes; it is a maximum, the ball being compact and the quantity
continuous. -/
def radialShearBound : ℝ :=
  sSup (radialShearProfile h '' closedBall (0 : WholePlane) (1 + (h : ℝ)))

/-- Inside the closed ball of radius `1 + h` the shear quantity is at most its supremum. -/
theorem radialShearProfile_le_radialShearBound_of_norm_le {w : WholePlane}
    (hw : ‖w‖ ≤ 1 + (h : ℝ)) : radialShearProfile h w ≤ radialShearBound h :=
  le_csSup (bddAbove_image_radialShearProfile h)
    ⟨w, by simpa only [mem_closedBall, dist_zero_right] using hw, rfl⟩

/-- The radial shear bound is nonnegative: the origin lies in the ball and contributes `0`. -/
theorem radialShearBound_nonneg : 0 ≤ radialShearBound h := by
  have hmem : ‖(0 : WholePlane)‖ ≤ 1 + (h : ℝ) := by
    simpa only [norm_zero] using by linarith [h.2.1]
  have h0 := radialShearProfile_le_radialShearBound_of_norm_le h hmem
  rw [radialShearProfile] at h0
  simpa using h0

/-- The shear quantity is bounded by `radialShearBound h` everywhere: inside the ball by the
supremum property, outside it because the quantity vanishes there. -/
theorem radialShearProfile_le_radialShearBound (w : WholePlane) :
    radialShearProfile h w ≤ radialShearBound h := by
  rcases le_or_gt ‖w‖ (1 + (h : ℝ)) with hw | hw
  · exact radialShearProfile_le_radialShearBound_of_norm_le h hw
  · rw [radialShearProfile_eq_zero_of_radius_le_norm h hw.le]
    exact radialShearBound_nonneg h

/-- `eq:omega-shear-bound` at the level of the radial cutoff: the scale-invariant
shear `‖w‖ ‖∇χ_h(w)‖` is bounded by `radialShearBound h`, uniformly in `w`.  Rescaling `w` by the
cell size leaves the left-hand side unchanged, which is what makes the cell-level bound uniform
in the cell index `n`. -/
theorem norm_mul_norm_fderiv_parameterizedRadialCutoff_le (w : WholePlane) :
    ‖w‖ * ‖fderiv ℝ (parameterizedRadialCutoff h) w‖ ≤ radialShearBound h := by
  rw [norm_mul_norm_fderiv_parameterizedRadialCutoff_eq]
  exact radialShearProfile_le_radialShearBound h w

end

end FastDynamo
