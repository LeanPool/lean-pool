/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneIntegralWeakDerivative
public import LeanPool.FastDynamo.Local.PonomarenkoCrossNormalizedAxial
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import LeanPool.FastDynamo.Local.RadialVelocity

/-!
# Parameterized smoothing of the Ponomarenko jump velocity

This module builds the radial cutoff `χ_h` of `eq:smooth-local-velocity` as a squared-radius
Schwartz profile, together with the transition annulus on which a smoothed velocity can
differ from the jump velocity `V⁰` of `eq:jump-flow`.

For a width `0 < h < 1` the cutoff is one on the ball of radius `1 - h` and vanishes outside
the ball of radius `1 + h`.  The free-`Ω` smoothed velocity
`parameterizedSmoothedVelocity h Ω U` of `Local/ParameterizedHelicalProfile.lean` is built on
`parameterizedRadialProfile`; it can differ from the discontinuous Ponomarenko velocity only on
the transition annulus `1 - h < |y| < 1 + h`, of area `4πh`, and the `L⁴` estimate
`‖v_h - V⁰‖_{L⁴} = O(h^{1/4})` of the proof of `prop:local-seed` is proved in
`Local/HorizontalSmoothedVelocity.lean` from the annulus and its area computed here.

This is only the coefficient-level smoothing step; no spectral conclusion is drawn here.

## Contents

* Parameterized smoothing: the width type `PonomarenkoSmoothingWidth`, the cutoff
  `parameterizedRadialCutoff` with its smoothness, range, plateau and support properties, its
  slope `parameterizedRadialSlope`, the profile `parameterizedRadialProfile` and its reality,
  and the transition annulus `ponomarenkoSmoothingAnnulus`.
* The closed transition annulus `ponomarenkoSmoothingClosedAnnulus`, its measurability and its
  area `volume_ponomarenkoSmoothingClosedAnnulus`.
-/

@[expose] public section

/-!
## Parameterized smoothing of the Ponomarenko jump velocity

For a width `0 < h < 1`, a radial `C∞` cutoff which is
one on the ball of radius `1 - h` and zero outside the ball of radius
`1 + h`, packaged as the squared-radius Schwartz profile from which the smoothed
helical velocity is built.

This is only the coefficient-level smoothing step.  No spectral conclusion is
made here.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal LineDeriv SchwartzMap RealInnerProductSpace

/-- Admissible widths for the radial smoothing layer. -/
abbrev PonomarenkoSmoothingWidth := Set.Ioo (0 : ℝ) 1

/-- The argument of `Real.smoothTransition`.  Its values `1` and `0`
correspond respectively to squared radii `(1-h)^2` and `(1+h)^2`. -/
def parameterizedRadialArgument (h : PonomarenkoSmoothingWidth)
    (y : WholePlane) : ℝ :=
  (((1 + (h : ℝ)) ^ 2 - ‖y‖ ^ 2) / (4 * (h : ℝ)))

/-- The real radial cutoff of transition width `h`. -/
def parameterizedRadialCutoff (h : PonomarenkoSmoothingWidth)
    (y : WholePlane) : ℝ :=
  Real.smoothTransition (parameterizedRadialArgument h y)

/-- Complex-valued version of the parameterized cutoff. -/
def parameterizedRadialCutoffC (h : PonomarenkoSmoothingWidth)
    (y : WholePlane) : ℂ :=
  (parameterizedRadialCutoff h y : ℂ)

/-- The radial cutoff of width `h` is smooth of every order, being Mathlib's smooth transition
composed with the smooth map `y ↦ ((1+h)² - ‖y‖²)/(4h)`. -/
theorem parameterizedRadialCutoff_contDiff
    (h : PonomarenkoSmoothingWidth) :
    ContDiff ℝ (⊤ : ℕ∞) (parameterizedRadialCutoff h) := by
  unfold parameterizedRadialCutoff
  apply Real.smoothTransition.contDiff.comp
  unfold parameterizedRadialArgument
  exact (contDiff_const.sub (contDiff_norm_sq ℝ)).div_const _

/-- The complex-valued radial cutoff of width `h` is smooth of every order. -/
theorem parameterizedRadialCutoffC_contDiff
    (h : PonomarenkoSmoothingWidth) :
    ContDiff ℝ (⊤ : ℕ∞) (parameterizedRadialCutoffC h) := by
  exact Complex.ofRealCLM.contDiff.comp
    (parameterizedRadialCutoff_contDiff h)

/-- The radial cutoff takes values in `[0, 1]`. -/
theorem parameterizedRadialCutoff_mem_Icc
    (h : PonomarenkoSmoothingWidth) (y : WholePlane) :
    parameterizedRadialCutoff h y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The cutoff equals one on the closed ball of radius `1 - h`, so the smoothed velocity agrees
with the solid screw flow there. -/
theorem parameterizedRadialCutoff_one_of_norm_le
    (h : PonomarenkoSmoothingWidth) {y : WholePlane}
    (hy : ‖y‖ ≤ 1 - (h : ℝ)) :
    parameterizedRadialCutoff h y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  unfold parameterizedRadialArgument
  have hh : 0 < (h : ℝ) := h.2.1
  have hr : 0 ≤ 1 - (h : ℝ) := by linarith [h.2.2]
  apply (le_div_iff₀ (by positivity : 0 < 4 * (h : ℝ))).2
  have hsquare : ‖y‖ ^ 2 ≤ (1 - (h : ℝ)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg y) hr).2 hy
  nlinarith

/-- The cutoff vanishes for `‖y‖ ≥ 1 + h`, so the smoothed velocity is supported in the ball of
radius `1 + h`. -/
theorem parameterizedRadialCutoff_zero_of_radius_le_norm
    (h : PonomarenkoSmoothingWidth) {y : WholePlane}
    (hy : 1 + (h : ℝ) ≤ ‖y‖) :
    parameterizedRadialCutoff h y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  unfold parameterizedRadialArgument
  have hh : 0 < (h : ℝ) := h.2.1
  apply div_nonpos_iff.mpr
  right
  constructor
  · have hsquare : (1 + (h : ℝ)) ^ 2 ≤ ‖y‖ ^ 2 :=
      (sq_le_sq₀ (by linarith [hh]) (norm_nonneg y)).2 hy
    linarith
  · positivity

/-- The cutoff has compact support, contained in the closed ball of radius `1 + h`. -/
theorem parameterizedRadialCutoff_hasCompactSupport
    (h : PonomarenkoSmoothingWidth) :
    HasCompactSupport (parameterizedRadialCutoff h) := by
  apply HasCompactSupport.intro
    (isCompact_closedBall (0 : WholePlane) (1 + (h : ℝ)))
  intro y hy
  apply parameterizedRadialCutoff_zero_of_radius_le_norm h
  have hyr : 1 + (h : ℝ) < ‖y‖ := by
    simpa [mem_closedBall, dist_zero_right, not_le] using hy
  exact hyr.le

/-- The complex-valued cutoff has compact support. -/
theorem parameterizedRadialCutoffC_hasCompactSupport
    (h : PonomarenkoSmoothingWidth) :
    HasCompactSupport (parameterizedRadialCutoffC h) :=
  (parameterizedRadialCutoff_hasCompactSupport h).comp_left rfl

/-- The parameterized cutoff as a Schwartz function. -/
def parameterizedRadialCutoffSchwartz
    (h : PonomarenkoSmoothingWidth) : SchwartzMap WholePlane ℂ :=
  (parameterizedRadialCutoffC_hasCompactSupport h).toSchwartzMap
    (parameterizedRadialCutoffC_contDiff h)

/-- The Schwartz packaging of the width-`h` cutoff evaluates to the cutoff itself. -/
@[simp] theorem parameterizedRadialCutoffSchwartz_apply
    (h : PonomarenkoSmoothingWidth) (y : WholePlane) :
    parameterizedRadialCutoffSchwartz h y =
      (parameterizedRadialCutoff h y : ℂ) :=
  rfl

/-- The slope in the identity `∂ⱼ χₕ = 2 yⱼ slope`. -/
def parameterizedRadialSlope (h : PonomarenkoSmoothingWidth)
    (y : WholePlane) : ℂ :=
  -((deriv Real.smoothTransition
      (parameterizedRadialArgument h y) : ℝ) : ℂ) /
    (4 * (h : ℝ) : ℝ)

/-- The `j`-th coordinate line derivative of the width-`h` cutoff factors through the squared
radius: `∂ⱼ χₕ (y) = 2 yⱼ · parameterizedRadialSlope h y`.  This is the identity making the
cutoff a `SquaredRadiusSchwartzProfile`. -/
theorem lineDeriv_parameterizedRadialCutoffSchwartz
    (h : PonomarenkoSmoothingWidth) (j : Fin 2) (y : WholePlane) :
    (∂_{wholePlaneBasis j} (parameterizedRadialCutoffSchwartz h)) y =
      2 * (y j : ℂ) * parameterizedRadialSlope h y := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hs : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (parameterizedRadialArgument h y))
      (parameterizedRadialArgument h y) :=
    ((@Real.smoothTransition.contDiff 1).differentiable (by simp))
      (parameterizedRadialArgument h y) |>.hasDerivAt
  have hq : HasFDerivAt (parameterizedRadialArgument h)
      ((-(2 / (4 * (h : ℝ)))) • innerSL ℝ y) y := by
    unfold parameterizedRadialArgument
    have hbase := ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_sub
      ((1 + (h : ℝ)) ^ 2)).mul_const (4 * (h : ℝ))⁻¹
    have heq : (4 * (h : ℝ))⁻¹ • (-(2 • innerSL ℝ y)) =
        (-(2 / (4 * (h : ℝ)))) • innerSL ℝ y := by
      apply ContinuousLinearMap.ext
      intro z
      simp only [smul_apply, neg_apply, smul_eq_mul]
      ring
    simpa only [div_eq_mul_inv] using hbase.congr_fderiv heq
  have hreal := hs.comp_hasFDerivAt y hq
  have hc := Complex.ofRealCLM.hasFDerivAt.comp y hreal
  change (fderiv ℝ
    (Complex.ofRealCLM ∘ Real.smoothTransition ∘
      parameterizedRadialArgument h) y) (wholePlaneBasis j) = _
  rw [hc.fderiv]
  simp [parameterizedRadialSlope, inner_wholePlaneBasis]
  ring

/-- The squared-radius profile attached to a smoothing width. -/
def parameterizedRadialProfile
    (h : PonomarenkoSmoothingWidth) : SquaredRadiusSchwartzProfile where
  value := parameterizedRadialCutoffSchwartz h
  slope := parameterizedRadialSlope h
  lineDeriv_value := lineDeriv_parameterizedRadialCutoffSchwartz h

/-- On the closed ball of radius `1 - h` the width-`h` profile takes the value `1`. -/
theorem parameterizedRadialProfile_value_one
    (h : PonomarenkoSmoothingWidth) {y : WholePlane}
    (hy : ‖y‖ ≤ 1 - (h : ℝ)) :
    (parameterizedRadialProfile h).value y = 1 := by
  simp [parameterizedRadialProfile,
    parameterizedRadialCutoff_one_of_norm_le h hy]

/-- Outside the ball of radius `1 + h` the width-`h` profile vanishes. -/
theorem parameterizedRadialProfile_value_zero
    (h : PonomarenkoSmoothingWidth) {y : WholePlane}
    (hy : 1 + (h : ℝ) ≤ ‖y‖) :
    (parameterizedRadialProfile h).value y = 0 := by
  simp [parameterizedRadialProfile,
    parameterizedRadialCutoff_zero_of_radius_le_norm h hy]

/-- The width-`h` profile is real valued. -/
theorem parameterizedRadialProfile_value_real
    (h : PonomarenkoSmoothingWidth) (y : WholePlane) :
    ((parameterizedRadialProfile h).value y).im = 0 := by
  simp [parameterizedRadialProfile]

/-- The radial slope of the width-`h` profile is real valued. -/
theorem parameterizedRadialProfile_slope_real
    (h : PonomarenkoSmoothingWidth) (y : WholePlane) :
    ((parameterizedRadialProfile h).slope y).im = 0 := by
  simp [parameterizedRadialProfile, parameterizedRadialSlope,
    Complex.div_im]

/-- The open annulus on which smoothing can alter the jump velocity. -/
def ponomarenkoSmoothingAnnulus (h : PonomarenkoSmoothingWidth) :
    Set WholePlane :=
  {y | 1 - (h : ℝ) < ‖y‖ ∧ ‖y‖ < 1 + (h : ℝ)}

/-! ## The closed transition annulus -/

/-- A measurable closed annulus containing the support of the smoothing
error.  Its boundary convention is convenient for the exact volume formula
and has no effect on the `L⁴` class. -/
def ponomarenkoSmoothingClosedAnnulus
    (h : PonomarenkoSmoothingWidth) : Set WholePlane :=
  closedBall (0 : WholePlane) (1 + (h : ℝ)) \
    ball (0 : WholePlane) (1 - (h : ℝ))

/-- The closed transition annulus, being a closed ball minus an open ball, is measurable. -/
theorem measurableSet_ponomarenkoSmoothingClosedAnnulus
    (h : PonomarenkoSmoothingWidth) :
    MeasurableSet (ponomarenkoSmoothingClosedAnnulus h) :=
  measurableSet_closedBall.diff measurableSet_ball

/-- The transition annulus has exactly area `4 π h`. -/
theorem volume_ponomarenkoSmoothingClosedAnnulus
    (h : PonomarenkoSmoothingWidth) :
    volume (ponomarenkoSmoothingClosedAnnulus h) =
      ENNReal.ofReal (4 * Real.pi * (h : ℝ)) := by
  rw [ponomarenkoSmoothingClosedAnnulus]
  rw [measure_sdiff]
  · rw [EuclideanSpace.volume_closedBall_fin_two,
      EuclideanSpace.volume_ball_fin_two]
    have hh0 : 0 ≤ (h : ℝ) := h.2.1.le
    have hinner : 0 ≤ 1 - (h : ℝ) := by linarith [h.2.2]
    have houter : 0 ≤ 1 + (h : ℝ) := by linarith
    rw [← ENNReal.ofReal_pow houter, ← ENNReal.ofReal_pow hinner,
      ← ENNReal.ofReal_mul (sq_nonneg (1 + (h : ℝ))),
      ← ENNReal.ofReal_mul (sq_nonneg (1 - (h : ℝ))),
      ← ENNReal.ofReal_sub]
    · congr 1
      ring
    · positivity
  · intro y hy
    simp only [mem_ball, mem_closedBall, dist_zero_right] at hy ⊢
    linarith [h.2.1]
  · exact measurableSet_ball.nullMeasurableSet
  · rw [EuclideanSpace.volume_ball_fin_two]
    finiteness

end

end FastDynamo
