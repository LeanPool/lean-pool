/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.ParameterizedRadialSmoothing
public import LeanPool.FastDynamo.Local.HelicalProfile

/-!
# Helical witnesses for the parameterized radial smoothing

The smoothing construction of `Local/ParameterizedRadialSmoothing.lean` provides a concrete
radial profile and the coefficient-level regularity facts.  This module defines the smoothed
helical velocity `parameterizedSmoothedVelocity h Ω U` (the velocity `v_h` of
`eq:smooth-local-velocity`) and packages it in the `HelicalProfile` interface of
`Local/HelicalProfile.lean`, from which it obtains the weak-gradient certificate of its
coefficients and its vanishing outside the ball of radius `1 + h`.  It makes no spectral
assertion.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Metric Set
open scoped LineDeriv SchwartzMap RealInnerProductSpace

/-! ## Support of the radial slope -/

/-- `Real.smoothTransition` has zero derivative on its constant left
region, including the endpoint. -/
private theorem smoothTransition_deriv_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  have hg (t : ℝ) : HasDerivAt expNegInvGlue
      (((Polynomial.X ^ 2 * ((1 : Polynomial ℝ) -
        Polynomial.derivative (1 : Polynomial ℝ))).eval t⁻¹) *
        expNegInvGlue t) t := by
    simpa using
      (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
        (1 : Polynomial ℝ) t)
  have hnum : HasDerivAt expNegInvGlue 0 x := by
    have h := hg x
    simpa [expNegInvGlue.zero_of_nonpos hx] using h
  have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    convert (hasDerivAt_const x 1).sub (hasDerivAt_id x) using 1 <;>
      first | rfl | simp
  have hden : HasDerivAt (fun t : ℝ =>
      expNegInvGlue t + expNegInvGlue (1 - t))
      (0 + (((Polynomial.X ^ 2 * ((1 : Polynomial ℝ) -
        Polynomial.derivative (1 : Polynomial ℝ))).eval (1 - x)⁻¹) *
        expNegInvGlue (1 - x)) * (-1)) x := by
    have hd := hnum.add ((hg (1 - x)).comp x hsub)
    change HasDerivAt (expNegInvGlue + expNegInvGlue ∘ fun t : ℝ => 1 - t) _ x
    simpa only [Function.comp_apply] using hd
  change deriv (expNegInvGlue / fun t : ℝ =>
    expNegInvGlue t + expNegInvGlue (1 - t)) x = 0
  have hd := (hnum.div hden (Real.smoothTransition.pos_denom x).ne').deriv
  simpa [expNegInvGlue.zero_of_nonpos hx] using hd

/-- The profile's radial slope vanishes at and outside its cutoff radius. -/
theorem parameterizedRadialProfile_slope_zero
    (h : PonomarenkoSmoothingWidth) {y : WholePlane}
    (hy : 1 + (h : ℝ) ≤ ‖y‖) :
    (parameterizedRadialProfile h).slope y = 0 := by
  have harg : parameterizedRadialArgument h y ≤ 0 := by
    unfold parameterizedRadialArgument
    apply div_nonpos_iff.mpr
    right
    constructor
    · have hsquare : (1 + (h : ℝ)) ^ 2 ≤ ‖y‖ ^ 2 :=
        (sq_le_sq₀ (by linarith [h.2.1]) (norm_nonneg y)).2 hy
      linarith
    · exact mul_nonneg (by norm_num) h.2.1.le
  simp [parameterizedRadialProfile, parameterizedRadialSlope,
    smoothTransition_deriv_eq_zero_of_nonpos harg]

/-! ## Interface instantiation -/

/-- The parameterized radial profile with arbitrary real helical speeds. -/
def parameterizedSmoothedVelocity (h : PonomarenkoSmoothingWidth)
    (angularSpeed axialSpeed : ℝ) : SchwartzMap WholePlane C3 :=
  squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
    angularSpeed axialSpeed

/-- The parameterized smoothed velocity has exactly the radial helical form
required by the local-seed interface. -/
def parameterizedSmoothedHelicalProfile (h : PonomarenkoSmoothingWidth)
    (angularSpeed axialSpeed : ℝ) :
    HelicalProfile (parameterizedSmoothedVelocity h angularSpeed axialSpeed) where
  profile := parameterizedRadialProfile h
  angularSpeed := angularSpeed
  axialSpeed := axialSpeed
  velocity_eq := rfl
  supportRadius := 1 + (h : ℝ)
  supportRadius_pos := by linarith [h.2.1]
  value_eq_zero_of_supportRadius_le_norm := by
    intro y hy
    exact parameterizedRadialProfile_value_zero h hy
  slope_eq_zero_of_supportRadius_le_norm := by
    intro y hy
    exact parameterizedRadialProfile_slope_zero h hy
  value_real := parameterizedRadialProfile_value_real h
  slope_real := parameterizedRadialProfile_slope_real h

/-- The Fourier coefficients of the smoothed helical velocity have a weak gradient, so the
velocity is admissible as a coefficient of the induction form at a fixed axial wavenumber. -/
theorem parameterizedSmoothedVelocity_coefficients_hasWeakGradient
    (h : PonomarenkoSmoothingWidth) (angularSpeed axialSpeed : ℝ) :
    (wholePlaneSchwartzVelocityCoefficients
      (parameterizedSmoothedVelocity h angularSpeed axialSpeed)).HasWeakGradient :=
  (parameterizedSmoothedHelicalProfile h angularSpeed axialSpeed).coefficients_hasWeakGradient

/-- The smoothed helical velocity vanishes outside the closed ball of radius `1 + h`, so it is
compactly supported with the smoothing width `h` controlling the overshoot beyond the unit
cylinder. -/
theorem parameterizedSmoothedVelocity_eq_zero_of_radius_le_norm
    (h : PonomarenkoSmoothingWidth) (angularSpeed axialSpeed : ℝ)
    {y : WholePlane} (hy : 1 + (h : ℝ) ≤ ‖y‖) :
    parameterizedSmoothedVelocity h angularSpeed axialSpeed y = 0 :=
  HelicalProfile.velocity_eq_zero_of_supportRadius_le_norm
    (parameterizedSmoothedHelicalProfile h angularSpeed axialSpeed) y hy

end

end FastDynamo
