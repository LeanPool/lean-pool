/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneExteriorCutoff
public import LeanPool.FastDynamo.Local.RadialVelocity
public import LeanPool.FastDynamo.Local.SeedParameters
public import LeanPool.FastDynamo.Operator.Riesz

/-!
# Helical velocity profiles

The local model of the paper is stated for the velocity `v = v_h` of
`eq:smooth-local-velocity`, a compactly supported radial helical field, and the particle-flow
argument (§4) uses that form.  `HelicalProfile velocity` records it as an explicit witness for a
Schwartz velocity: the squared-radius profile, the angular and axial speeds, and a common support
radius for the profile and its slope.  The module proves the weak-gradient certificate of the
coefficients of such a field and its vanishing outside the support radius;
`Local/ParameterizedHelicalProfile.lean` instantiates the witness for the smoothed velocity `v_h`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped SchwartzMap

/-- An explicit witness that a Schwartz velocity is a compactly supported,
real radial helical field

`(-Omega y_2 chi(y), Omega y_1 chi(y), U chi(y))`.

The scalar profile is the squared-radius profile of `RadialVelocity`; its
directional-derivative identity is therefore part of the witness.  A common
support radius for its value and radial slope is recorded because the global
cell construction must place both the velocity and its first derivatives
inside the local core. -/
structure HelicalProfile (velocity : SchwartzMap WholePlane C3) where
  /-- The scalar squared-radius Schwartz profile. -/
  profile : SquaredRadiusSchwartzProfile
  /-- Angular speed in the helical formula. -/
  angularSpeed : ℝ
  /-- Axial speed in the helical formula. -/
  axialSpeed : ℝ
  /-- The velocity is exactly the helical field built from this profile. -/
  velocity_eq :
    velocity = squaredRadiusHelicalVelocity profile angularSpeed axialSpeed
  /-- A positive radius outside which the profile and its slope vanish. -/
  supportRadius : ℝ
  supportRadius_pos : 0 < supportRadius
  value_eq_zero_of_supportRadius_le_norm : ∀ y : WholePlane,
    supportRadius ≤ ‖y‖ → profile.value y = 0
  slope_eq_zero_of_supportRadius_le_norm : ∀ y : WholePlane,
    supportRadius ≤ ‖y‖ → profile.slope y = 0
  /-- Reality of the scalar profile. -/
  value_real : ∀ y : WholePlane, (profile.value y).im = 0
  /-- Reality of the radial slope, hence also of the derivative coefficients. -/
  slope_real : ∀ y : WholePlane, (profile.slope y).im = 0

namespace HelicalProfile

variable {velocity : SchwartzMap WholePlane C3}

/-- The helical witness supplies the weak-gradient certificate for
the coefficient package used by the local operator. -/
theorem coefficients_hasWeakGradient (h : HelicalProfile velocity) :
    (wholePlaneSchwartzVelocityCoefficients velocity).HasWeakGradient := by
  rw [h.velocity_eq]
  exact squaredRadiusHelicalVelocityCoefficients_hasWeakGradient
    h.profile h.angularSpeed h.axialSpeed

/-- The velocity itself vanishes outside the support radius stored in its
helical witness. -/
theorem velocity_eq_zero_of_supportRadius_le_norm
    (h : HelicalProfile velocity) (y : WholePlane)
    (hy : h.supportRadius ≤ ‖y‖) : velocity y = 0 := by
  rw [h.velocity_eq]
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [h.value_eq_zero_of_supportRadius_le_norm y hy]

end HelicalProfile

end

end FastDynamo
