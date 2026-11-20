/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.WholePlaneLocal

/-!
# Squared-radius helical Schwartz velocities

The local instability construction needs its velocity presented as a
`WholePlaneVelocityCoefficients` package.  This module performs both steps of that
packaging.  First, an arbitrary Schwartz vector field on the transverse plane is converted
into whole-plane velocity coefficients by taking its actual directional derivatives in the
two coordinate directions; the resulting package automatically carries the weak-gradient
certificate.

The concrete field is then built from a scalar Schwartz profile of the squared radius.
Writing the profile as `χ(|y|²)` avoids differentiating the nonsmooth map `y ↦ |y|` at the
origin and produces exactly the velocity of `eq:smooth-local-velocity`

`(-Ω y₂ χ(|y|²), Ω y₁ χ(|y|²), U χ(|y|²))`

as a `C3`-valued Schwartz map whose transverse divergence cancels pointwise.  (The
paper writes the cut-off as `χ_h(|y|)`; here the profile is a Schwartz function of `|y|²`.)  The
generic packaging supplies the weak-gradient certificate required by the whole-plane local
operator.

## Contents

* Schwartz velocities as whole-plane coefficients: the generic constructor
  `wholePlaneSchwartzVelocityCoefficients` and its weak-gradient certificate.
* Squared-radius helical Schwartz velocities: the complex coordinate multiplier, the profile
  structure `SquaredRadiusSchwartzProfile`, the field `squaredRadiusHelicalVelocity`, its
  componentwise line derivatives, the pointwise cancellation of its transverse divergence,
  and the weak-gradient certificate inherited from the first part.
-/

@[expose] public section

/-!
## Schwartz velocities as whole-plane coefficients

The first analytic packaging step.  A Schwartz vector field on the transverse plane
is converted into `WholePlaneVelocityCoefficients` by taking its actual
directional derivatives in the two coordinate directions.

The resulting coefficients automatically carry the weak-gradient certificate
expected by the whole-plane local operator.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

/-- Viewing an `L∞` function as a tempered distribution agrees definitionally
with the corresponding bundled coercion. -/
@[simp] theorem wholePlaneLInfToTempered_eq_coe
    (f : WholePlaneC3LInf) :
    wholePlaneLInfToTempered C3 f =
      (f : TemperedDistribution WholePlane C3) :=
  rfl

/-- Package a Schwartz velocity together with its actual transverse
directional derivatives as bounded whole-plane velocity coefficients. -/
def wholePlaneSchwartzVelocityCoefficients
    (u : SchwartzMap WholePlane C3) : WholePlaneVelocityCoefficients where
  value := u.toLp ∞ volume
  deriv j := (∂_{wholePlaneBasis j} u).toLp ∞ volume

/-- The value field of the coefficient package built from a Schwartz velocity `u` is the `L∞`
class of `u` itself. -/
@[simp] theorem wholePlaneSchwartzVelocityCoefficients_value
    (u : SchwartzMap WholePlane C3) :
    (wholePlaneSchwartzVelocityCoefficients u).value = u.toLp ∞ volume :=
  rfl

/-- The `j`-th derivative field of the coefficient package built from a Schwartz velocity `u` is
the `L∞` class of the directional derivative `∂_{e_j} u`. -/
@[simp] theorem wholePlaneSchwartzVelocityCoefficients_deriv
    (u : SchwartzMap WholePlane C3) (j : Fin 2) :
    (wholePlaneSchwartzVelocityCoefficients u).deriv j =
      (∂_{wholePlaneBasis j} u).toLp ∞ volume :=
  rfl

/-- The derivatives bundled by `wholePlaneSchwartzVelocityCoefficients` are
the distributional weak derivatives of its value. -/
theorem wholePlaneSchwartzVelocityCoefficients_hasWeakGradient
    (u : SchwartzMap WholePlane C3) :
    (wholePlaneSchwartzVelocityCoefficients u).HasWeakGradient := by
  constructor
  intro j
  rw [wholePlaneSchwartzVelocityCoefficients_value,
    wholePlaneSchwartzVelocityCoefficients_deriv,
    wholePlaneLInfToTempered_eq_coe,
    wholePlaneLInfToTempered_eq_coe,
    Lp.toTemperedDistribution_toLp_eq,
    Lp.toTemperedDistribution_toLp_eq]
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq
    (μ := (volume : Measure WholePlane)) u (wholePlaneBasis j)

end

end FastDynamo

/-!
## Squared-radius helical Schwartz velocities

The helical velocity shape used in the local instability argument, built from a
scalar Schwartz profile depending on squared radius.  Writing the profile as
`χ(|y|²)` avoids differentiating the nonsmooth map `y ↦ |y|` at the origin and
produces exactly the field of `eq:smooth-local-velocity`

`(-Ω y₂ χ(|y|²), Ω y₁ χ(|y|²), U χ(|y|²))`.

The construction is a `C3`-valued Schwartz map.  Its transverse divergence cancels
pointwise, and the generic Schwartz packaging above supplies the weak-gradient
certificate required by the whole-plane local operator.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

/-- The complexification of one transverse coordinate. -/
def wholePlaneComplexCoord (j : Fin 2) (y : WholePlane) : ℂ :=
  (y j : ℂ)

/-- The complexified coordinate `y ↦ (y j : ℂ)` is linear, hence of temperate growth, so it may be
used as a Schwartz multiplier. -/
theorem wholePlaneComplexCoord_hasTemperateGrowth (j : Fin 2) :
    (wholePlaneComplexCoord j).HasTemperateGrowth := by
  change (⇑(Complex.ofRealCLM.comp (EuclideanSpace.proj j))).HasTemperateGrowth
  exact (Complex.ofRealCLM.comp (EuclideanSpace.proj j)).hasTemperateGrowth

/-- Multiplication of a scalar Schwartz function by one coordinate. -/
def wholePlaneCoordMulSchwartz (j : Fin 2)
    (f : SchwartzMap WholePlane ℂ) : SchwartzMap WholePlane ℂ :=
  SchwartzMap.smulLeftCLM ℂ (wholePlaneComplexCoord j) f

/-- Pointwise value of the coordinate multiplier: multiplying a scalar Schwartz function by the
`j`-th coordinate is the pointwise product `y ↦ yⱼ · f y`. -/
@[simp] theorem wholePlaneCoordMulSchwartz_apply (j : Fin 2)
    (f : SchwartzMap WholePlane ℂ) (y : WholePlane) :
    wholePlaneCoordMulSchwartz j f y = (y j : ℂ) * f y := by
  simp [wholePlaneCoordMulSchwartz,
    wholePlaneComplexCoord_hasTemperateGrowth, wholePlaneComplexCoord]

/-- Product rule for the coordinate multiplier, expressed in the coordinate
directions used by the local operator. -/
theorem lineDeriv_wholePlaneCoordMulSchwartz (j k : Fin 2)
    (f : SchwartzMap WholePlane ℂ) (y : WholePlane) :
    (∂_{wholePlaneBasis k} (wholePlaneCoordMulSchwartz j f)) y =
      ((wholePlaneBasis k j : ℝ) : ℂ) * f y +
        (y j : ℂ) * (∂_{wholePlaneBasis k} f) y := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hfun :
      (⇑(wholePlaneCoordMulSchwartz j f) : WholePlane → ℂ) =
        fun x : WholePlane ↦ wholePlaneComplexCoord j x * f x := by
    funext x
    simp [wholePlaneComplexCoord]
  rw [hfun]
  have hcoord : HasFDerivAt (wholePlaneComplexCoord j)
      (Complex.ofRealCLM.comp (EuclideanSpace.proj j)) y :=
    (Complex.ofRealCLM.comp (EuclideanSpace.proj j)).hasFDerivAt
  change (fderiv ℝ (wholePlaneComplexCoord j * ⇑f) y) (wholePlaneBasis k) = _
  rw [(hcoord.mul (f.hasFDerivAt y)).fderiv]
  simp [wholePlaneComplexCoord, mul_comm]
  ring

/-- Embed a scalar Schwartz function as one coordinate of a `C3` field. -/
def wholePlaneC3SingleSchwartz (i : Fin 3)
    (f : SchwartzMap WholePlane ℂ) : SchwartzMap WholePlane C3 :=
  SchwartzMap.postcompCLM
    (ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single i 1)) f

/-- Pointwise value of the single-component embedding: the `k`-th component of the `C3` field
built from `f` in slot `i` is `f y` when `k = i` and `0` otherwise. -/
@[simp] theorem wholePlaneC3SingleSchwartz_apply (i k : Fin 3)
    (f : SchwartzMap WholePlane ℂ) (y : WholePlane) :
    wholePlaneC3SingleSchwartz i f y k = if i = k then f y else 0 := by
  simp [wholePlaneC3SingleSchwartz, ContinuousLinearMap.toSpanSingleton_apply,
    eq_comm]

/-- Directional differentiation commutes with embedding a scalar Schwartz
function into one component. -/
theorem lineDeriv_wholePlaneC3SingleSchwartz_apply
    (i k : Fin 3) (j : Fin 2) (f : SchwartzMap WholePlane ℂ)
    (y : WholePlane) :
    (∂_{wholePlaneBasis j} (wholePlaneC3SingleSchwartz i f)) y k =
      if i = k then (∂_{wholePlaneBasis j} f) y else 0 := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  let L : ℂ →L[ℂ] C3 :=
    ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single i 1)
  have hfun :
      (⇑(wholePlaneC3SingleSchwartz i f) : WholePlane → C3) =
        fun x : WholePlane ↦ L (f x) := by
    funext x
    rfl
  rw [hfun]
  have hcomp := (L.restrictScalars ℝ).hasFDerivAt.comp y (f.hasFDerivAt y)
  change ((fderiv ℝ (⇑(L.restrictScalars ℝ) ∘ ⇑f) y)
    (wholePlaneBasis j)) k = _
  rw [hcomp.fderiv]
  simp [L, ContinuousLinearMap.toSpanSingleton_apply, eq_comm]

/-- A scalar Schwartz profile carrying the differential identity of a
function of squared radius. The field `slope` represents the derivative
of the one-dimensional profile evaluated at `|y|²`. -/
structure SquaredRadiusSchwartzProfile where
  /-- The scalar Schwartz cutoff evaluated on the transverse plane. -/
  value : SchwartzMap WholePlane ℂ
  /-- The radial slope appearing in the identity
  `∂ⱼ value(y) = 2 yⱼ slope(y)`. -/
  slope : WholePlane → ℂ
  lineDeriv_value : ∀ (j : Fin 2) (y : WholePlane),
    (∂_{wholePlaneBasis j} value) y = 2 * (y j : ℂ) * slope y

/-- The helical velocity
`(-Ω y₂ χ(|y|²), Ω y₁ χ(|y|²), U χ(|y|²))`
attached to a squared-radius Schwartz profile. -/
def squaredRadiusHelicalVelocity
    (profile : SquaredRadiusSchwartzProfile) (Ω U : ℝ) :
    SchwartzMap WholePlane C3 :=
  wholePlaneC3SingleSchwartz 0
      ((-(Ω : ℂ)) • wholePlaneCoordMulSchwartz 1 profile.value) +
    wholePlaneC3SingleSchwartz 1
      ((Ω : ℂ) • wholePlaneCoordMulSchwartz 0 profile.value) +
    wholePlaneC3SingleSchwartz 2 ((U : ℂ) • profile.value)

/-- First Cartesian component of the helical velocity `χ(|y|²)(-Ω y₂, Ω y₁, U)` of
`eq:smooth-local-velocity`: it equals `-Ω y₂ χ(|y|²)`. -/
@[simp] theorem squaredRadiusHelicalVelocity_apply_zero
    (profile : SquaredRadiusSchwartzProfile) (Ω U : ℝ) (y : WholePlane) :
    squaredRadiusHelicalVelocity profile Ω U y 0 =
      -(Ω : ℂ) * (y 1 : ℂ) * profile.value y := by
  simp [squaredRadiusHelicalVelocity, mul_assoc]

/-- Second Cartesian component of the helical velocity `χ(|y|²)(-Ω y₂, Ω y₁, U)`: it equals
`Ω y₁ χ(|y|²)`. -/
@[simp] theorem squaredRadiusHelicalVelocity_apply_one
    (profile : SquaredRadiusSchwartzProfile) (Ω U : ℝ) (y : WholePlane) :
    squaredRadiusHelicalVelocity profile Ω U y 1 =
      (Ω : ℂ) * (y 0 : ℂ) * profile.value y := by
  simp [squaredRadiusHelicalVelocity, mul_assoc]

/-- Axial component of the helical velocity `χ(|y|²)(-Ω y₂, Ω y₁, U)`: it equals `U χ(|y|²)`. -/
@[simp] theorem squaredRadiusHelicalVelocity_apply_two
    (profile : SquaredRadiusSchwartzProfile) (Ω U : ℝ) (y : WholePlane) :
    squaredRadiusHelicalVelocity profile Ω U y 2 =
      (U : ℂ) * profile.value y := by
  simp [squaredRadiusHelicalVelocity]

/-- The first component of each transverse derivative of the helical
velocity. -/
theorem lineDeriv_squaredRadiusHelicalVelocity_apply_zero
    (profile : SquaredRadiusSchwartzProfile) (Ω U : ℝ)
    (j : Fin 2) (y : WholePlane) :
    (∂_{wholePlaneBasis j} (squaredRadiusHelicalVelocity profile Ω U)) y 0 =
      -(Ω : ℂ) *
        (((wholePlaneBasis j 1 : ℝ) : ℂ) * profile.value y +
          (y 1 : ℂ) * (2 * (y j : ℂ) * profile.slope y)) := by
  simp only [squaredRadiusHelicalVelocity,
    LineDerivAdd.lineDerivOp_add, add_apply, PiLp.add_apply]
  rw [lineDeriv_wholePlaneC3SingleSchwartz_apply,
    lineDeriv_wholePlaneC3SingleSchwartz_apply,
    lineDeriv_wholePlaneC3SingleSchwartz_apply]
  simp only [LineDerivSMul.lineDerivOp_smul, smul_apply, smul_eq_mul]
  simp only [↓reduceIte, Fin.isValue, neg_mul, one_ne_zero, add_zero, Fin.reduceEq, neg_inj,
    mul_eq_mul_left_iff, Complex.ofReal_eq_zero]
  rw [lineDeriv_wholePlaneCoordMulSchwartz, profile.lineDeriv_value]
  simp

/-- The second component of each transverse derivative of the helical
velocity. -/
theorem lineDeriv_squaredRadiusHelicalVelocity_apply_one
    (profile : SquaredRadiusSchwartzProfile) (Ω U : ℝ)
    (j : Fin 2) (y : WholePlane) :
    (∂_{wholePlaneBasis j} (squaredRadiusHelicalVelocity profile Ω U)) y 1 =
      (Ω : ℂ) *
        (((wholePlaneBasis j 0 : ℝ) : ℂ) * profile.value y +
          (y 0 : ℂ) * (2 * (y j : ℂ) * profile.slope y)) := by
  simp only [squaredRadiusHelicalVelocity,
    LineDerivAdd.lineDerivOp_add, add_apply, PiLp.add_apply]
  rw [lineDeriv_wholePlaneC3SingleSchwartz_apply,
    lineDeriv_wholePlaneC3SingleSchwartz_apply,
    lineDeriv_wholePlaneC3SingleSchwartz_apply]
  simp only [LineDerivSMul.lineDerivOp_smul, smul_apply, smul_eq_mul]
  simp only [Fin.isValue, zero_ne_one, ↓reduceIte, zero_add, Fin.reduceEq, add_zero,
    mul_eq_mul_left_iff, Complex.ofReal_eq_zero]
  rw [lineDeriv_wholePlaneCoordMulSchwartz, profile.lineDeriv_value]
  simp

/-- The axial component of each transverse derivative of the helical
velocity. -/
theorem lineDeriv_squaredRadiusHelicalVelocity_apply_two
    (profile : SquaredRadiusSchwartzProfile) (Ω U : ℝ)
    (j : Fin 2) (y : WholePlane) :
    (∂_{wholePlaneBasis j} (squaredRadiusHelicalVelocity profile Ω U)) y 2 =
      (U : ℂ) * (2 * (y j : ℂ) * profile.slope y) := by
  simp only [squaredRadiusHelicalVelocity,
    LineDerivAdd.lineDerivOp_add, add_apply, PiLp.add_apply]
  rw [lineDeriv_wholePlaneC3SingleSchwartz_apply,
    lineDeriv_wholePlaneC3SingleSchwartz_apply,
    lineDeriv_wholePlaneC3SingleSchwartz_apply]
  simp only [LineDerivSMul.lineDerivOp_smul, smul_apply, smul_eq_mul]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, add_zero, zero_add, mul_eq_mul_left_iff,
    Complex.ofReal_eq_zero]
  rw [profile.lineDeriv_value]
  simp

/-- The transverse divergence of the helical velocity cancels pointwise. -/
theorem squaredRadiusHelicalVelocity_transverseDivergence
    (profile : SquaredRadiusSchwartzProfile) (Ω U : ℝ)
    (y : WholePlane) :
    (∂_{wholePlaneBasis (0 : Fin 2)}
        (squaredRadiusHelicalVelocity profile Ω U)) y (0 : Fin 3) +
      (∂_{wholePlaneBasis (1 : Fin 2)}
        (squaredRadiusHelicalVelocity profile Ω U)) y (1 : Fin 3) = 0 := by
  simp only [squaredRadiusHelicalVelocity,
    LineDerivAdd.lineDerivOp_add, add_apply, PiLp.add_apply]
  rw [lineDeriv_wholePlaneC3SingleSchwartz_apply,
    lineDeriv_wholePlaneC3SingleSchwartz_apply,
    lineDeriv_wholePlaneC3SingleSchwartz_apply,
    lineDeriv_wholePlaneC3SingleSchwartz_apply,
    lineDeriv_wholePlaneC3SingleSchwartz_apply,
    lineDeriv_wholePlaneC3SingleSchwartz_apply]
  simp only [LineDerivSMul.lineDerivOp_smul, smul_apply, smul_eq_mul]
  simp only [↓reduceIte, Fin.isValue, neg_mul, one_ne_zero, add_zero, Fin.reduceEq, zero_ne_one,
    zero_add]
  simp only [lineDeriv_wholePlaneCoordMulSchwartz]
  rw [profile.lineDeriv_value, profile.lineDeriv_value]
  simp [wholePlaneBasis]
  ring

/-- The same concrete coefficient package automatically has its weak
gradient certificate. -/
theorem squaredRadiusHelicalVelocityCoefficients_hasWeakGradient
    (profile : SquaredRadiusSchwartzProfile) (Ω U : ℝ) :
    (wholePlaneSchwartzVelocityCoefficients
      (squaredRadiusHelicalVelocity profile Ω U)).HasWeakGradient :=
  wholePlaneSchwartzVelocityCoefficients_hasWeakGradient _

end

end FastDynamo
