/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalModeExteriorSecondDerivatives

/-!
# The bulk eigen-identity of the two-component Ponomarenko mode

This module proves the *bulk* half of the distributional identity that
`Local/HorizontalModeWeakIdentity.lean` takes as input, that is, hypothesis 2 of the assembly
theorem
`horizontalModeDistributionalEquation_of_coordinate_sources` of
`Local/HorizontalModeSurface.lean`.

Write `b` for the two-component mode, `w = V⁰ = 1_{r<1}(Ω r e_θ + U e₃)` for the discontinuous
screw flow of `eq:jump-flow`, and

`D_j = ∂_j b + w_⊥ b_j`,
`M = N² b + w_⊥·∇_⊥ b + iN w₃ b + w_⊥(Div_⊥ b)`

for the two pivot fields of `HorizontalModeWeakIdentity`.  Off the unit circle,

`Σ_j ∂_j D_j = Δ_⊥ b + (b·∇_⊥)w_⊥ + w_⊥(Div_⊥ b)`,

the last term being exactly the Leibniz term of `Σ_j ∂_j(w_⊥ b_j)`; it therefore cancels the
identical term of `M` and **no divergence-free hypothesis is used** — the two-component mode is
not solenoidal.  What remains is

`Δ_⊥ b + (b·∇_⊥)w_⊥ = N² b + w_⊥·∇_⊥ b + iN w₃ b + λ_* b`,   `λ_* = κ² - N²`.

With `Δ_⊥ b = κ² b` (`Local/HorizontalModeSecondDerivatives.lean`) this reduces to the purely
algebraic transport-stretching cancellation

`(b·∇_⊥)w_⊥ = w_⊥·∇_⊥ b + iN w₃ b`,

which outside the disk is `0 = 0` and inside is the paper's `-i(jΩ + NU) = 0` at the
angular index `j = 1` with `NU = -Ω` (the paper writes `2π` for `N`; proof of
`lem:jump-horizontal-mode`, and the
free-`Ω` interface of `Local/PonomarenkoFreeOmegaInterface.lean`).  In Cartesian form the
cancellation is the angular-derivative identity

`(-y₂)∂_1 b + y₁ ∂_2 b = i b + (-b₂, b₁)`,

which holds because `b₁ + i b₂ = z²Φ₊(|y|²)` has angular frequency two and `b₁ - i b₂ = Φ₋(|y|²)`
has angular frequency zero.

Contents.

* The transverse screw velocity as a constant real-linear field, and its relation to the
  three-component `L∞` coefficient `horizontalModeVelocity N Ω`.
* The pointwise pivot field `D_j`, its one-sided `C¹` structure up to the unit circle, its
  one-sided boundary values and the jump `[D_j]`, and the pointwise bulk field `{∂_j D_j}`.
* The angular-derivative identity and the pointwise bulk equation on each side of the circle.
* The `L²` packaging: `bulk j : WholePlaneC2L2` and the identity
  `bulk 0 + bulk 1 = M + λ_* b`, which is `hbulk` of the assembly theorem verbatim.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace HorizontalMode

open Complex Filter MeasureTheory Metric Set Topology
open CartesianRadialRegularity
open HorizontalWeakForm
open PolarHessianCalculus
open PonomarenkoCartesianExteriorDerivative
open ComplexRadius
open PonomarenkoCartesianInteriorDerivative
open PonomarenkoOriginProfiles
open PonomarenkoFreeOmegaInterface
open ScalarSecondPartial
open WholePlaneRadialExponential

/-! ## The transverse screw velocity as a linear field -/

/-- The two scalar component maps of the transverse screw velocity `w_⊥ = Ω(-y₂, y₁)`. -/
def horizontalTransverseVelocityComponentCLM (Omega : ℝ) (a : Fin 2) : WholePlane →L[ℝ] ℂ :=
  match a with
  | 0 => -((Omega : ℂ) •
      Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)))
  | 1 => (Omega : ℂ) •
      Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))

/-- The transverse screw velocity `w_⊥ = Ω r e_θ = Ω(-y₂, y₁)` as a real-linear map of the
plane into `ℂ²`.  Being linear, it is its own differential. -/
def horizontalTransverseVelocityCLM (Omega : ℝ) : WholePlane →L[ℝ] C2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (horizontalTransverseVelocityComponentCLM Omega))

/-- First component of the linear transverse screw velocity. -/
@[simp] theorem horizontalTransverseVelocityCLM_apply_zero (Omega : ℝ) (v : WholePlane) :
    horizontalTransverseVelocityCLM Omega v 0 = -(Omega : ℂ) * (v (1 : Fin 2) : ℂ) := by
  simp [horizontalTransverseVelocityCLM, horizontalTransverseVelocityComponentCLM]

/-- Second component of the linear transverse screw velocity. -/
@[simp] theorem horizontalTransverseVelocityCLM_apply_one (Omega : ℝ) (v : WholePlane) :
    horizontalTransverseVelocityCLM Omega v 1 = (Omega : ℂ) * (v (0 : Fin 2) : ℂ) := by
  simp [horizontalTransverseVelocityCLM, horizontalTransverseVelocityComponentCLM]

/-- The interior value of the transverse screw velocity at a point of the plane. -/
def horizontalInteriorTransverseVelocity (Omega : ℝ) (y : WholePlane) : C2 :=
  horizontalTransverseVelocityCLM Omega y

/-- First component of the interior transverse screw velocity: `-Ω y₂`. -/
@[simp] theorem horizontalInteriorTransverseVelocity_apply_zero (Omega : ℝ) (y : WholePlane) :
    horizontalInteriorTransverseVelocity Omega y 0 = -(Omega : ℂ) * (y (1 : Fin 2) : ℂ) :=
  horizontalTransverseVelocityCLM_apply_zero Omega y

/-- Second component of the interior transverse screw velocity: `Ω y₁`. -/
@[simp] theorem horizontalInteriorTransverseVelocity_apply_one (Omega : ℝ) (y : WholePlane) :
    horizontalInteriorTransverseVelocity Omega y 1 = (Omega : ℂ) * (y (0 : Fin 2) : ℂ) :=
  horizontalTransverseVelocityCLM_apply_one Omega y

/-- The constant vector `∂_j w_⊥`: `(0, Ω)` for `j = 1` and `(-Ω, 0)` for `j = 2`. -/
def horizontalTransverseVelocityPartial (Omega : ℝ) (j : Fin 2) : C2 :=
  horizontalTransverseVelocityCLM Omega (wholePlaneBasis j)

/-- The glued transverse velocity: `Ω r e_θ` on the closed unit disk and zero outside, the
transverse part of the representative `horizontalJumpVelocity`. -/
def horizontalTransverseVelocityField (Omega : ℝ) (y : WholePlane) : C2 :=
  if ‖y‖ ≤ 1 then horizontalInteriorTransverseVelocity Omega y else 0

/-- On the closed unit disk the glued transverse velocity is the interior screw value. -/
@[simp] theorem horizontalTransverseVelocityField_of_norm_le
    (Omega : ℝ) {y : WholePlane} (hy : ‖y‖ ≤ 1) :
    horizontalTransverseVelocityField Omega y =
      horizontalInteriorTransverseVelocity Omega y := by
  simp [horizontalTransverseVelocityField, hy]

/-- Outside the closed unit disk the glued transverse velocity vanishes. -/
@[simp] theorem horizontalTransverseVelocityField_of_one_lt_norm
    (Omega : ℝ) {y : WholePlane} (hy : 1 < ‖y‖) :
    horizontalTransverseVelocityField Omega y = 0 := by
  simp [horizontalTransverseVelocityField, not_le_of_gt hy]

/-- The glued axial velocity: `U` on the closed unit disk and zero outside. -/
def horizontalAxialVelocityField (N Omega : ℝ) (y : WholePlane) : ℂ :=
  if ‖y‖ ≤ 1 then ((jumpAxialSpeed N Omega : ℝ) : ℂ) else 0

/-- On the closed unit disk the glued axial velocity is the constant `U`. -/
@[simp] theorem horizontalAxialVelocityField_of_norm_le
    (N Omega : ℝ) {y : WholePlane} (hy : ‖y‖ ≤ 1) :
    horizontalAxialVelocityField N Omega y = ((jumpAxialSpeed N Omega : ℝ) : ℂ) := by
  simp [horizontalAxialVelocityField, hy]

/-- Outside the closed unit disk the glued axial velocity vanishes. -/
@[simp] theorem horizontalAxialVelocityField_of_one_lt_norm
    (N Omega : ℝ) {y : WholePlane} (hy : 1 < ‖y‖) :
    horizontalAxialVelocityField N Omega y = 0 := by
  simp [horizontalAxialVelocityField, not_le_of_gt hy]

/-- First transverse component of the three-component jump representative. -/
theorem horizontalJumpVelocity_apply_zero (Omega U : ℝ) (y : WholePlane) :
    horizontalJumpVelocity Omega U y ((0 : Fin 2).castSucc) =
      horizontalTransverseVelocityField Omega y 0 := by
  by_cases hy : ‖y‖ ≤ 1
  · rw [horizontalJumpVelocity_of_norm_le Omega U hy,
      horizontalTransverseVelocityField_of_norm_le Omega hy]
    simp [horizontalJumpInteriorVelocity, horizontalInteriorTransverseVelocity]
  · rw [horizontalJumpVelocity_of_one_lt_norm Omega U (lt_of_not_ge hy),
      horizontalTransverseVelocityField_of_one_lt_norm Omega (lt_of_not_ge hy)]
    simp

/-- Second transverse component of the three-component jump representative. -/
theorem horizontalJumpVelocity_apply_one (Omega U : ℝ) (y : WholePlane) :
    horizontalJumpVelocity Omega U y ((1 : Fin 2).castSucc) =
      horizontalTransverseVelocityField Omega y 1 := by
  by_cases hy : ‖y‖ ≤ 1
  · rw [horizontalJumpVelocity_of_norm_le Omega U hy,
      horizontalTransverseVelocityField_of_norm_le Omega hy]
    simp [horizontalJumpInteriorVelocity, horizontalInteriorTransverseVelocity]
  · rw [horizontalJumpVelocity_of_one_lt_norm Omega U (lt_of_not_ge hy),
      horizontalTransverseVelocityField_of_one_lt_norm Omega (lt_of_not_ge hy)]
    simp

/-- Axial component of the three-component jump representative. -/
theorem horizontalJumpVelocity_apply_two (N Omega : ℝ) (y : WholePlane) :
    horizontalJumpVelocity Omega (jumpAxialSpeed N Omega) y (2 : Fin 3) =
      horizontalAxialVelocityField N Omega y := by
  by_cases hy : ‖y‖ ≤ 1
  · rw [horizontalJumpVelocity_of_norm_le Omega (jumpAxialSpeed N Omega) hy,
      horizontalAxialVelocityField_of_norm_le N Omega hy]
    simp [horizontalJumpInteriorVelocity]
  · rw [horizontalJumpVelocity_of_one_lt_norm Omega (jumpAxialSpeed N Omega)
      (lt_of_not_ge hy), horizontalAxialVelocityField_of_one_lt_norm N Omega (lt_of_not_ge hy)]
    simp

/-! ## Exact first Cartesian derivatives of the regular interior branch -/

/-- The first Cartesian component of the regular interior field differentiated in an arbitrary
direction, from the chain rules for `Φ₋(|y|²)` and `z²Φ₊(|y|²)`. -/
theorem fderiv_horizontalInteriorField_apply_zero (kappa : ℂ) (y v : WholePlane) :
    fderiv ℝ (fun x : WholePlane ↦ horizontalInteriorField kappa x 0) y v =
      ((((2 * inner ℝ y v : ℝ) : ℂ) * deriv (minusOriginProfile kappa) (squaredRadius y)) +
        (complexCoordinate y ^ 2 *
            (((2 * inner ℝ y v : ℝ) : ℂ) *
              deriv (plusOriginProfile kappa) (squaredRadius y)) +
          radialScalar (plusOriginProfile kappa) y *
            (2 * complexCoordinate y * complexCoordinateCLM v))) / 2 := by
  let Dminus : WholePlane →L[ℝ] ℂ :=
    (2 • innerSL ℝ y).smulRight (deriv (minusOriginProfile kappa) (squaredRadius y))
  let Dplus : WholePlane →L[ℝ] ℂ :=
    (complexCoordinate y ^ 2) •
        ((2 • innerSL ℝ y).smulRight (deriv (plusOriginProfile kappa) (squaredRadius y))) +
      (radialScalar (plusOriginProfile kappa) y) •
        ((2 • complexCoordinate y ^ (2 - 1)) • complexCoordinateCLM)
  have hm : HasFDerivAt (radialScalar (minusOriginProfile kappa)) Dminus y :=
    radialScalar_hasFDerivAt (minusOriginProfile_hasDerivAt kappa (squaredRadius y))
  have hp : HasFDerivAt (degreeTwoFactor (plusOriginProfile kappa)) Dplus y :=
    degreeTwoFactor_hasFDerivAt (plusOriginProfile_hasDerivAt kappa (squaredRadius y))
  have h := (hm.add hp).const_mul ((2 : ℂ)⁻¹)
  have hfield : HasFDerivAt
      (fun x : WholePlane ↦ horizontalInteriorField kappa x 0)
      (((2 : ℂ)⁻¹) • (Dminus + Dplus)) y := by
    apply h.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun x ↦ by
      change horizontalInteriorField kappa x 0 = _
      rw [horizontalInteriorField_apply_zero]
      simp only [Pi.add_apply]
      ring
  rw [hfield.fderiv]
  simp [Dminus, Dplus, Complex.real_smul, div_eq_mul_inv]
  ring

/-- The second Cartesian component of the regular interior field differentiated in an arbitrary
direction. -/
theorem fderiv_horizontalInteriorField_apply_one (kappa : ℂ) (y v : WholePlane) :
    fderiv ℝ (fun x : WholePlane ↦ horizontalInteriorField kappa x 1) y v =
      I *
        ((((2 * inner ℝ y v : ℝ) : ℂ) * deriv (minusOriginProfile kappa) (squaredRadius y)) -
          (complexCoordinate y ^ 2 *
              (((2 * inner ℝ y v : ℝ) : ℂ) *
                deriv (plusOriginProfile kappa) (squaredRadius y)) +
            radialScalar (plusOriginProfile kappa) y *
              (2 * complexCoordinate y * complexCoordinateCLM v))) / 2 := by
  let Dminus : WholePlane →L[ℝ] ℂ :=
    (2 • innerSL ℝ y).smulRight (deriv (minusOriginProfile kappa) (squaredRadius y))
  let Dplus : WholePlane →L[ℝ] ℂ :=
    (complexCoordinate y ^ 2) •
        ((2 • innerSL ℝ y).smulRight (deriv (plusOriginProfile kappa) (squaredRadius y))) +
      (radialScalar (plusOriginProfile kappa) y) •
        ((2 • complexCoordinate y ^ (2 - 1)) • complexCoordinateCLM)
  have hm : HasFDerivAt (radialScalar (minusOriginProfile kappa)) Dminus y :=
    radialScalar_hasFDerivAt (minusOriginProfile_hasDerivAt kappa (squaredRadius y))
  have hp : HasFDerivAt (degreeTwoFactor (plusOriginProfile kappa)) Dplus y :=
    degreeTwoFactor_hasFDerivAt (plusOriginProfile_hasDerivAt kappa (squaredRadius y))
  have h := (hm.sub hp).const_mul (I / 2)
  have hfield : HasFDerivAt
      (fun x : WholePlane ↦ horizontalInteriorField kappa x 1)
      ((I / 2) • (Dminus - Dplus)) y := by
    apply h.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun x ↦ by
      change horizontalInteriorField kappa x 1 = _
      rw [horizontalInteriorField_apply_one]
      simp only [Pi.sub_apply]
      ring
  rw [hfield.fderiv]
  simp [Dminus, Dplus, Complex.real_smul, div_eq_mul_inv]
  ring

/-- Componentwise, the packaged interior first partial is the scalar partial of the
corresponding component. -/
theorem horizontalInteriorPartialDerivative_apply
    (kappa : ℂ) (j : Fin 2) (y : WholePlane) (a : Fin 2) :
    horizontalInteriorPartialDerivative kappa j y a =
      fderiv ℝ (fun x : WholePlane ↦ horizontalInteriorField kappa x a) y
        (wholePlaneBasis j) := by
  unfold horizontalInteriorPartialDerivative
  exact (fderiv_c2_component_apply
    ((horizontalInteriorField_contDiff kappa).differentiable (by simp) y) a
    (wholePlaneBasis j)).symm

/-! ## The transport-stretching cancellation inside the disk -/

/-- Coordinates of the plane's standard basis vectors. -/
@[simp] theorem wholePlaneBasis_apply (j i : Fin 2) :
    wholePlaneBasis j i = if i = j then (1 : ℝ) else 0 := by
  simp [wholePlaneBasis]

/-- First component of the Cartesian transport-stretching cancellation
`(b·∇_⊥)w_⊥ = w_⊥·∇_⊥b - iΩ b` for the regular interior branch. -/
theorem horizontalInteriorStretch_apply_zero (Omega : ℝ) (kappa : ℂ) (y : WholePlane) :
    horizontalInteriorField kappa y 0 * horizontalTransverseVelocityPartial Omega 0 0 +
        horizontalInteriorField kappa y 1 * horizontalTransverseVelocityPartial Omega 1 0 =
      horizontalInteriorTransverseVelocity Omega y 0 *
          horizontalInteriorPartialDerivative kappa 0 y 0 +
        horizontalInteriorTransverseVelocity Omega y 1 *
          horizontalInteriorPartialDerivative kappa 1 y 0 -
        I * (Omega : ℂ) * horizontalInteriorField kappa y 0 := by
  simp only [horizontalInteriorPartialDerivative_apply,
    fderiv_horizontalInteriorField_apply_zero]
  simp only [horizontalTransverseVelocityPartial, horizontalInteriorTransverseVelocity,
    horizontalTransverseVelocityCLM_apply_zero, horizontalTransverseVelocityCLM_apply_one,
    horizontalInteriorField_apply_zero, horizontalInteriorField_apply_one,
    inner_wholePlaneBasis, complexCoordinateCLM_apply, degreeTwoFactor, complexCoordinate,
    wholePlaneBasis_apply]
  norm_num
  linear_combination
    (((y (0 : Fin 2) : ℝ) : ℂ) * ((y (1 : Fin 2) : ℝ) : ℂ) *
        radialScalar (plusOriginProfile kappa) y * ((Omega : ℝ) : ℂ) +
      I * ((y (1 : Fin 2) : ℝ) : ℂ) ^ 2 *
        radialScalar (plusOriginProfile kappa) y * ((Omega : ℝ) : ℂ)) * Complex.I_sq

/-- Second component of the Cartesian transport-stretching cancellation for the regular
interior branch. -/
theorem horizontalInteriorStretch_apply_one (Omega : ℝ) (kappa : ℂ) (y : WholePlane) :
    horizontalInteriorField kappa y 0 * horizontalTransverseVelocityPartial Omega 0 1 +
        horizontalInteriorField kappa y 1 * horizontalTransverseVelocityPartial Omega 1 1 =
      horizontalInteriorTransverseVelocity Omega y 0 *
          horizontalInteriorPartialDerivative kappa 0 y 1 +
        horizontalInteriorTransverseVelocity Omega y 1 *
          horizontalInteriorPartialDerivative kappa 1 y 1 -
        I * (Omega : ℂ) * horizontalInteriorField kappa y 1 := by
  simp only [horizontalInteriorPartialDerivative_apply,
    fderiv_horizontalInteriorField_apply_one]
  simp only [horizontalTransverseVelocityPartial, horizontalInteriorTransverseVelocity,
    horizontalTransverseVelocityCLM_apply_zero, horizontalTransverseVelocityCLM_apply_one,
    horizontalInteriorField_apply_zero, horizontalInteriorField_apply_one,
    inner_wholePlaneBasis, complexCoordinateCLM_apply, degreeTwoFactor, complexCoordinate,
    wholePlaneBasis_apply]
  norm_num
  linear_combination
    ((radialScalar (minusOriginProfile kappa) y * ((Omega : ℝ) : ℂ) +
        ((y (0 : Fin 2) : ℝ) : ℂ) ^ 2 * radialScalar (plusOriginProfile kappa) y *
          ((Omega : ℝ) : ℂ) -
        I ^ 2 * ((y (1 : Fin 2) : ℝ) : ℂ) ^ 2 * radialScalar (plusOriginProfile kappa) y *
          ((Omega : ℝ) : ℂ)) / 2) * Complex.I_sq

/-- The Cartesian transport-stretching cancellation for the regular interior branch:

`(b·∇_⊥)w_⊥ = w_⊥·∇_⊥b - iΩ b`,

the paper's `-i(jΩ + NU) = 0` at `j = 1` with `NU = -Ω`
(proof of `lem:jump-horizontal-mode`).  It holds at every point of the plane, the polar axis
included, because the regular branch is smooth there. -/
theorem horizontalInteriorStretch_eq (Omega : ℝ) (kappa : ℂ) (y : WholePlane) :
    (∑ j : Fin 2, horizontalInteriorField kappa y j •
        horizontalTransverseVelocityPartial Omega j) =
      (∑ j : Fin 2, horizontalInteriorTransverseVelocity Omega y j •
          horizontalInteriorPartialDerivative kappa j y) -
        (I * (Omega : ℂ)) • horizontalInteriorField kappa y := by
  have h0 : (∑ j : Fin 2, horizontalInteriorField kappa y j •
        horizontalTransverseVelocityPartial Omega j) 0 =
      ((∑ j : Fin 2, horizontalInteriorTransverseVelocity Omega y j •
          horizontalInteriorPartialDerivative kappa j y) -
        (I * (Omega : ℂ)) • horizontalInteriorField kappa y) 0 := by
    simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, mul_assoc] using horizontalInteriorStretch_apply_zero Omega kappa y
  have h1 : (∑ j : Fin 2, horizontalInteriorField kappa y j •
        horizontalTransverseVelocityPartial Omega j) 1 =
      ((∑ j : Fin 2, horizontalInteriorTransverseVelocity Omega y j •
          horizontalInteriorPartialDerivative kappa j y) -
        (I * (Omega : ℂ)) • horizontalInteriorField kappa y) 1 := by
    simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, mul_assoc] using horizontalInteriorStretch_apply_one Omega kappa y
  apply PiLp.ext
  intro a
  fin_cases a
  · exact h0
  · exact h1

/-! ## The pivot field `D_j` and its branchwise derivative -/

/-- The interior branch of the pivot field `D_j = ∂_j b + b_j w_⊥`, written with the
*unrestricted* polynomial screw velocity.  It is smooth on the whole plane and agrees with the
glued pivot field on the closed unit disk. -/
def horizontalInteriorPivotField (Omega : ℝ) (kappa : ℂ) (j : Fin 2) (y : WholePlane) : C2 :=
  horizontalInteriorPartialDerivative kappa j y +
    horizontalInteriorField kappa y j • horizontalInteriorTransverseVelocity Omega y

/-- The exterior branch of the pivot field.  The velocity vanishes outside the disk, so
`D_j = ∂_j b` there. -/
def horizontalExteriorPivotField (kappa : ℂ) (j : Fin 2) (y : WholePlane) : C2 :=
  horizontalExteriorPartialDerivative kappa j y

/-- The glued pivot field `D_j = ∂_j b + w_⊥ b_j` of `HorizontalModeWeakIdentity`, pointwise. -/
def horizontalModePivotField (Omega : ℝ) (kappa : ℂ) (j : Fin 2) (y : WholePlane) : C2 :=
  horizontalModePartialDerivative kappa j y +
    horizontalModeField kappa y j • horizontalTransverseVelocityField Omega y

/-- On the closed unit disk the glued pivot field is its interior branch. -/
@[simp] theorem horizontalModePivotField_of_norm_le
    (Omega : ℝ) (kappa : ℂ) (j : Fin 2) {y : WholePlane} (hy : ‖y‖ ≤ 1) :
    horizontalModePivotField Omega kappa j y =
      horizontalInteriorPivotField Omega kappa j y := by
  simp [horizontalModePivotField, horizontalInteriorPivotField, hy]

/-- Outside the closed unit disk the glued pivot field is its exterior branch. -/
@[simp] theorem horizontalModePivotField_of_one_lt_norm
    (Omega : ℝ) (kappa : ℂ) (j : Fin 2) {y : WholePlane} (hy : 1 < ‖y‖) :
    horizontalModePivotField Omega kappa j y = horizontalExteriorPivotField kappa j y := by
  simp [horizontalModePivotField, horizontalExteriorPivotField, hy]

/-! ## The branchwise bulk field `{∂_j D_j}` -/

/-- The interior bulk field `∂_j D_j = ∂_j∂_j b + (∂_j b)_j w_⊥ + b_j ∂_j w_⊥`. -/
def horizontalInteriorBulkField (Omega : ℝ) (kappa : ℂ) (j : Fin 2) (y : WholePlane) : C2 :=
  horizontalInteriorSecondPartialDerivative kappa j j y +
    horizontalInteriorPartialDerivative kappa j y j •
      horizontalInteriorTransverseVelocity Omega y +
    horizontalInteriorField kappa y j • horizontalTransverseVelocityPartial Omega j

/-- The exterior bulk field `∂_j D_j = ∂_j∂_j b`. -/
def horizontalExteriorBulkField (kappa : ℂ) (j : Fin 2) (y : WholePlane) : C2 :=
  horizontalExteriorSecondPartialDerivative kappa j j y

/-- The glued bulk field `{∂_j D_j}`, the pointwise derivative of the pivot field off the unit
circle (a set of measure zero, where the value chosen below is irrelevant). -/
def horizontalModeBulkField (Omega : ℝ) (kappa : ℂ) (j : Fin 2) (y : WholePlane) : C2 :=
  if ‖y‖ ≤ 1 then horizontalInteriorBulkField Omega kappa j y
  else horizontalExteriorBulkField kappa j y

/-- On the closed unit disk the glued bulk field is its interior branch. -/
@[simp] theorem horizontalModeBulkField_of_norm_le
    (Omega : ℝ) (kappa : ℂ) (j : Fin 2) {y : WholePlane} (hy : ‖y‖ ≤ 1) :
    horizontalModeBulkField Omega kappa j y = horizontalInteriorBulkField Omega kappa j y := by
  simp [horizontalModeBulkField, hy]

/-- Outside the closed unit disk the glued bulk field is its exterior branch. -/
@[simp] theorem horizontalModeBulkField_of_one_lt_norm
    (Omega : ℝ) (kappa : ℂ) (j : Fin 2) {y : WholePlane} (hy : 1 < ‖y‖) :
    horizontalModeBulkField Omega kappa j y = horizontalExteriorBulkField kappa j y := by
  simp [horizontalModeBulkField, not_le_of_gt hy]

/-- The interior pivot field is Fréchet differentiable at every point of the plane. -/
theorem horizontalInteriorPivotField_hasFDerivAt
    (Omega : ℝ) (kappa : ℂ) (j : Fin 2) (y : WholePlane) :
    HasFDerivAt (horizontalInteriorPivotField Omega kappa j)
      (fderiv ℝ (horizontalInteriorPartialDerivative kappa j) y +
        (horizontalInteriorField kappa y j • horizontalTransverseVelocityCLM Omega +
          ((c2ComponentProjection j).comp
              (fderiv ℝ (horizontalInteriorField kappa) y)).smulRight
            (horizontalInteriorTransverseVelocity Omega y))) y := by
  have hb := horizontalInteriorPartialDerivative_hasFDerivAt kappa j y
  have hfield : HasFDerivAt (horizontalInteriorField kappa)
      (fderiv ℝ (horizontalInteriorField kappa) y) y :=
    ((horizontalInteriorField_contDiff kappa).differentiable (by simp) y).hasFDerivAt
  have hcomp := hasFDerivAt_c2_component hfield j
  have hw : HasFDerivAt (horizontalInteriorTransverseVelocity Omega)
      (horizontalTransverseVelocityCLM Omega) y :=
    (horizontalTransverseVelocityCLM Omega).hasFDerivAt
  exact hb.add (hcomp.smul hw)

/-- The interior pivot field is differentiable on the whole plane. -/
theorem horizontalInteriorPivotField_differentiable (Omega : ℝ) (kappa : ℂ) (j : Fin 2) :
    Differentiable ℝ (horizontalInteriorPivotField Omega kappa j) :=
  fun y ↦ (horizontalInteriorPivotField_hasFDerivAt Omega kappa j y).differentiableAt

/-- The interior pivot field is continuous on the whole plane; in particular it has a
one-sided trace on the unit circle from inside. -/
theorem horizontalInteriorPivotField_continuous (Omega : ℝ) (kappa : ℂ) (j : Fin 2) :
    Continuous (horizontalInteriorPivotField Omega kappa j) :=
  (horizontalInteriorPivotField_differentiable Omega kappa j).continuous

/-- The `k`-th Cartesian derivative of the interior pivot field, by the Leibniz rule. -/
theorem fderiv_horizontalInteriorPivotField_basis
    (Omega : ℝ) (kappa : ℂ) (j k : Fin 2) (y : WholePlane) :
    fderiv ℝ (horizontalInteriorPivotField Omega kappa j) y (wholePlaneBasis k) =
      horizontalInteriorSecondPartialDerivative kappa j k y +
        horizontalInteriorPartialDerivative kappa k y j •
          horizontalInteriorTransverseVelocity Omega y +
        horizontalInteriorField kappa y j • horizontalTransverseVelocityPartial Omega k := by
  rw [(horizontalInteriorPivotField_hasFDerivAt Omega kappa j y).fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, c2ComponentProjection_comp_apply,
    horizontalInteriorSecondPartialDerivative, horizontalTransverseVelocityPartial,
    horizontalInteriorPartialDerivative]
  abel

/-- The `j`-th Cartesian derivative of the interior pivot field is the interior bulk field:
`∂_j D_j = {∂_j D_j}` inside the disk. -/
theorem fderiv_horizontalInteriorPivotField_self
    (Omega : ℝ) (kappa : ℂ) (j : Fin 2) (y : WholePlane) :
    fderiv ℝ (horizontalInteriorPivotField Omega kappa j) y (wholePlaneBasis j) =
      horizontalInteriorBulkField Omega kappa j y :=
  fderiv_horizontalInteriorPivotField_basis Omega kappa j j y

/-- Away from the origin the exterior pivot field is Fréchet differentiable. -/
theorem horizontalExteriorPivotField_hasFDerivAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j : Fin 2) :
    HasFDerivAt (horizontalExteriorPivotField kappa j)
      (fderiv ℝ (horizontalExteriorPivotField kappa j) y) y :=
  horizontalExteriorPartialDerivative_hasFDerivAt hkappa hy j

/-- Away from the origin the exterior pivot field is differentiable. -/
theorem horizontalExteriorPivotField_differentiableAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j : Fin 2) :
    DifferentiableAt ℝ (horizontalExteriorPivotField kappa j) y :=
  (horizontalExteriorPivotField_hasFDerivAt hkappa hy j).differentiableAt

/-- Away from the origin the exterior pivot field is continuous; in particular it has a
one-sided trace on the unit circle from outside. -/
theorem horizontalExteriorPivotField_continuousAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j : Fin 2) :
    ContinuousAt (horizontalExteriorPivotField kappa j) y :=
  (horizontalExteriorPivotField_differentiableAt hkappa hy j).continuousAt

/-- The `j`-th Cartesian derivative of the exterior pivot field is the exterior bulk field. -/
theorem fderiv_horizontalExteriorPivotField_self
    (kappa : ℂ) (j : Fin 2) (y : WholePlane) :
    fderiv ℝ (horizontalExteriorPivotField kappa j) y (wholePlaneBasis j) =
      horizontalExteriorBulkField kappa j y :=
  rfl

/-! ## The pointwise mass field and the bulk equation -/

/-- The pointwise transverse divergence `Div_⊥ b = Σ_j ∂_j b_j` of the glued mode.  It is
*not* zero: the two-component mode is not solenoidal, and nothing below assumes it is. -/
def horizontalModeDivergenceField (kappa : ℂ) (y : WholePlane) : ℂ :=
  ∑ j : Fin 2, horizontalModePartialDerivative kappa j y j

/-- The pointwise mass field `M = N²b + w_⊥·∇_⊥b + iN w₃ b + w_⊥(Div_⊥ b)`, the pointwise
counterpart of `horizontalWeakFormMassPivot`. -/
def horizontalModeMassField (N Omega : ℝ) (kappa : ℂ) (y : WholePlane) : C2 :=
  ((N : ℂ) ^ 2) • horizontalModeField kappa y +
      (∑ j : Fin 2, horizontalTransverseVelocityField Omega y j •
        horizontalModePartialDerivative kappa j y) +
      (I * (N : ℂ)) •
        (horizontalAxialVelocityField N Omega y • horizontalModeField kappa y) +
    horizontalModeDivergenceField kappa y • horizontalTransverseVelocityField Omega y

/-- The helical cancellation `iN U = -iΩ` acting on any `ℂ²` vector, from `NU = -Ω`
(proof of `lem:jump-horizontal-mode`). -/
theorem horizontalAxialStretch_cancel {N : ℝ} (Omega : ℝ) (hN : N ≠ 0) (v : C2) :
    (I * (N : ℂ)) • (((jumpAxialSpeed N Omega : ℝ) : ℂ) • v) = (-(I * (Omega : ℂ))) • v := by
  rw [smul_smul]
  congr 1
  have h : ((N : ℝ) : ℂ) * ((jumpAxialSpeed N Omega : ℝ) : ℂ) = ((-Omega : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, scale_mul_jumpAxialSpeed hN]
  rw [mul_assoc, h]
  push_cast
  ring

/-- The pointwise bulk equation inside the unit disk:

`Σ_j ∂_j D_j = M + λ_* b`,  `λ_* = κ² - N²`.

The `w_⊥(Div_⊥ b)` term of `M` is exactly the Leibniz term of `Σ_j ∂_j(w_⊥ b_j)` and cancels;
what remains is `Δ_⊥ b = κ² b` together with the transport-stretching cancellation. -/
theorem horizontalModeBulkField_add_of_norm_le
    {N Omega : ℝ} (hN : N ≠ 0) {kappa : ℂ} (hkappa : kappa ≠ 0)
    {y : WholePlane} (hy : ‖y‖ ≤ 1) :
    horizontalModeBulkField Omega kappa 0 y + horizontalModeBulkField Omega kappa 1 y =
      horizontalModeMassField N Omega kappa y +
        horizontalEigenvalue N kappa • horizontalModeField kappa y := by
  have hlap := horizontalInteriorLaplacian_eq hkappa y
  rw [horizontalInteriorLaplacian, Fin.sum_univ_two] at hlap
  have hstretch := horizontalInteriorStretch_eq Omega kappa y
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hstretch
  have hU := horizontalAxialStretch_cancel (N := N) Omega hN (horizontalInteriorField kappa y)
  rw [horizontalModeBulkField_of_norm_le _ _ _ hy, horizontalModeBulkField_of_norm_le _ _ _ hy,
    horizontalEigenvalue_eq_ponomarenkoLocalEigenvalue, ponomarenkoLocalEigenvalue_apply,
    sub_smul]
  simp only [horizontalInteriorBulkField, horizontalModeMassField,
    horizontalModeDivergenceField, horizontalModeField_of_norm_le kappa hy,
    horizontalModePartialDerivative_of_norm_le kappa 0 hy,
    horizontalModePartialDerivative_of_norm_le kappa 1 hy,
    horizontalTransverseVelocityField_of_norm_le Omega hy,
    horizontalAxialVelocityField_of_norm_le N Omega hy, Fin.sum_univ_two]
  linear_combination (norm := module) hlap + hstretch - hU

/-- The pointwise bulk equation outside the closed unit disk, where the velocity vanishes and
the identity is exactly `Δ_⊥ b = κ² b`. -/
theorem horizontalModeBulkField_add_of_one_lt_norm
    (N Omega : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re)
    {y : WholePlane} (hy : 1 < ‖y‖) :
    horizontalModeBulkField Omega kappa 0 y + horizontalModeBulkField Omega kappa 1 y =
      horizontalModeMassField N Omega kappa y +
        horizontalEigenvalue N kappa • horizontalModeField kappa y := by
  have hy0 : y ≠ 0 := by
    intro hzero
    rw [hzero] at hy
    norm_num at hy
  have hlap := horizontalExteriorLaplacian_eq hkappa hy0
  rw [horizontalExteriorLaplacian, Fin.sum_univ_two] at hlap
  rw [horizontalModeBulkField_of_one_lt_norm _ _ _ hy,
    horizontalModeBulkField_of_one_lt_norm _ _ _ hy,
    horizontalEigenvalue_eq_ponomarenkoLocalEigenvalue, ponomarenkoLocalEigenvalue_apply,
    sub_smul]
  simp only [horizontalExteriorBulkField, horizontalModeMassField,
    horizontalModeField_of_one_lt_norm kappa hy,
    horizontalTransverseVelocityField_of_one_lt_norm Omega hy,
    horizontalAxialVelocityField_of_one_lt_norm N Omega hy, Fin.sum_univ_two,
    PiLp.zero_apply]
  linear_combination (norm := module) hlap

/-- The pointwise bulk equation off the unit circle, the two branches combined. -/
theorem horizontalModeBulkField_add
    {N Omega : ℝ} (hN : N ≠ 0) {kappa : ℂ} (hkappa : 0 < kappa.re)
    {y : WholePlane} (hy : ‖y‖ ≠ 1) :
    horizontalModeBulkField Omega kappa 0 y + horizontalModeBulkField Omega kappa 1 y =
      horizontalModeMassField N Omega kappa y +
        horizontalEigenvalue N kappa • horizontalModeField kappa y := by
  have hkne : kappa ≠ 0 := by
    intro hzero
    rw [hzero] at hkappa
    simp at hkappa
  rcases lt_or_gt_of_ne hy with h | h
  · exact horizontalModeBulkField_add_of_norm_le hN hkne h.le
  · exact horizontalModeBulkField_add_of_one_lt_norm N Omega hkappa h

end HorizontalMode
end FastDynamo
