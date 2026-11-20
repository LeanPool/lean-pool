/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.HorizontalModeSecondDerivatives
public import LeanPool.FastDynamo.Local.PonomarenkoExteriorSecondPartialBounds

/-!
# Second Cartesian derivatives of the two-component Ponomarenko mode: the exterior branch

This module continues `Local/HorizontalModeSecondDerivatives.lean` with the decaying branch of
the mode `b` of `lem:jump-horizontal-mode` (`eq:bessel-solutions` and the last paragraph of
its proof).  Outside the unit circle the mode is

`b₁ + i b₂ = q² B₊(r)`,  `b₁ - i b₂ = B₋(r)`,  `q = z/r`,

with `B₊` built from `K₂` and `B₋` from `K₀`.  The exterior branch is singular at the polar
axis, so every statement carries `y ≠ 0`; that is harmless because the branch is used only on
`1 < ‖y‖`.

Contents.

* The exterior field written as the two angular modes `B₋(r)` and `q²B₊(r)`, and its
  smoothness of every order on the punctured plane and on the open unit exterior.
* The ordered second Cartesian partials, their identification with the explicit polar model
  built from the scalar polar Hessian values of `PonomarenkoExteriorSecondPartialBounds`, and the
  proof that the model does not depend on the first-derivative packaging.
* The transverse Helmholtz equation `Δ_⊥ b_out = κ² b_out` off the polar axis, the same
  equation as inside (the radial equations in the proof of `lem:jump-horizontal-mode`).
* Exponential decay of every second partial at rate `Re κ`, hence `L²` membership outside the
  unit disk.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace HorizontalMode

open Complex Filter MeasureTheory Metric Set Topology
open CartesianRadialRegularity
open PolarHessianCalculus
open PonomarenkoCartesianExteriorDerivative
open PonomarenkoExteriorSecondPartialBounds
open ComplexRadius
open PonomarenkoCartesianPolarLaplacian
open ScalarSecondPartial
open PonomarenkoCrossNormalizedJump
open WholePlaneRadialExponential

/-! ## The decaying exterior branch as a pair of angular modes -/

/-- The first Cartesian component of the decaying exterior field is the combination
`½B₋(r) + ½q²B₊(r)` of the two exterior angular modes, at every point of the plane. -/
theorem horizontalExteriorField_apply_zero_eq_modes (kappa : ℂ) :
    (fun x : WholePlane ↦ horizontalExteriorField kappa x 0) =
      fun x : WholePlane ↦
        (1 / 2 : ℂ) * radialMode (minusOutsideReal kappa) x +
          (1 / 2 : ℂ) * phaseSqRadialMode (plusOutsideReal kappa) x := by
  funext x
  simp only [horizontalExteriorField_apply_zero, radialMode, phaseSqRadialMode,
    minusOutsideReal, plusOutsideReal, complexRadius]
  ring

/-- The second Cartesian component of the decaying exterior field is the combination
`(i/2)B₋(r) - (i/2)q²B₊(r)` of the two exterior angular modes. -/
theorem horizontalExteriorField_apply_one_eq_modes (kappa : ℂ) :
    (fun x : WholePlane ↦ horizontalExteriorField kappa x 1) =
      fun x : WholePlane ↦
        (I / 2 : ℂ) * radialMode (minusOutsideReal kappa) x +
          (-I / 2 : ℂ) * phaseSqRadialMode (plusOutsideReal kappa) x := by
  funext x
  simp only [horizontalExteriorField_apply_one, radialMode, phaseSqRadialMode,
    minusOutsideReal, plusOutsideReal, complexRadius]
  ring

/-- The radial part of the exterior field is smooth of every order at each nonzero point. -/
theorem horizontalExteriorMinusMode_contDiffAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (radialMode (minusOutsideReal kappa)) y :=
  radialMode_contDiffAt_infty hy
    (horizontalMinusOutside_analyticAt
      (horizontalExteriorArgument_re_pos hkappa (norm_pos_iff.mpr hy)))

/-- The angular-frequency-two part of the exterior field is smooth of every order at each
nonzero point. -/
theorem horizontalExteriorPlusMode_contDiffAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (phaseSqRadialMode (plusOutsideReal kappa)) y :=
  phaseSqRadialMode_contDiffAt_infty hy
    (horizontalPlusOutside_analyticAt
      (horizontalExteriorArgument_re_pos hkappa (norm_pos_iff.mpr hy)))

/-- The first Cartesian component of the exterior field is smooth at every nonzero point. -/
theorem horizontalExteriorField_apply_zero_contDiffAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x : WholePlane ↦ horizontalExteriorField kappa x 0) y := by
  rw [horizontalExteriorField_apply_zero_eq_modes]
  exact (contDiffAt_const.mul (horizontalExteriorMinusMode_contDiffAt hkappa hy)).add
    (contDiffAt_const.mul (horizontalExteriorPlusMode_contDiffAt hkappa hy))

/-- The second Cartesian component of the exterior field is smooth at every nonzero point. -/
theorem horizontalExteriorField_apply_one_contDiffAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x : WholePlane ↦ horizontalExteriorField kappa x 1) y := by
  rw [horizontalExteriorField_apply_one_eq_modes]
  exact (contDiffAt_const.mul (horizontalExteriorMinusMode_contDiffAt hkappa hy)).add
    (contDiffAt_const.mul (horizontalExteriorPlusMode_contDiffAt hkappa hy))

/-- The decaying exterior two-component field is smooth at every nonzero point. -/
theorem horizontalExteriorField_contDiffAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (horizontalExteriorField kappa) y := by
  apply (contDiffAt_piLp 2).2
  intro a
  fin_cases a
  · exact horizontalExteriorField_apply_zero_contDiffAt hkappa hy
  · exact horizontalExteriorField_apply_one_contDiffAt hkappa hy

/-! ## Second Cartesian derivatives of the decaying exterior branch -/

/-- Near every nonzero point, the packaged exterior first partial is exactly the Fréchet
derivative of the exterior field in the corresponding coordinate direction. -/
theorem horizontalExteriorPartialDerivative_eventuallyEq_fderiv
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j : Fin 2) :
    horizontalExteriorPartialDerivative kappa j =ᶠ[nhds y]
      fun x : WholePlane ↦
        fderiv ℝ (horizontalExteriorField kappa) x (wholePlaneBasis j) := by
  have hy' : y ∈ ({0} : Set WholePlane)ᶜ := by simpa using hy
  filter_upwards [isOpen_compl_singleton.mem_nhds hy'] with x hx
  exact horizontalExteriorPartialDerivative_eq_fderiv hkappa (by simpa using hx) j

/-- Each packaged exterior first partial is itself smooth at every nonzero point. -/
theorem horizontalExteriorPartialDerivative_contDiffAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j : Fin 2) :
    ContDiffAt ℝ (⊤ : ℕ∞) (horizontalExteriorPartialDerivative kappa j) y := by
  have hfderiv : ContDiffAt ℝ (⊤ : ℕ∞)
      (fderiv ℝ (horizontalExteriorField kappa)) y :=
    (horizontalExteriorField_contDiffAt hkappa hy).fderiv_right (by simp)
  exact (hfderiv.clm_apply contDiffAt_const).congr_of_eventuallyEq
    (horizontalExteriorPartialDerivative_eventuallyEq_fderiv hkappa hy j)

/-- The ordered second Cartesian partial `∂_k∂_j b_out` of the decaying exterior field.  It is
totalized by Mathlib's `fderiv`, but every statement below uses it only where `y ≠ 0`. -/
def horizontalExteriorSecondPartialDerivative
    (kappa : ℂ) (j k : Fin 2) (y : WholePlane) : C2 :=
  fderiv ℝ (horizontalExteriorPartialDerivative kappa j) y (wholePlaneBasis k)

/-- At every nonzero point the packaged exterior first partial has a Fréchet
derivative, so the previous definition is a classical second partial. -/
theorem horizontalExteriorPartialDerivative_hasFDerivAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j : Fin 2) :
    HasFDerivAt (horizontalExteriorPartialDerivative kappa j)
      (fderiv ℝ (horizontalExteriorPartialDerivative kappa j) y) y :=
  ((horizontalExteriorPartialDerivative_contDiffAt hkappa hy j).differentiableAt
    (by simp)).hasFDerivAt

/-- The ordered exterior second partial agrees with differentiating the Fréchet derivative of
the field itself, so it does not depend on the explicit first-derivative packaging. -/
theorem horizontalExteriorSecondPartialDerivative_eq_field_fderiv
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j k : Fin 2) :
    horizontalExteriorSecondPartialDerivative kappa j k y =
      fderiv ℝ
        (fun x : WholePlane ↦
          fderiv ℝ (horizontalExteriorField kappa) x (wholePlaneBasis j)) y
        (wholePlaneBasis k) := by
  unfold horizontalExteriorSecondPartialDerivative
  rw [(horizontalExteriorPartialDerivative_eventuallyEq_fderiv hkappa hy j).fderiv_eq]

/-- Componentwise, the exterior second Cartesian partial is the scalar second partial of the
corresponding component. -/
theorem horizontalExteriorSecondPartialDerivative_apply
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j k : Fin 2)
    (a : Fin 2) :
    horizontalExteriorSecondPartialDerivative kappa j k y a =
      scalarSecondPartial (fun x : WholePlane ↦ horizontalExteriorField kappa x a) j k y := by
  rw [horizontalExteriorSecondPartialDerivative_eq_field_fderiv hkappa hy]
  exact c2SecondPartial_apply_eq_scalarSecondPartial
    ((horizontalExteriorField_contDiffAt hkappa hy).of_le horizontalTwo_le_top) j k a

/-- The polar model for the ordered second partials of the two-component exterior field, built
from the two scalar polar Hessian values of `Local/PonomarenkoExteriorSecondPartialBounds.lean`. -/
def horizontalExteriorSecondPartialModel
    (kappa : ℂ) (j k : Fin 2) (y : WholePlane) : C2 :=
  WithLp.toLp 2 ![
    (exteriorMinusSecondPartialValue kappa y j k +
      exteriorPlusSecondPartialValue kappa y j k) / 2,
    I * (exteriorMinusSecondPartialValue kappa y j k -
      exteriorPlusSecondPartialValue kappa y j k) / 2]

/-- First component of the exterior polar second-partial model. -/
@[simp] theorem horizontalExteriorSecondPartialModel_apply_zero
    (kappa : ℂ) (j k : Fin 2) (y : WholePlane) :
    horizontalExteriorSecondPartialModel kappa j k y 0 =
      (exteriorMinusSecondPartialValue kappa y j k +
        exteriorPlusSecondPartialValue kappa y j k) / 2 := by
  simp [horizontalExteriorSecondPartialModel]

/-- Second component of the exterior polar second-partial model. -/
@[simp] theorem horizontalExteriorSecondPartialModel_apply_one
    (kappa : ℂ) (j k : Fin 2) (y : WholePlane) :
    horizontalExteriorSecondPartialModel kappa j k y 1 =
      I * (exteriorMinusSecondPartialValue kappa y j k -
        exteriorPlusSecondPartialValue kappa y j k) / 2 := by
  simp [horizontalExteriorSecondPartialModel]

/-- The two explicit polar Hessian values for an angular-frequency-two radial product agree:
`PolarHessianCalculus` and `PonomarenkoExteriorSecondPartialBounds` group the same five terms
differently. -/
theorem phaseSqRadialModeSecondPartialValue_eq
    (b b' b'' : ℂ) (y : WholePlane) (j k : Fin 2) :
    phaseSqRadialModeSecondPartialValue b b' b'' y j k =
      phaseSquaredRadialSecondPartialValue b b' b'' y j k := by
  simp only [phaseSqRadialModeSecondPartialValue,
    phaseSquareRadialProductSecondPartialValue, phaseSquaredRadialSecondPartialValue,
    exteriorPhaseSquareSecondPartial, radialCompositionPartialValue, Complex.real_smul]
  ring

/-- The scalar second partial of the radial exterior mode is the polar `B₋` Hessian value. -/
theorem scalarSecondPartial_minusOutside
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j k : Fin 2) :
    scalarSecondPartial (radialMode (minusOutsideReal kappa)) j k y =
      exteriorMinusSecondPartialValue kappa y j k :=
  scalarSecondPartial_radialMode
    (fun _ hr ↦ horizontalMinusOutsideReal_hasDerivAt_self hkappa hr)
    (fun _ hr ↦ horizontalMinusOutsideReal_deriv_hasDerivAt_self hkappa hr) hy j k

/-- The scalar second partial of the angular-frequency-two exterior mode is the polar `B₊`
Hessian value. -/
theorem scalarSecondPartial_plusOutside
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j k : Fin 2) :
    scalarSecondPartial (phaseSqRadialMode (plusOutsideReal kappa)) j k y =
      exteriorPlusSecondPartialValue kappa y j k := by
  rw [scalarSecondPartial_phaseSqRadialMode
    (fun _ hr ↦ horizontalPlusOutsideReal_hasDerivAt_self hkappa hr)
    (fun _ hr ↦ horizontalPlusOutsideReal_deriv_hasDerivAt_self hkappa hr) hy j k]
  exact phaseSqRadialModeSecondPartialValue_eq _ _ _ y j k

/-- First component of the exterior second partial against the polar model. -/
theorem horizontalExteriorSecondPartialDerivative_apply_zero_eq_model
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j k : Fin 2) :
    horizontalExteriorSecondPartialDerivative kappa j k y 0 =
      horizontalExteriorSecondPartialModel kappa j k y 0 := by
  have hm := (horizontalExteriorMinusMode_contDiffAt hkappa hy).of_le horizontalTwo_le_top
  have hp := (horizontalExteriorPlusMode_contDiffAt hkappa hy).of_le horizontalTwo_le_top
  rw [horizontalExteriorSecondPartialDerivative_apply hkappa hy,
    horizontalExteriorField_apply_zero_eq_modes,
    scalarSecondPartial_linearCombination hm hp,
    scalarSecondPartial_minusOutside hkappa hy, scalarSecondPartial_plusOutside hkappa hy,
    horizontalExteriorSecondPartialModel_apply_zero]
  ring

/-- Second component of the exterior second partial against the polar model. -/
theorem horizontalExteriorSecondPartialDerivative_apply_one_eq_model
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j k : Fin 2) :
    horizontalExteriorSecondPartialDerivative kappa j k y 1 =
      horizontalExteriorSecondPartialModel kappa j k y 1 := by
  have hm := (horizontalExteriorMinusMode_contDiffAt hkappa hy).of_le horizontalTwo_le_top
  have hp := (horizontalExteriorPlusMode_contDiffAt hkappa hy).of_le horizontalTwo_le_top
  rw [horizontalExteriorSecondPartialDerivative_apply hkappa hy,
    horizontalExteriorField_apply_one_eq_modes,
    scalarSecondPartial_linearCombination hm hp,
    scalarSecondPartial_minusOutside hkappa hy, scalarSecondPartial_plusOutside hkappa hy,
    horizontalExteriorSecondPartialModel_apply_one]
  ring

/-- Away from the origin, the ordered second Cartesian partial of the exterior field is the
explicit polar model. -/
theorem horizontalExteriorSecondPartialDerivative_eq_model
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j k : Fin 2) :
    horizontalExteriorSecondPartialDerivative kappa j k y =
      horizontalExteriorSecondPartialModel kappa j k y := by
  apply PiLp.ext
  intro a
  fin_cases a
  · exact horizontalExteriorSecondPartialDerivative_apply_zero_eq_model hkappa hy j k
  · exact horizontalExteriorSecondPartialDerivative_apply_one_eq_model hkappa hy j k

/-! ## The exterior transverse Helmholtz equation -/

/-- The transverse Cartesian Laplacian of the decaying exterior branch. -/
def horizontalExteriorLaplacian (kappa : ℂ) (y : WholePlane) : C2 :=
  ∑ j : Fin 2, horizontalExteriorSecondPartialDerivative kappa j j y

/-- Componentwise, the exterior Laplacian is the scalar Cartesian Laplacian of the
corresponding component. -/
theorem horizontalExteriorLaplacian_apply
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (a : Fin 2) :
    horizontalExteriorLaplacian kappa y a =
      scalarCartesianLaplacian
        (fun x : WholePlane ↦ horizontalExteriorField kappa x a) y := by
  simp only [horizontalExteriorLaplacian, Fin.sum_univ_two, PiLp.add_apply,
    horizontalExteriorSecondPartialDerivative_apply hkappa hy, scalarCartesianLaplacian]

/-- Away from the origin, the first Cartesian component of the decaying exterior branch
satisfies `Δ_⊥ b₁ = κ² b₁`. -/
theorem horizontalExteriorLaplacian_apply_zero_eq
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) :
    horizontalExteriorLaplacian kappa y 0 = kappa ^ 2 * horizontalExteriorField kappa y 0 := by
  have hr : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hm := (horizontalExteriorMinusMode_contDiffAt hkappa hy).of_le horizontalTwo_le_top
  have hp := (horizontalExteriorPlusMode_contDiffAt hkappa hy).of_le horizontalTwo_le_top
  have hmLap : scalarCartesianLaplacian (radialMode (minusOutsideReal kappa)) y =
      kappa ^ 2 * minusOutsideReal kappa ‖y‖ := by
    rw [scalarCartesianLaplacian_radialMode_eq_polar
      (fun _ hs ↦ horizontalMinusOutsideReal_hasDerivAt_self hkappa hs)
      (fun _ hs ↦ horizontalMinusOutsideReal_deriv_hasDerivAt_self hkappa hs) hy,
      horizontalMinusOutsideReal_polar hkappa hr]
  have hpLap : scalarCartesianLaplacian (phaseSqRadialMode (plusOutsideReal kappa)) y =
      exteriorPhase y ^ 2 * (kappa ^ 2 * plusOutsideReal kappa ‖y‖) := by
    rw [scalarCartesianLaplacian_phaseSqRadialMode_eq_polar
      (fun _ hs ↦ horizontalPlusOutsideReal_hasDerivAt_self hkappa hs)
      (fun _ hs ↦ horizontalPlusOutsideReal_deriv_hasDerivAt_self hkappa hs) hy,
      horizontalPlusOutsideReal_polar hkappa hr]
  have hfield := congrFun (horizontalExteriorField_apply_zero_eq_modes kappa) y
  rw [horizontalExteriorLaplacian_apply hkappa hy,
    horizontalExteriorField_apply_zero_eq_modes,
    scalarCartesianLaplacian_linearCombination hm hp, hmLap, hpLap, hfield]
  simp only [radialMode, phaseSqRadialMode]
  ring

/-- Away from the origin, the second Cartesian component of the decaying exterior branch
satisfies `Δ_⊥ b₂ = κ² b₂`. -/
theorem horizontalExteriorLaplacian_apply_one_eq
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) :
    horizontalExteriorLaplacian kappa y 1 = kappa ^ 2 * horizontalExteriorField kappa y 1 := by
  have hr : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hm := (horizontalExteriorMinusMode_contDiffAt hkappa hy).of_le horizontalTwo_le_top
  have hp := (horizontalExteriorPlusMode_contDiffAt hkappa hy).of_le horizontalTwo_le_top
  have hmLap : scalarCartesianLaplacian (radialMode (minusOutsideReal kappa)) y =
      kappa ^ 2 * minusOutsideReal kappa ‖y‖ := by
    rw [scalarCartesianLaplacian_radialMode_eq_polar
      (fun _ hs ↦ horizontalMinusOutsideReal_hasDerivAt_self hkappa hs)
      (fun _ hs ↦ horizontalMinusOutsideReal_deriv_hasDerivAt_self hkappa hs) hy,
      horizontalMinusOutsideReal_polar hkappa hr]
  have hpLap : scalarCartesianLaplacian (phaseSqRadialMode (plusOutsideReal kappa)) y =
      exteriorPhase y ^ 2 * (kappa ^ 2 * plusOutsideReal kappa ‖y‖) := by
    rw [scalarCartesianLaplacian_phaseSqRadialMode_eq_polar
      (fun _ hs ↦ horizontalPlusOutsideReal_hasDerivAt_self hkappa hs)
      (fun _ hs ↦ horizontalPlusOutsideReal_deriv_hasDerivAt_self hkappa hs) hy,
      horizontalPlusOutsideReal_polar hkappa hr]
  have hfield := congrFun (horizontalExteriorField_apply_one_eq_modes kappa) y
  rw [horizontalExteriorLaplacian_apply hkappa hy,
    horizontalExteriorField_apply_one_eq_modes,
    scalarCartesianLaplacian_linearCombination hm hp, hmLap, hpLap, hfield]
  simp only [radialMode, phaseSqRadialMode]
  ring

/-- Away from the origin the decaying exterior branch satisfies the same transverse Helmholtz
equation `Δ_⊥ b_out = κ² b_out` as the regular one: the radial system in the proof of
`lem:jump-horizontal-mode` is the same inside and outside. -/
theorem horizontalExteriorLaplacian_eq
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) :
    horizontalExteriorLaplacian kappa y = kappa ^ 2 • horizontalExteriorField kappa y := by
  apply PiLp.ext
  intro a
  fin_cases a
  · exact horizontalExteriorLaplacian_apply_zero_eq hkappa hy
  · exact horizontalExteriorLaplacian_apply_one_eq hkappa hy

/-! ## Exponential decay and `L²` control of the second partials -/

/-- The common exterior Hessian envelope constant for the two Cartesian components: the sum of
the order-zero and order-two polar Hessian constants of
`Local/PonomarenkoExteriorSecondPartialBounds.lean`. -/
def horizontalExteriorHessianConstant (kappa : ℂ) : ℝ :=
  minusHessianConstant kappa + plusHessianConstant kappa

/-- The exterior Hessian envelope constant is nonnegative. -/
theorem horizontalExteriorHessianConstant_nonneg (kappa : ℂ) :
    0 ≤ horizontalExteriorHessianConstant kappa :=
  add_nonneg (minusHessianConstant_nonneg kappa) (plusHessianConstant_nonneg kappa)

/-- The sum of the two scalar polar Hessian moduli obeys the exponential envelope. -/
private theorem norm_exteriorSecondPartialValues_sum_le
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : 1 ≤ ‖y‖) (j k : Fin 2) :
    ‖exteriorMinusSecondPartialValue kappa y j k‖ +
        ‖exteriorPlusSecondPartialValue kappa y j k‖ ≤
      2 * (radialExponentialEnvelope kappa.re y * horizontalExteriorHessianConstant kappa) := by
  have hE : (0 : ℝ) ≤ radialExponentialEnvelope kappa.re y := (Real.exp_pos _).le
  have hM : (0 : ℝ) ≤ minusHessianConstant kappa := minusHessianConstant_nonneg kappa
  have hP : (0 : ℝ) ≤ plusHessianConstant kappa := plusHessianConstant_nonneg kappa
  have hm : ‖exteriorMinusSecondPartialValue kappa y j k‖ ≤
      radialExponentialEnvelope kappa.re y * minusHessianConstant kappa :=
    norm_exteriorMinusSecondPartialValue_le_exp 1 hkappa hy j k
  have hp : ‖exteriorPlusSecondPartialValue kappa y j k‖ ≤
      radialExponentialEnvelope kappa.re y * plusHessianConstant kappa :=
    norm_exteriorPlusSecondPartialValue_le_exp hkappa hy j k
  unfold horizontalExteriorHessianConstant
  nlinarith [hm, hp, hE, hM, hP]

/-- Exponential decay of the two-component exterior polar second-partial model, with the
explicit constant `2 · horizontalExteriorHessianConstant κ`. -/
theorem norm_horizontalExteriorSecondPartialModel_le_exp
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : 1 ≤ ‖y‖) (j k : Fin 2) :
    ‖horizontalExteriorSecondPartialModel kappa j k y‖ ≤
      2 * horizontalExteriorHessianConstant kappa *
        radialExponentialEnvelope kappa.re y := by
  set E : ℝ := radialExponentialEnvelope kappa.re y with hEdef
  set C : ℝ := horizontalExteriorHessianConstant kappa with hCdef
  have hE : (0 : ℝ) ≤ E := (Real.exp_pos _).le
  have hC : (0 : ℝ) ≤ C := horizontalExteriorHessianConstant_nonneg kappa
  have hsum := norm_exteriorSecondPartialValues_sum_le hkappa hy j k
  have hzero : ‖horizontalExteriorSecondPartialModel kappa j k y 0‖ ≤ E * C := by
    rw [horizontalExteriorSecondPartialModel_apply_zero, norm_div]
    norm_num only [Complex.norm_ofNat]
    calc
      ‖exteriorMinusSecondPartialValue kappa y j k +
          exteriorPlusSecondPartialValue kappa y j k‖ / 2 ≤
          (‖exteriorMinusSecondPartialValue kappa y j k‖ +
            ‖exteriorPlusSecondPartialValue kappa y j k‖) / 2 := by
        gcongr
        exact norm_add_le _ _
      _ ≤ E * C := by linarith
  have hone : ‖horizontalExteriorSecondPartialModel kappa j k y 1‖ ≤ E * C := by
    rw [horizontalExteriorSecondPartialModel_apply_one, norm_div, norm_mul]
    norm_num only [Complex.norm_I, Complex.norm_ofNat, one_mul]
    calc
      ‖exteriorMinusSecondPartialValue kappa y j k -
          exteriorPlusSecondPartialValue kappa y j k‖ / 2 ≤
          (‖exteriorMinusSecondPartialValue kappa y j k‖ +
            ‖exteriorPlusSecondPartialValue kappa y j k‖) / 2 := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ E * C := by linarith
  have hsq : ‖horizontalExteriorSecondPartialModel kappa j k y‖ ^ 2 ≤ (2 * C * E) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    nlinarith [norm_nonneg (horizontalExteriorSecondPartialModel kappa j k y 0),
      norm_nonneg (horizontalExteriorSecondPartialModel kappa j k y 1)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- Exponential decay of the ordered second Cartesian partial of the exterior branch,
outside the unit disk. -/
theorem norm_horizontalExteriorSecondPartialDerivative_le_exp
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : 1 ≤ ‖y‖) (j k : Fin 2) :
    ‖horizontalExteriorSecondPartialDerivative kappa j k y‖ ≤
      2 * horizontalExteriorHessianConstant kappa *
        radialExponentialEnvelope kappa.re y := by
  have hy0 : y ≠ 0 := by
    intro hzero
    rw [hzero] at hy
    norm_num at hy
  rw [horizontalExteriorSecondPartialDerivative_eq_model hkappa hy0]
  exact norm_horizontalExteriorSecondPartialModel_le_exp hkappa hy j k

/-- The totalized exterior second partial is measurable on the whole plane. -/
theorem horizontalExteriorSecondPartialDerivative_measurable
    (kappa : ℂ) (j k : Fin 2) :
    Measurable (horizontalExteriorSecondPartialDerivative kappa j k) :=
  measurable_fderiv_apply_const ℝ (horizontalExteriorPartialDerivative kappa j)
    (wholePlaneBasis k)

/-- Every ordered second Cartesian partial of the exterior branch is square integrable outside
the unit disk. -/
theorem horizontalExteriorSecondPartialDerivative_memLp_two_unitExterior
    {kappa : ℂ} (hkappa : 0 < kappa.re) (j k : Fin 2) :
    MemLp (horizontalExteriorSecondPartialDerivative kappa j k) 2
      (volume.restrict unitExterior) := by
  have hmeas : AEStronglyMeasurable (horizontalExteriorSecondPartialDerivative kappa j k) volume :=
    (horizontalExteriorSecondPartialDerivative_measurable kappa j k).aestronglyMeasurable
  refine memLp_two_unitExterior_of_norm_le_radialExponential
    (C := 2 * horizontalExteriorHessianConstant kappa) hkappa hmeas.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_unitExterior] with y hy
  exact norm_horizontalExteriorSecondPartialDerivative_le_exp hkappa hy j k

end HorizontalMode
end FastDynamo
