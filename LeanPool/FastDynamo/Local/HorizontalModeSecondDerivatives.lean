/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.ScalarSecondPartialBridges
public import LeanPool.FastDynamo.Local.HorizontalModeSurface
public import LeanPool.FastDynamo.Local.PonomarenkoCartesianPolarLaplacian

/-!
# Second Cartesian derivatives of the two-component Ponomarenko mode: the interior branch

The eigenvalue equation of `lem:jump-horizontal-mode` is second order, so the bulk half of
the distributional identity that `Local/HorizontalModeWeakIdentity.lean` takes as a hypothesis
needs the *pointwise* second derivatives of the mode on each side of the unit circle.  This
module supplies them for the two-component field `b : ℝ² → ℂ²` of
`Local/HorizontalModeBranches.lean`.

The paper writes the mode in the circular combinations

`b₁ + i b₂ = e^{2iθ}B₊(r)`,  `b₁ - i b₂ = B₋(r)`,

and records the radial system (proof of `lem:jump-horizontal-mode`)

`B_±'' + r⁻¹B_±' - (ν_±²r⁻² + κ²)B_± = 0`,  `ν₊ = 2`, `ν₋ = 0`.

Since the polar Laplacian of an angular-frequency-`ν` mode `q^ν B(r)` is
`q^ν(B'' + r⁻¹B' - ν²r⁻²B)`, the radial system says exactly that **both** circular
combinations are eigenfunctions of the transverse Laplacian with the same eigenvalue `κ²`.
Consequently the Cartesian statement is the very clean

`Δ_⊥ b = κ² b`

on each branch, off the polar axis for the decaying branch and everywhere for the regular
one.  That identity, and not the individual Hessian entries, is what the bulk equation of
`Local/HorizontalModeBulkIdentity.lean` consumes.

Contents.

* A `ℂ²` version of the scalar-component bridge for second Fréchet partials, and the germ
  invariance of the scalar second partial.
* The real radial restrictions of the four circular branches, their derivatives, and the
  eigenvalue form `B'' + r⁻¹B' - ν²r⁻²B = κ²B` of the radial system.
* The regular interior branch: smoothness of the first partials, the ordered second partials,
  their continuity through the origin, `Δ_⊥ b_in = κ² b_in` on the whole plane, and the
  closed-disk `L²` bound.
The decaying exterior branch is treated in `Local/HorizontalModeExteriorSecondDerivatives.lean`,
which continues this module.

Everything scalar and fibre-independent is imported from the scalar layer of the Cartesian
Ponomarenko field (`PonomarenkoCartesianPolarLaplacian`, `PolarHessianCalculus`,
`PonomarenkoExteriorSecondPartialBounds`); nothing `C3`-valued is used.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace HorizontalMode

open Complex Filter MeasureTheory Metric Set Topology
open CartesianRadialRegularity
open ModifiedBesselBoundaryBehavior
open PolarHessianCalculus
open PonomarenkoCartesianExteriorDerivative
open ComplexRadius
open PonomarenkoOriginProfiles
open PonomarenkoCartesianPolarLaplacian
open PonomarenkoCrossNormalizedJump
open PonomarenkoCrossNormalizedRadialODE
open PonomarenkoRealRadialBridge
open ScalarSecondPartial
open WholePlaneRadialExponential

/-! ## The polar radial operator on an analytic branch -/

/-- Dividing the denominator-free radial Bessel equation by `r²` turns it into the statement
that the polar radial operator of order `ν²` acts on the branch as multiplication by `κ²`.
This is `B'' + r⁻¹B' - ν²r⁻²B = κ²B` of the proof of `lem:jump-horizontal-mode`. -/
theorem realPolarRadialOperator_eq_of_radialResidual
    {orderSq kappa : ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : r ≠ 0)
    (hf : AnalyticAt ℂ f (r : ℂ))
    (hres : radialResidual orderSq kappa f (r : ℂ) = 0) :
    realPolarRadialOperator orderSq (fun s : ℝ ↦ f (s : ℂ)) r = kappa ^ 2 * f (r : ℂ) := by
  have hrc : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  rw [realPolarRadialOperator, deriv_realRestriction_eq hf.differentiableAt,
    deriv_deriv_realRestriction_eq hf]
  rw [radialResidual] at hres
  rw [Complex.ofReal_div, Complex.ofReal_one]
  field_simp
  linear_combination hres

/-! ## Real radial restrictions of the four circular branches -/

/-- The regular order-two interior branch restricted to the real radial axis. -/
def horizontalPlusInsideReal (kappa : ℂ) (r : ℝ) : ℂ :=
  plusInside kappa (r : ℂ)

/-- The signed regular order-zero interior branch restricted to the real radial axis. -/
def horizontalMinusInsideReal (kappa : ℂ) (r : ℝ) : ℂ :=
  minusInside kappa (r : ℂ)

/-- The real restriction of the regular order-two branch is differentiable at every radius. -/
theorem horizontalPlusInsideReal_hasDerivAt_self (kappa : ℂ) (r : ℝ) :
    HasDerivAt (horizontalPlusInsideReal kappa)
      (deriv (horizontalPlusInsideReal kappa) r) r :=
  realRestriction_hasDerivAt_self (plusInside_analyticAt kappa (r : ℂ))

/-- The derivative of the real restriction of the regular order-two branch is again
differentiable at every radius. -/
theorem horizontalPlusInsideReal_deriv_hasDerivAt_self (kappa : ℂ) (r : ℝ) :
    HasDerivAt (deriv (horizontalPlusInsideReal kappa))
      (deriv (deriv (horizontalPlusInsideReal kappa)) r) r :=
  realRestriction_deriv_hasDerivAt_self (plusInside_analyticAt kappa (r : ℂ))

/-- The real restriction of the signed regular order-zero branch is differentiable at every
radius. -/
theorem horizontalMinusInsideReal_hasDerivAt_self (kappa : ℂ) (r : ℝ) :
    HasDerivAt (horizontalMinusInsideReal kappa)
      (deriv (horizontalMinusInsideReal kappa) r) r :=
  realRestriction_hasDerivAt_self (minusInside_analyticAt kappa (r : ℂ))

/-- The derivative of the real restriction of the signed regular order-zero branch is again
differentiable at every radius. -/
theorem horizontalMinusInsideReal_deriv_hasDerivAt_self (kappa : ℂ) (r : ℝ) :
    HasDerivAt (deriv (horizontalMinusInsideReal kappa))
      (deriv (deriv (horizontalMinusInsideReal kappa)) r) r :=
  realRestriction_deriv_hasDerivAt_self (minusInside_analyticAt kappa (r : ℂ))

/-- The decaying order-two branch is analytic at every radius of positive real part. -/
theorem horizontalPlusOutside_analyticAt
    {kappa r : ℂ} (hkr : 0 < (kappa * r).re) :
    AnalyticAt ℂ (plusOutside kappa) r := by
  have hinner : AnalyticAt ℂ (fun s : ℂ ↦ kappa * s) r :=
    analyticAt_const.mul analyticAt_id
  unfold plusOutside
  convert! analyticAt_const.mul
    ((ModifiedBessel.analyticOnNhd_K2 (kappa * r) hkr).comp hinner) using 1

/-- The signed decaying order-zero branch is analytic at every radius of positive real
part. -/
theorem horizontalMinusOutside_analyticAt
    {kappa r : ℂ} (hkr : 0 < (kappa * r).re) :
    AnalyticAt ℂ (minusOutside kappa) r := by
  have hinner : AnalyticAt ℂ (fun s : ℂ ↦ kappa * s) r :=
    analyticAt_const.mul analyticAt_id
  unfold minusOutside
  convert! analyticAt_const.mul
    ((ModifiedBessel.analyticOnNhd_K0 (kappa * r) hkr).comp hinner) using 1

/-- The product `κ r` has positive real part whenever `Re κ > 0` and `r > 0`. -/
theorem horizontalExteriorArgument_re_pos
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    0 < (kappa * (r : ℂ)).re := by
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact mul_pos hkappa hr

/-- The real restriction of the decaying order-two branch is differentiable at every positive
radius. -/
theorem horizontalPlusOutsideReal_hasDerivAt_self
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (plusOutsideReal kappa) (deriv (plusOutsideReal kappa) r) r :=
  realRestriction_hasDerivAt_self
    (horizontalPlusOutside_analyticAt (horizontalExteriorArgument_re_pos hkappa hr))

/-- The derivative of the real restriction of the decaying order-two branch is again
differentiable at every positive radius. -/
theorem horizontalPlusOutsideReal_deriv_hasDerivAt_self
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv (plusOutsideReal kappa)) (deriv (deriv (plusOutsideReal kappa)) r) r :=
  realRestriction_deriv_hasDerivAt_self
    (horizontalPlusOutside_analyticAt (horizontalExteriorArgument_re_pos hkappa hr))

/-- The real restriction of the signed decaying order-zero branch is differentiable at every
positive radius. -/
theorem horizontalMinusOutsideReal_hasDerivAt_self
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (minusOutsideReal kappa) (deriv (minusOutsideReal kappa) r) r :=
  realRestriction_hasDerivAt_self
    (horizontalMinusOutside_analyticAt (horizontalExteriorArgument_re_pos hkappa hr))

/-- The derivative of the real restriction of the signed decaying order-zero branch is again
differentiable at every positive radius. -/
theorem horizontalMinusOutsideReal_deriv_hasDerivAt_self
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv (minusOutsideReal kappa)) (deriv (deriv (minusOutsideReal kappa)) r) r :=
  realRestriction_deriv_hasDerivAt_self
    (horizontalMinusOutside_analyticAt (horizontalExteriorArgument_re_pos hkappa hr))

/-! ## Smoothness of the two angular modes -/

/-- If `f` is complex analytic at the radius `‖y‖`, the radial mode `x ↦ f(‖x‖)` is smooth of
every order at `y ≠ 0`. -/
theorem radialMode_contDiffAt_infty
    {f : ℂ → ℂ} {y : WholePlane} (hy : y ≠ 0)
    (hf : AnalyticAt ℂ f ((‖y‖ : ℝ) : ℂ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (radialMode (fun r : ℝ ↦ f (r : ℂ))) y := by
  have hb : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℝ ↦ f (r : ℂ)) ‖y‖ :=
    (realRestriction_analyticAt hf).contDiffAt
  have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : WholePlane ↦ ‖x‖) y :=
    contDiffAt_norm ℝ hy
  exact ContDiffAt.fun_comp y (g := fun r : ℝ ↦ f (r : ℂ)) hb hnorm

/-- If `f` is complex analytic at the radius `‖y‖`, the angular-frequency-two mode
`x ↦ q(x)² f(‖x‖)` is smooth of every order at `y ≠ 0`. -/
theorem phaseSqRadialMode_contDiffAt_infty
    {f : ℂ → ℂ} {y : WholePlane} (hy : y ≠ 0)
    (hf : AnalyticAt ℂ f ((‖y‖ : ℝ) : ℂ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (phaseSqRadialMode (fun r : ℝ ↦ f (r : ℂ))) y := by
  have hb := radialMode_contDiffAt_infty hy hf
  have hq := PonomarenkoExteriorSecondDerivative.exteriorPhase_contDiffAt_infty hy
  convert! (hq.pow 2).mul hb using 1

/-- Order-two form of the radial-mode smoothness. -/
theorem radialMode_contDiffAt_two
    {f : ℂ → ℂ} {y : WholePlane} (hy : y ≠ 0)
    (hf : AnalyticAt ℂ f ((‖y‖ : ℝ) : ℂ)) :
    ContDiffAt ℝ 2 (radialMode (fun r : ℝ ↦ f (r : ℂ))) y :=
  (radialMode_contDiffAt_infty hy hf).of_le horizontalTwo_le_top

/-- Order-two form of the angular-frequency-two mode smoothness. -/
theorem phaseSqRadialMode_contDiffAt_two
    {f : ℂ → ℂ} {y : WholePlane} (hy : y ≠ 0)
    (hf : AnalyticAt ℂ f ((‖y‖ : ℝ) : ℂ)) :
    ContDiffAt ℝ 2 (phaseSqRadialMode (fun r : ℝ ↦ f (r : ℂ))) y :=
  (phaseSqRadialMode_contDiffAt_infty hy hf).of_le horizontalTwo_le_top

/-! ## Polar Laplacian of the two angular modes -/

/-- Off the polar axis, the Cartesian Laplacian of a radial mode is the order-zero polar
radial operator evaluated at `‖y‖`. -/
theorem scalarCartesianLaplacian_radialMode_eq_polar
    {b : ℝ → ℂ}
    (hb : ∀ r : ℝ, 0 < r → HasDerivAt b (deriv b r) r)
    (hb'' : ∀ r : ℝ, 0 < r → HasDerivAt (deriv b) (deriv (deriv b) r) r)
    {y : WholePlane} (hy : y ≠ 0) :
    scalarCartesianLaplacian (radialMode b) y = realPolarRadialOperator 0 b ‖y‖ := by
  rw [scalarCartesianLaplacian_radialMode hb hb'' hy]
  simp [realPolarRadialOperator]

/-- Off the polar axis, the Cartesian Laplacian of `q² b(r)` is `q²` times the order-two polar
radial operator evaluated at `‖y‖`. -/
theorem scalarCartesianLaplacian_phaseSqRadialMode_eq_polar
    {b : ℝ → ℂ}
    (hb : ∀ r : ℝ, 0 < r → HasDerivAt b (deriv b r) r)
    (hb'' : ∀ r : ℝ, 0 < r → HasDerivAt (deriv b) (deriv (deriv b) r) r)
    {y : WholePlane} (hy : y ≠ 0) :
    scalarCartesianLaplacian (phaseSqRadialMode b) y =
      exteriorPhase y ^ 2 * realPolarRadialOperator 4 b ‖y‖ := by
  rw [scalarCartesianLaplacian_phaseSqRadialMode hb hb'' hy]
  unfold realPolarRadialOperator
  simp only [complexRadius]

/-- The regular order-zero branch is an eigenfunction of the order-zero polar radial operator
with eigenvalue `κ²`. -/
theorem horizontalMinusInsideReal_polar (kappa : ℂ) {r : ℝ} (hr : r ≠ 0) :
    realPolarRadialOperator 0 (horizontalMinusInsideReal kappa) r =
      kappa ^ 2 * horizontalMinusInsideReal kappa r :=
  realPolarRadialOperator_eq_of_radialResidual hr (minusInside_analyticAt kappa (r : ℂ))
    (minusInside_radialResidual kappa (r : ℂ))

/-- The regular order-two branch is an eigenfunction of the order-two polar radial operator
with eigenvalue `κ²`. -/
theorem horizontalPlusInsideReal_polar
    {kappa : ℂ} (hkappa : kappa ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    realPolarRadialOperator 4 (horizontalPlusInsideReal kappa) r =
      kappa ^ 2 * horizontalPlusInsideReal kappa r :=
  realPolarRadialOperator_eq_of_radialResidual hr (plusInside_analyticAt kappa (r : ℂ))
    (plusInside_radialResidual (mul_ne_zero hkappa (Complex.ofReal_ne_zero.mpr hr)))

/-- The decaying order-zero branch is an eigenfunction of the order-zero polar radial operator
with eigenvalue `κ²`. -/
theorem horizontalMinusOutsideReal_polar
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    realPolarRadialOperator 0 (minusOutsideReal kappa) r =
      kappa ^ 2 * minusOutsideReal kappa r :=
  realPolarRadialOperator_eq_of_radialResidual (ne_of_gt hr)
    (horizontalMinusOutside_analyticAt (horizontalExteriorArgument_re_pos hkappa hr))
    (minusOutside_radialResidual (horizontalExteriorArgument_re_pos hkappa hr))

/-- The decaying order-two branch is an eigenfunction of the order-two polar radial operator
with eigenvalue `κ²`. -/
theorem horizontalPlusOutsideReal_polar
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    realPolarRadialOperator 4 (plusOutsideReal kappa) r =
      kappa ^ 2 * plusOutsideReal kappa r :=
  realPolarRadialOperator_eq_of_radialResidual (ne_of_gt hr)
    (horizontalPlusOutside_analyticAt (horizontalExteriorArgument_re_pos hkappa hr))
    (plusOutside_radialResidual (horizontalExteriorArgument_re_pos hkappa hr))

/-! ## The regular interior branch as a pair of angular modes -/

/-- The order-zero part of the regular interior field is the radial mode of the regular
order-zero branch; the identification is valid on the polar axis as well. -/
theorem radialScalar_minusOriginProfile_eq_radialMode (kappa : ℂ) (y : WholePlane) :
    radialScalar (minusOriginProfile kappa) y =
      radialMode (horizontalMinusInsideReal kappa) y := by
  change radialScalar (minusOriginProfile kappa) y = minusInside kappa ((‖y‖ : ℝ) : ℂ)
  rw [minusInside_origin_factorization]
  simp only [radialScalar, minusOriginProfile, squaredRadius]
  norm_cast

/-- Off the polar axis, the order-two part of the regular interior field is the
angular-frequency-two mode of the regular order-two branch: `z²Φ₊(r²) = q²B₊(r)`. -/
theorem degreeTwoFactor_plusOriginProfile_eq_phaseSqRadialMode
    (kappa : ℂ) {y : WholePlane} (hy : y ≠ 0) :
    degreeTwoFactor (plusOriginProfile kappa) y =
      phaseSqRadialMode (horizontalPlusInsideReal kappa) y := by
  have hr : ((‖y‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  change degreeTwoFactor (plusOriginProfile kappa) y =
    exteriorPhase y ^ 2 * plusInside kappa ((‖y‖ : ℝ) : ℂ)
  rw [plusInside_origin_factorization]
  simp only [degreeTwoFactor, radialScalar, plusOriginProfile, squaredRadius,
    exteriorPhase, complexRadius]
  have hsq : (((‖y‖ ^ 2 : ℝ)) : ℂ) = ((‖y‖ : ℝ) : ℂ) ^ 2 := by norm_cast
  rw [hsq]
  field_simp

/-- Off the polar axis, the first Cartesian component of the regular interior field is the
combination `½B₋(r) + ½q²B₊(r)` of the two interior angular modes. -/
theorem horizontalInteriorField_apply_zero_eqOn_modes (kappa : ℂ) :
    EqOn (fun x : WholePlane ↦ horizontalInteriorField kappa x 0)
      (fun x : WholePlane ↦
        (1 / 2 : ℂ) * radialMode (horizontalMinusInsideReal kappa) x +
          (1 / 2 : ℂ) * phaseSqRadialMode (horizontalPlusInsideReal kappa) x)
      ({0}ᶜ : Set WholePlane) := by
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [horizontalInteriorField_apply_zero,
    radialScalar_minusOriginProfile_eq_radialMode,
    degreeTwoFactor_plusOriginProfile_eq_phaseSqRadialMode kappa hx0]
  ring

/-- Off the polar axis, the second Cartesian component of the regular interior field is the
combination `(i/2)B₋(r) - (i/2)q²B₊(r)` of the two interior angular modes. -/
theorem horizontalInteriorField_apply_one_eqOn_modes (kappa : ℂ) :
    EqOn (fun x : WholePlane ↦ horizontalInteriorField kappa x 1)
      (fun x : WholePlane ↦
        (I / 2 : ℂ) * radialMode (horizontalMinusInsideReal kappa) x +
          (-I / 2 : ℂ) * phaseSqRadialMode (horizontalPlusInsideReal kappa) x)
      ({0}ᶜ : Set WholePlane) := by
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [horizontalInteriorField_apply_one,
    radialScalar_minusOriginProfile_eq_radialMode,
    degreeTwoFactor_plusOriginProfile_eq_phaseSqRadialMode kappa hx0]
  ring

/-- Germ form of the first interior component decomposition. -/
theorem horizontalInteriorField_apply_zero_eventuallyEq_modes
    (kappa : ℂ) {y : WholePlane} (hy : y ≠ 0) :
    (fun x : WholePlane ↦ horizontalInteriorField kappa x 0) =ᶠ[nhds y]
      fun x : WholePlane ↦
        (1 / 2 : ℂ) * radialMode (horizontalMinusInsideReal kappa) x +
          (1 / 2 : ℂ) * phaseSqRadialMode (horizontalPlusInsideReal kappa) x :=
  Filter.eventuallyEq_of_mem
    (isOpen_compl_singleton.mem_nhds (by simpa using hy))
    (horizontalInteriorField_apply_zero_eqOn_modes kappa)

/-- Germ form of the second interior component decomposition. -/
theorem horizontalInteriorField_apply_one_eventuallyEq_modes
    (kappa : ℂ) {y : WholePlane} (hy : y ≠ 0) :
    (fun x : WholePlane ↦ horizontalInteriorField kappa x 1) =ᶠ[nhds y]
      fun x : WholePlane ↦
        (I / 2 : ℂ) * radialMode (horizontalMinusInsideReal kappa) x +
          (-I / 2 : ℂ) * phaseSqRadialMode (horizontalPlusInsideReal kappa) x :=
  Filter.eventuallyEq_of_mem
    (isOpen_compl_singleton.mem_nhds (by simpa using hy))
    (horizontalInteriorField_apply_one_eqOn_modes kappa)

/-! ## Second Cartesian derivatives of the regular interior branch -/

/-- Every first Cartesian partial of the regular interior field is again smooth on the whole
plane, the polar axis included. -/
theorem horizontalInteriorPartialDerivative_contDiff (kappa : ℂ) (j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (horizontalInteriorPartialDerivative kappa j) := by
  have hfderiv : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (horizontalInteriorField kappa)) :=
    (contDiff_infty_iff_fderiv.mp (horizontalInteriorField_contDiff kappa)).2
  unfold horizontalInteriorPartialDerivative
  exact hfderiv.clm_apply contDiff_const

/-- The ordered second Cartesian partial `∂_k∂_j b_in` of the regular interior field. -/
def horizontalInteriorSecondPartialDerivative
    (kappa : ℂ) (j k : Fin 2) (y : WholePlane) : C2 :=
  fderiv ℝ (horizontalInteriorPartialDerivative kappa j) y (wholePlaneBasis k)

/-- Every first Cartesian partial of the regular interior field is Fréchet differentiable at
every point, so the previous definition is a classical second partial. -/
theorem horizontalInteriorPartialDerivative_hasFDerivAt
    (kappa : ℂ) (j : Fin 2) (y : WholePlane) :
    HasFDerivAt (horizontalInteriorPartialDerivative kappa j)
      (fderiv ℝ (horizontalInteriorPartialDerivative kappa j) y) y :=
  ((horizontalInteriorPartialDerivative_contDiff kappa j).differentiable
    (by simp) y).hasFDerivAt

/-- The interior second Cartesian partials are continuous on the whole plane, in particular
through the removable polar axis. -/
theorem horizontalInteriorSecondPartialDerivative_continuous (kappa : ℂ) (j k : Fin 2) :
    Continuous (horizontalInteriorSecondPartialDerivative kappa j k) := by
  unfold horizontalInteriorSecondPartialDerivative
  exact ((horizontalInteriorPartialDerivative_contDiff kappa j).continuous_fderiv
    (by simp)).clm_apply continuous_const

/-- Componentwise, the interior second Cartesian partial is the scalar second partial of the
corresponding component. -/
theorem horizontalInteriorSecondPartialDerivative_apply
    (kappa : ℂ) (j k : Fin 2) (y : WholePlane) (a : Fin 2) :
    horizontalInteriorSecondPartialDerivative kappa j k y a =
      scalarSecondPartial (fun x : WholePlane ↦ horizontalInteriorField kappa x a) j k y := by
  have htwo : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  unfold horizontalInteriorSecondPartialDerivative horizontalInteriorPartialDerivative
  exact c2SecondPartial_apply_eq_scalarSecondPartial
    (((horizontalInteriorField_contDiff kappa).of_le htwo).contDiffAt) j k a

/-- The transverse Cartesian Laplacian of the regular interior branch, the trace of its
Hessian. -/
def horizontalInteriorLaplacian (kappa : ℂ) (y : WholePlane) : C2 :=
  ∑ j : Fin 2, horizontalInteriorSecondPartialDerivative kappa j j y

/-- Componentwise, the interior Laplacian is the scalar Cartesian Laplacian of the
corresponding component. -/
theorem horizontalInteriorLaplacian_apply (kappa : ℂ) (y : WholePlane) (a : Fin 2) :
    horizontalInteriorLaplacian kappa y a =
      scalarCartesianLaplacian
        (fun x : WholePlane ↦ horizontalInteriorField kappa x a) y := by
  simp only [horizontalInteriorLaplacian, Fin.sum_univ_two, PiLp.add_apply,
    horizontalInteriorSecondPartialDerivative_apply, scalarCartesianLaplacian]

/-- The interior Laplacian is continuous on the whole plane. -/
theorem horizontalInteriorLaplacian_continuous (kappa : ℂ) :
    Continuous (horizontalInteriorLaplacian kappa) := by
  unfold horizontalInteriorLaplacian
  exact continuous_finsetSum _ fun j _ ↦
    horizontalInteriorSecondPartialDerivative_continuous kappa j j

/-- Off the polar axis, the first Cartesian component of the regular interior branch satisfies
`Δ_⊥ b₁ = κ² b₁`. -/
theorem horizontalInteriorLaplacian_apply_zero_eq
    {kappa : ℂ} (hkappa : kappa ≠ 0) {y : WholePlane} (hy : y ≠ 0) :
    horizontalInteriorLaplacian kappa y 0 = kappa ^ 2 * horizontalInteriorField kappa y 0 := by
  have hrne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hmC2 : ContDiffAt ℝ 2 (radialMode (horizontalMinusInsideReal kappa)) y :=
    radialMode_contDiffAt_two hy (minusInside_analyticAt kappa ((‖y‖ : ℝ) : ℂ))
  have hpC2 : ContDiffAt ℝ 2 (phaseSqRadialMode (horizontalPlusInsideReal kappa)) y :=
    phaseSqRadialMode_contDiffAt_two hy (plusInside_analyticAt kappa ((‖y‖ : ℝ) : ℂ))
  have hmLap : scalarCartesianLaplacian (radialMode (horizontalMinusInsideReal kappa)) y =
      kappa ^ 2 * horizontalMinusInsideReal kappa ‖y‖ := by
    rw [scalarCartesianLaplacian_radialMode_eq_polar
      (fun _ _ ↦ horizontalMinusInsideReal_hasDerivAt_self kappa _)
      (fun _ _ ↦ horizontalMinusInsideReal_deriv_hasDerivAt_self kappa _) hy,
      horizontalMinusInsideReal_polar kappa hrne]
  have hpLap :
      scalarCartesianLaplacian (phaseSqRadialMode (horizontalPlusInsideReal kappa)) y =
      exteriorPhase y ^ 2 * (kappa ^ 2 * horizontalPlusInsideReal kappa ‖y‖) := by
    rw [scalarCartesianLaplacian_phaseSqRadialMode_eq_polar
      (fun _ _ ↦ horizontalPlusInsideReal_hasDerivAt_self kappa _)
      (fun _ _ ↦ horizontalPlusInsideReal_deriv_hasDerivAt_self kappa _) hy,
      horizontalPlusInsideReal_polar hkappa hrne]
  have hfield : horizontalInteriorField kappa y 0 =
      (1 / 2 : ℂ) * horizontalMinusInsideReal kappa ‖y‖ +
        (1 / 2 : ℂ) * (exteriorPhase y ^ 2 * horizontalPlusInsideReal kappa ‖y‖) :=
    horizontalInteriorField_apply_zero_eqOn_modes kappa (by simpa using hy)
  rw [horizontalInteriorLaplacian_apply,
    scalarCartesianLaplacian_congr_of_eventuallyEq
      (horizontalInteriorField_apply_zero_eventuallyEq_modes kappa hy),
    scalarCartesianLaplacian_linearCombination hmC2 hpC2, hmLap, hpLap, hfield]
  ring

/-- Off the polar axis, the second Cartesian component of the regular interior branch satisfies
`Δ_⊥ b₂ = κ² b₂`. -/
theorem horizontalInteriorLaplacian_apply_one_eq
    {kappa : ℂ} (hkappa : kappa ≠ 0) {y : WholePlane} (hy : y ≠ 0) :
    horizontalInteriorLaplacian kappa y 1 = kappa ^ 2 * horizontalInteriorField kappa y 1 := by
  have hrne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hmC2 : ContDiffAt ℝ 2 (radialMode (horizontalMinusInsideReal kappa)) y :=
    radialMode_contDiffAt_two hy (minusInside_analyticAt kappa ((‖y‖ : ℝ) : ℂ))
  have hpC2 : ContDiffAt ℝ 2 (phaseSqRadialMode (horizontalPlusInsideReal kappa)) y :=
    phaseSqRadialMode_contDiffAt_two hy (plusInside_analyticAt kappa ((‖y‖ : ℝ) : ℂ))
  have hmLap : scalarCartesianLaplacian (radialMode (horizontalMinusInsideReal kappa)) y =
      kappa ^ 2 * horizontalMinusInsideReal kappa ‖y‖ := by
    rw [scalarCartesianLaplacian_radialMode_eq_polar
      (fun _ _ ↦ horizontalMinusInsideReal_hasDerivAt_self kappa _)
      (fun _ _ ↦ horizontalMinusInsideReal_deriv_hasDerivAt_self kappa _) hy,
      horizontalMinusInsideReal_polar kappa hrne]
  have hpLap :
      scalarCartesianLaplacian (phaseSqRadialMode (horizontalPlusInsideReal kappa)) y =
      exteriorPhase y ^ 2 * (kappa ^ 2 * horizontalPlusInsideReal kappa ‖y‖) := by
    rw [scalarCartesianLaplacian_phaseSqRadialMode_eq_polar
      (fun _ _ ↦ horizontalPlusInsideReal_hasDerivAt_self kappa _)
      (fun _ _ ↦ horizontalPlusInsideReal_deriv_hasDerivAt_self kappa _) hy,
      horizontalPlusInsideReal_polar hkappa hrne]
  have hfield : horizontalInteriorField kappa y 1 =
      (I / 2 : ℂ) * horizontalMinusInsideReal kappa ‖y‖ +
        (-I / 2 : ℂ) * (exteriorPhase y ^ 2 * horizontalPlusInsideReal kappa ‖y‖) :=
    horizontalInteriorField_apply_one_eqOn_modes kappa (by simpa using hy)
  rw [horizontalInteriorLaplacian_apply,
    scalarCartesianLaplacian_congr_of_eventuallyEq
      (horizontalInteriorField_apply_one_eventuallyEq_modes kappa hy),
    scalarCartesianLaplacian_linearCombination hmC2 hpC2, hmLap, hpLap, hfield]
  ring

/-- Off the polar axis the regular interior branch satisfies the transverse Helmholtz equation
`Δ_⊥ b_in = κ² b_in`.  Both circular combinations obey the same radial system
(proof of `lem:jump-horizontal-mode`), the order-two angular factor exactly absorbing the
`ν₊² r⁻²` term. -/
theorem horizontalInteriorLaplacian_eq_of_ne_zero
    {kappa : ℂ} (hkappa : kappa ≠ 0) {y : WholePlane} (hy : y ≠ 0) :
    horizontalInteriorLaplacian kappa y = kappa ^ 2 • horizontalInteriorField kappa y := by
  apply PiLp.ext
  intro a
  fin_cases a
  · exact horizontalInteriorLaplacian_apply_zero_eq hkappa hy
  · exact horizontalInteriorLaplacian_apply_one_eq hkappa hy

/-- The transverse Helmholtz equation `Δ_⊥ b_in = κ² b_in` holds on the *whole* plane for the
regular interior branch: both sides are continuous and agree off the polar axis, which is a
dense subset of the plane. -/
theorem horizontalInteriorLaplacian_eq
    {kappa : ℂ} (hkappa : kappa ≠ 0) (y : WholePlane) :
    horizontalInteriorLaplacian kappa y = kappa ^ 2 • horizontalInteriorField kappa y := by
  have hfun : horizontalInteriorLaplacian kappa =
      fun x : WholePlane ↦ kappa ^ 2 • horizontalInteriorField kappa x := by
    apply Continuous.ext_on (dense_compl_singleton (0 : WholePlane))
      (horizontalInteriorLaplacian_continuous kappa)
      ((horizontalInteriorField_continuous kappa).const_smul (kappa ^ 2))
    intro x hx
    exact horizontalInteriorLaplacian_eq_of_ne_zero hkappa (by simpa using hx)
  exact congrFun hfun y

end HorizontalMode
end FastDynamo
