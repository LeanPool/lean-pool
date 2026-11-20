/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.PonomarenkoExteriorDerivativeDecay
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The two Cartesian components of the horizontal Ponomarenko mode

This module builds the pointwise `ℂ²`-valued eigenmode of `lem:jump-horizontal-mode`
(last paragraph of its proof) out of the cross-normalized radial branches.

The paper writes the angular mode `b = e^{iθ}(B_r e_r + B_θ e_θ)` in the circular
variables `B_± = B_r ± i B_θ` and records the Cartesian combinations

`b₁ + i b₂ = e^{2iθ} B₊(r)`,  `b₁ - i b₂ = B₋(r)`,

with `B₊` built from `I₂/K₂` and `B₋` from `I₀/K₀` at the radial parameter `κ`
(`eq:bessel-solutions`).  Equivalently

`b₁ = (B₋ + q² B₊)/2`,  `b₂ = i(B₋ - q² B₊)/2`,  `q = z/r = e^{iθ}`.

Only the two transverse components are used — the axial branch of the Cartesian Ponomarenko
field of the `PonomarenkoCartesian*` modules does not enter: the horizontal operator
`A_w` of `eq:horizontal-induction` acts on two-component fields.

Contents.

* The interior field, written without dividing by the polar radius: `I₂(κr) = r²` times an
  analytic function of `r²` and `I₀(κr)` is analytic in `r²`, so the mode extends smoothly
  through the origin (proof of `lem:jump-horizontal-mode`).
* The exterior field, built from the decaying branches `K₀`, `K₂`, smooth on the punctured
  plane and exponentially decaying (proof of `lem:jump-horizontal-mode`).
* The glued piecewise field, continuous across the unit circle.  In the two-component case the
  matching needs *no* hypothesis at all: the cross-normalized branches have equal traces at
  `r = 1`.
* Explicit exponential decay with rate `Re κ`, and the value at the origin, which is the
  non-vanishing witness `-K₀(κ)/2` of the paper's "non-zero eigenfunction".

No `L²`, weak-derivative, `H¹`, or eigenvalue claim is made here.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace HorizontalMode

open Complex Metric Set
open CartesianRadialRegularity
open ModifiedBesselBoundaryBehavior
open PonomarenkoCartesianExteriorDerivative
open ComplexRadius
open PonomarenkoCartesianExteriorDecay
open PonomarenkoOriginProfiles
open PonomarenkoCrossNormalizedJump

/-! ## The interior field -/

/-- The regular interior two-component field, written in the squared radius so that no polar
radius is divided out: `b = ((Φ₋ + z²Φ₊)/2, i(Φ₋ - z²Φ₊)/2)` with `Φ_±` the entire
squared-radius coefficients of the regular branches `B_±`. -/
def horizontalInteriorField (kappa : ℂ) (y : WholePlane) : C2 :=
  WithLp.toLp 2 ![
    (radialScalar (minusOriginProfile kappa) y +
      degreeTwoFactor (plusOriginProfile kappa) y) / 2,
    I * (radialScalar (minusOriginProfile kappa) y -
      degreeTwoFactor (plusOriginProfile kappa) y) / 2]

/-- First Cartesian component of the regular interior field: `(Φ₋(|y|²) + z²Φ₊(|y|²))/2`. -/
@[simp] theorem horizontalInteriorField_apply_zero (kappa : ℂ) (y : WholePlane) :
    horizontalInteriorField kappa y 0 =
      (radialScalar (minusOriginProfile kappa) y +
        degreeTwoFactor (plusOriginProfile kappa) y) / 2 := by
  simp [horizontalInteriorField]

/-- Second Cartesian component of the regular interior field: `i(Φ₋(|y|²) - z²Φ₊(|y|²))/2`. -/
@[simp] theorem horizontalInteriorField_apply_one (kappa : ℂ) (y : WholePlane) :
    horizontalInteriorField kappa y 1 =
      I * (radialScalar (minusOriginProfile kappa) y -
        degreeTwoFactor (plusOriginProfile kappa) y) / 2 := by
  simp [horizontalInteriorField]

/-- The first Cartesian component of the interior field is smooth on the whole plane. -/
theorem horizontalInteriorField_zero_contDiff (kappa : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : WholePlane ↦ horizontalInteriorField kappa y 0) := by
  have hminus := radialScalar_contDiff (minusOriginProfile_contDiff kappa)
  have hplus := degreeTwoFactor_contDiff (plusOriginProfile_contDiff kappa)
  simpa only [horizontalInteriorField_apply_zero] using (hminus.add hplus).div_const 2

/-- The second Cartesian component of the interior field is smooth on the whole plane. -/
theorem horizontalInteriorField_one_contDiff (kappa : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : WholePlane ↦ horizontalInteriorField kappa y 1) := by
  have hminus := radialScalar_contDiff (minusOriginProfile_contDiff kappa)
  have hplus := degreeTwoFactor_contDiff (plusOriginProfile_contDiff kappa)
  simpa only [horizontalInteriorField_apply_one] using
    (contDiff_const.mul (hminus.sub hplus)).div_const 2

/-- The interior two-component field is smooth on the whole plane, the polar axis included.
This is the paper's "the field is smooth at the origin" (proof of
`lem:jump-horizontal-mode`). -/
theorem horizontalInteriorField_contDiff (kappa : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (horizontalInteriorField kappa) := by
  apply (contDiff_piLp 2).2
  intro j
  fin_cases j
  · exact horizontalInteriorField_zero_contDiff kappa
  · exact horizontalInteriorField_one_contDiff kappa

/-- The interior two-component field is continuous on the whole plane. -/
theorem horizontalInteriorField_continuous (kappa : ℂ) :
    Continuous (horizontalInteriorField kappa) :=
  (horizontalInteriorField_contDiff kappa).continuous

/-- Exact value of the smooth interior extension on the polar axis: `(-K₀(κ)/2, -iK₀(κ)/2)`.
This is the witness for the non-vanishing of the eigenfunction. -/
theorem horizontalInteriorField_zero (kappa : ℂ) :
    horizontalInteriorField kappa 0 =
      WithLp.toLp 2 ![-ModifiedBessel.K0 kappa / 2,
        I * (-ModifiedBessel.K0 kappa) / 2] := by
  apply PiLp.ext
  intro j
  fin_cases j <;> simp

/-! ## The exterior field -/

/-- The decaying exterior two-component field, written with the physical polar phase
`q = z/r` and the cross-normalized decaying branches `B_±`. -/
def horizontalExteriorField (kappa : ℂ) (y : WholePlane) : C2 :=
  WithLp.toLp 2 ![
    (minusOutside kappa (complexRadius y) +
      exteriorPhase y ^ 2 * plusOutside kappa (complexRadius y)) / 2,
    I * (minusOutside kappa (complexRadius y) -
      exteriorPhase y ^ 2 * plusOutside kappa (complexRadius y)) / 2]

/-- First Cartesian component of the exterior field: `(B₋(r) + q²B₊(r))/2`. -/
@[simp] theorem horizontalExteriorField_apply_zero (kappa : ℂ) (y : WholePlane) :
    horizontalExteriorField kappa y 0 =
      (minusOutside kappa (complexRadius y) +
        exteriorPhase y ^ 2 * plusOutside kappa (complexRadius y)) / 2 := by
  simp [horizontalExteriorField]

/-- Second Cartesian component of the exterior field: `i(B₋(r) - q²B₊(r))/2`. -/
@[simp] theorem horizontalExteriorField_apply_one (kappa : ℂ) (y : WholePlane) :
    horizontalExteriorField kappa y 1 =
      I * (minusOutside kappa (complexRadius y) -
        exteriorPhase y ^ 2 * plusOutside kappa (complexRadius y)) / 2 := by
  simp [horizontalExteriorField]

/-- The exterior two-component field is continuous at every nonzero point when `Re κ > 0`. -/
theorem horizontalExteriorField_continuousAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : 0 < ‖y‖) :
    ContinuousAt (horizontalExteriorField kappa) y := by
  have hy0 : y ≠ 0 := norm_pos_iff.mp hy
  have hq : ContinuousAt exteriorPhase y :=
    (exteriorPhase_hasFDerivAt hy0).continuousAt
  have hr : ContinuousAt complexRadius y := by
    unfold complexRadius
    fun_prop
  have hkr : 0 < (kappa * complexRadius y).re := by
    simp only [complexRadius, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact mul_pos hkappa hy
  have hK2 : ContinuousAt (fun x : WholePlane ↦ plusOutside kappa (complexRadius x)) y := by
    have hb : ContinuousAt (plusOutside kappa) (complexRadius y) := by
      unfold plusOutside
      exact continuousAt_const.mul
        ((ModifiedBessel.hasDerivAt_K2 hkr).continuousAt.comp_of_eq
          (continuousAt_const.mul continuousAt_id) rfl)
    exact hb.comp_of_eq hr rfl
  have hK0 : ContinuousAt (fun x : WholePlane ↦ minusOutside kappa (complexRadius x)) y := by
    have hb : ContinuousAt (minusOutside kappa) (complexRadius y) := by
      unfold minusOutside
      exact continuousAt_const.neg.mul
        ((ModifiedBessel.hasDerivAt_K0 hkr).continuousAt.comp_of_eq
          (continuousAt_const.mul continuousAt_id) rfl)
    exact hb.comp_of_eq hr rfl
  unfold horizontalExteriorField
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℂ)).continuousAt.comp
  rw [continuousAt_pi]
  intro j
  fin_cases j
  · exact (hK0.add ((hq.pow 2).mul hK2)).div_const 2
  · exact (continuousAt_const.mul (hK0.sub ((hq.pow 2).mul hK2))).div_const 2

/-! ## Matching across the unit circle -/

/-- On the unit circle the complex radius is one. -/
private theorem complexRadius_of_norm_eq_one {y : WholePlane} (hy : ‖y‖ = 1) :
    complexRadius y = 1 := by
  simp [complexRadius, hy]

/-- On the unit circle the interior and exterior two-component formulas agree.

No interface hypothesis is needed: the cross-normalized order-zero and order-two branches have
equal traces at `r = 1` by construction, which is exactly `minus_boundaryValueJump` and
`plus_boundaryValueJump`. -/
theorem horizontalInteriorField_eq_exteriorField_of_norm_eq_one
    (kappa : ℂ) {y : WholePlane} (hy : ‖y‖ = 1) :
    horizontalInteriorField kappa y = horizontalExteriorField kappa y := by
  have hr : complexRadius y = 1 := complexRadius_of_norm_eq_one hy
  have hs : ((squaredRadius y : ℝ) : ℂ) = 1 := by
    simp [squaredRadius, hy]
  have hq : exteriorPhase y = complexCoordinate y := by
    rw [exteriorPhase, hr, div_one]
  have hplus : plusOutside kappa 1 = plusInside kappa 1 := by
    have h := plus_boundaryValueJump kappa
    change plusOutside kappa 1 - plusInside kappa 1 = 0 at h
    exact sub_eq_zero.mp h
  have hminus : minusOutside kappa 1 = minusInside kappa 1 := by
    have h := minus_boundaryValueJump kappa
    change minusOutside kappa 1 - minusInside kappa 1 = 0 at h
    exact sub_eq_zero.mp h
  have hminusTrace : radialScalar (minusOriginProfile kappa) y = minusInside kappa 1 := by
    rw [minusInside_origin_factorization]
    change minusInsideSquaredRadiusCoefficient kappa ((squaredRadius y : ℝ) : ℂ) = _
    rw [hs]
    norm_num
  have hplusTrace :
      degreeTwoFactor (plusOriginProfile kappa) y =
        complexCoordinate y ^ 2 * plusInside kappa 1 := by
    rw [plusInside_origin_factorization]
    change complexCoordinate y ^ 2 *
      plusInsideSquaredRadiusCoefficient kappa ((squaredRadius y : ℝ) : ℂ) = _
    rw [hs]
    norm_num
  have hzero : horizontalInteriorField kappa y 0 = horizontalExteriorField kappa y 0 := by
    rw [horizontalInteriorField_apply_zero, horizontalExteriorField_apply_zero,
      hminusTrace, hplusTrace, hr, hq, hplus, hminus]
  have hone : horizontalInteriorField kappa y 1 = horizontalExteriorField kappa y 1 := by
    rw [horizontalInteriorField_apply_one, horizontalExteriorField_apply_one,
      hminusTrace, hplusTrace, hr, hq, hplus, hminus]
  apply PiLp.ext
  intro j
  fin_cases j
  · exact hzero
  · exact hone

/-- Sphere-set form of the two-component trace equality. -/
theorem horizontalInteriorField_eqOn_exteriorField_unitSphere (kappa : ℂ) :
    EqOn (horizontalInteriorField kappa) (horizontalExteriorField kappa)
      (sphere (0 : WholePlane) 1) := by
  intro y hy
  apply horizontalInteriorField_eq_exteriorField_of_norm_eq_one
  simpa [mem_sphere, dist_zero_right] using hy

/-! ## The glued mode -/

/-- The pointwise two-component Ponomarenko mode: the regular formula on the closed unit disk,
the decaying formula outside.  This is the field `b` of `lem:jump-horizontal-mode`. -/
def horizontalModeField (kappa : ℂ) (y : WholePlane) : C2 :=
  if ‖y‖ ≤ 1 then horizontalInteriorField kappa y else horizontalExteriorField kappa y

/-- On the closed unit disk the mode is the regular interior formula. -/
@[simp] theorem horizontalModeField_of_norm_le
    (kappa : ℂ) {y : WholePlane} (hy : ‖y‖ ≤ 1) :
    horizontalModeField kappa y = horizontalInteriorField kappa y := by
  simp [horizontalModeField, hy]

/-- Strictly inside the unit disk the mode is the regular interior formula. -/
@[simp] theorem horizontalModeField_of_norm_lt_one
    (kappa : ℂ) {y : WholePlane} (hy : ‖y‖ < 1) :
    horizontalModeField kappa y = horizontalInteriorField kappa y :=
  horizontalModeField_of_norm_le kappa hy.le

/-- Strictly outside the unit circle the mode is the decaying exterior formula. -/
@[simp] theorem horizontalModeField_of_one_lt_norm
    (kappa : ℂ) {y : WholePlane} (hy : 1 < ‖y‖) :
    horizontalModeField kappa y = horizontalExteriorField kappa y := by
  simp [horizontalModeField, not_le_of_gt hy]

/-- The glued two-component mode is globally continuous.  This is the paper's
"continuity at `r = 1`" (proof of `lem:jump-horizontal-mode`); in the two-component case it
needs no hypothesis beyond `0 < Re κ`. -/
theorem horizontalModeField_continuous {kappa : ℂ} (hkappa : 0 < kappa.re) :
    Continuous (horizontalModeField kappa) := by
  unfold horizontalModeField
  have hset : {y : WholePlane | ‖y‖ ≤ 1} = closedBall 0 1 := by
    ext y
    simp [mem_closedBall, dist_zero_right]
  apply continuous_if
  · intro y hy
    rw [hset] at hy
    rw [frontier_closedBall (0 : WholePlane) one_ne_zero] at hy
    exact horizontalInteriorField_eqOn_exteriorField_unitSphere kappa hy
  · rw [hset, isClosed_closedBall.closure_eq]
    exact (horizontalInteriorField_continuous kappa).continuousOn
  · have hcomp : {x : WholePlane | ¬‖x‖ ≤ 1} = (closedBall 0 1)ᶜ := by
      ext y
      simp [mem_closedBall, dist_zero_right]
    rw [hcomp]
    intro y hy
    rw [closure_compl, interior_closedBall (0 : WholePlane) one_ne_zero] at hy
    have hone : 1 ≤ ‖y‖ := by
      simpa [mem_ball, dist_zero_right, not_lt] using hy
    exact (horizontalExteriorField_continuousAt hkappa
      (lt_of_lt_of_le zero_lt_one hone)).continuousWithinAt

/-- The value of the mode at the origin, the non-vanishing witness. -/
theorem horizontalModeField_zero (kappa : ℂ) :
    horizontalModeField kappa 0 =
      WithLp.toLp 2 ![-ModifiedBessel.K0 kappa / 2,
        I * (-ModifiedBessel.K0 kappa) / 2] := by
  rw [horizontalModeField_of_norm_le kappa (by simp), horizontalInteriorField_zero]

/-! ## Exponential decay of the exterior branch -/

/-- The common exterior majorant constant for the two Cartesian components, the sum of the
order-zero and order-two exterior branch constants of
`Local/PonomarenkoCartesianExteriorDecay.lean`. -/
def horizontalExteriorDecayConstant (kappa : ℂ) : ℝ :=
  exteriorPlusDecayConstant kappa + exteriorMinusDecayConstant kappa

/-- The exterior majorant constant is nonnegative. -/
theorem horizontalExteriorDecayConstant_nonneg (kappa : ℂ) :
    0 ≤ horizontalExteriorDecayConstant kappa :=
  add_nonneg (exteriorPlusDecayConstant_nonneg kappa)
    (exteriorMinusDecayConstant_nonneg kappa)

/-- The sum of the two exterior branch moduli obeys the exponential envelope. -/
private theorem norm_exteriorBranches_sum_le
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : 1 ≤ ‖y‖) :
    ‖minusOutside kappa (complexRadius y)‖ +
        ‖exteriorPhase y ^ 2 * plusOutside kappa (complexRadius y)‖ ≤
      2 * (Real.exp (-kappa.re * (‖y‖ - 1)) * horizontalExteriorDecayConstant kappa) := by
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hy
    norm_num at hy
  have hE : (0 : ℝ) ≤ Real.exp (-kappa.re * (‖y‖ - 1)) := (Real.exp_pos _).le
  have hP : (0 : ℝ) ≤ exteriorPlusDecayConstant kappa := exteriorPlusDecayConstant_nonneg kappa
  have hM : (0 : ℝ) ≤ exteriorMinusDecayConstant kappa :=
    exteriorMinusDecayConstant_nonneg kappa
  have hphase : ‖exteriorPhase y‖ = 1 := norm_exteriorPhase hy0
  have hplus' : ‖plusOutside kappa (complexRadius y)‖ ≤
      Real.exp (-kappa.re * (‖y‖ - 1)) * exteriorPlusDecayConstant kappa := by
    simpa [complexRadius] using norm_plusOutside_le_exp hkappa hy
  have hminus' : ‖minusOutside kappa (complexRadius y)‖ ≤
      Real.exp (-kappa.re * (‖y‖ - 1)) * exteriorMinusDecayConstant kappa := by
    simpa [complexRadius] using norm_minusOutside_le_exp hkappa hy
  have hprod : ‖exteriorPhase y ^ 2 * plusOutside kappa (complexRadius y)‖ =
      ‖plusOutside kappa (complexRadius y)‖ := by
    rw [norm_mul, norm_pow, hphase, one_pow, one_mul]
  rw [hprod]
  unfold horizontalExteriorDecayConstant
  nlinarith [hplus', hminus', hE, hP, hM]

/-- The first Cartesian component of the exterior mode obeys the exponential envelope. -/
private theorem norm_horizontalExteriorField_apply_zero_le
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : 1 ≤ ‖y‖) :
    ‖horizontalExteriorField kappa y 0‖ ≤
      Real.exp (-kappa.re * (‖y‖ - 1)) * horizontalExteriorDecayConstant kappa := by
  have hsum := norm_exteriorBranches_sum_le hkappa hy
  rw [horizontalExteriorField_apply_zero, norm_div]
  norm_num only [Complex.norm_ofNat]
  calc
    ‖minusOutside kappa (complexRadius y) +
        exteriorPhase y ^ 2 * plusOutside kappa (complexRadius y)‖ / 2 ≤
        (‖minusOutside kappa (complexRadius y)‖ +
          ‖exteriorPhase y ^ 2 * plusOutside kappa (complexRadius y)‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ ≤ _ := by linarith

/-- The second Cartesian component of the exterior mode obeys the exponential envelope. -/
private theorem norm_horizontalExteriorField_apply_one_le
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : 1 ≤ ‖y‖) :
    ‖horizontalExteriorField kappa y 1‖ ≤
      Real.exp (-kappa.re * (‖y‖ - 1)) * horizontalExteriorDecayConstant kappa := by
  have hsum := norm_exteriorBranches_sum_le hkappa hy
  rw [horizontalExteriorField_apply_one, norm_div, norm_mul]
  norm_num only [Complex.norm_I, Complex.norm_ofNat, one_mul]
  calc
    ‖minusOutside kappa (complexRadius y) -
        exteriorPhase y ^ 2 * plusOutside kappa (complexRadius y)‖ / 2 ≤
        (‖minusOutside kappa (complexRadius y)‖ +
          ‖exteriorPhase y ^ 2 * plusOutside kappa (complexRadius y)‖) / 2 := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ _ := by linarith

/-- Exponential decay of the exterior two-component mode at rate `Re κ`, with the explicit
constant `2 · horizontalExteriorDecayConstant κ`.  This is the paper's "the exterior
branches and their derivatives decay exponentially" (proof of `lem:jump-horizontal-mode`). -/
theorem norm_horizontalExteriorField_le_exp
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : 1 ≤ ‖y‖) :
    ‖horizontalExteriorField kappa y‖ ≤
      2 * horizontalExteriorDecayConstant kappa *
        Real.exp (-kappa.re * (‖y‖ - 1)) := by
  set E : ℝ := Real.exp (-kappa.re * (‖y‖ - 1)) with hEdef
  set C : ℝ := horizontalExteriorDecayConstant kappa with hCdef
  have hE : (0 : ℝ) ≤ E := (Real.exp_pos _).le
  have hC : (0 : ℝ) ≤ C := horizontalExteriorDecayConstant_nonneg kappa
  have hzero : ‖horizontalExteriorField kappa y 0‖ ≤ E * C :=
    norm_horizontalExteriorField_apply_zero_le hkappa hy
  have hone : ‖horizontalExteriorField kappa y 1‖ ≤ E * C :=
    norm_horizontalExteriorField_apply_one_le hkappa hy
  have hsq : ‖horizontalExteriorField kappa y‖ ^ 2 ≤ (2 * C * E) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    nlinarith [norm_nonneg (horizontalExteriorField kappa y 0),
      norm_nonneg (horizontalExteriorField kappa y 1)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- Exponential decay of the glued mode outside the unit disk, in the repository's radial
envelope notation. -/
theorem norm_horizontalModeField_le_exp
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : 1 < ‖y‖) :
    ‖horizontalModeField kappa y‖ ≤
      2 * horizontalExteriorDecayConstant kappa *
        WholePlaneRadialExponential.radialExponentialEnvelope kappa.re y := by
  rw [horizontalModeField_of_one_lt_norm kappa hy]
  exact norm_horizontalExteriorField_le_exp hkappa hy.le

end HorizontalMode
end FastDynamo
