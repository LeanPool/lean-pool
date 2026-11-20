/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalModeBranches
public import LeanPool.FastDynamo.Local.WholePlaneSliceRadius
public import LeanPool.FastDynamo.Analysis.WholePlaneSliceProductRule
public import LeanPool.FastDynamo.Local.WholePlaneC2
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# The horizontal Ponomarenko mode in `H¹(ℝ²; ℂ²)`

The form domain of `𝔩_w` is `H¹(ℝ²;ℂ²)`, so the two-component mode built in
`Local/HorizontalModeBranches.lean` has to be realized there.  This module carries out the
corresponding step of the proof of `lem:jump-horizontal-mode` (smoothness at the origin,
exponential decay of the exterior branches and their derivatives, continuity at `r = 1`, hence
`b ∈ H¹`).

The pointwise mode is continuous across the unit circle and classically differentiable off it.
Each coordinate slice meets the circle in at most two points, so the one-dimensional
fundamental theorem of calculus applies to a Schwartz-test product away from a countable
exceptional set; the repository's slice integration-by-parts theorem then identifies the
branchwise Cartesian partials as the whole-plane weak derivatives.

Also recorded here are the two facts the witness step of the local seed needs: the mode is
non-zero in `L²` (its value at the origin is `(-K₀(κ)/2, -iK₀(κ)/2)`), and its `L²` mass
outside a disk of radius `L` decays like `e^{-(Re κ)(L-1)}`.

No weak-form, distributional, or eigenvalue claim is made here.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace HorizontalMode

open Complex Filter MeasureTheory Metric Set Topology
open scoped LineDeriv SchwartzMap
open CartesianRadialRegularity
open PonomarenkoExteriorDerivativeDecay
open PonomarenkoCartesianExteriorDerivative
open ComplexRadius
open PonomarenkoCartesianExteriorDecay
open WholePlaneSliceRadius
open PonomarenkoCrossNormalizedJump
open WholePlaneRadialExponential

/-! ## `L²` membership of the mode -/

/-- The pointwise squared norm of the glued two-component mode is integrable: continuity on
the compact closed unit disk handles the interior branch, the exponential envelope the
exterior one. -/
theorem integrable_sq_norm_horizontalModeField
    {kappa : ℂ} (hkappa : 0 < kappa.re) :
    Integrable (fun y : WholePlane ↦ ‖horizontalModeField kappa y‖ ^ 2) := by
  set f : WholePlane → ℝ := fun y ↦ ‖horizontalModeField kappa y‖ ^ 2 with hfdef
  have hfcont : Continuous f :=
    (horizontalModeField_continuous hkappa).norm.pow 2
  have hinner : IntegrableOn f (closedBall (0 : WholePlane) 1) :=
    hfcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)
  have hg : Integrable (fun y : WholePlane ↦
      (2 * horizontalExteriorDecayConstant kappa) ^ 2 *
        radialExponentialEnvelope kappa.re y ^ 2) :=
    (integrable_sq_radialExponentialEnvelope hkappa).const_mul _
  have houter : IntegrableOn f {y : WholePlane | 1 < ‖y‖} := by
    apply Integrable.mono' hg.integrableOn hfcont.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const (by fun_prop))] with y hy
    have hbound := norm_horizontalModeField_le_exp hkappa hy
    have hnonneg : (0 : ℝ) ≤ radialExponentialEnvelope kappa.re y := (Real.exp_pos _).le
    have hCnonneg : (0 : ℝ) ≤ 2 * horizontalExteriorDecayConstant kappa := by
      have := horizontalExteriorDecayConstant_nonneg kappa
      linarith
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      ‖horizontalModeField kappa y‖ ^ 2 ≤
          (2 * horizontalExteriorDecayConstant kappa *
            radialExponentialEnvelope kappa.re y) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hbound 2
      _ = (2 * horizontalExteriorDecayConstant kappa) ^ 2 *
            radialExponentialEnvelope kappa.re y ^ 2 := by ring
  have hunion : closedBall (0 : WholePlane) 1 ∪ {y : WholePlane | 1 < ‖y‖} = univ := by
    ext y
    simp only [mem_union, mem_closedBall, dist_zero_right, Set.mem_ofPred_eq, mem_univ,
      iff_true]
    exact le_or_gt ‖y‖ 1
  have hu := hinner.union houter
  rw [hunion] at hu
  simpa using hu

/-- The glued two-component mode belongs to `L²(ℝ²; ℂ²)`. -/
theorem horizontalModeField_memLp {kappa : ℂ} (hkappa : 0 < kappa.re) :
    MemLp (horizontalModeField kappa) 2 volume :=
  (memLp_two_iff_integrable_sq_norm
    (horizontalModeField_continuous hkappa).aestronglyMeasurable).2
    (integrable_sq_norm_horizontalModeField hkappa)

/-- The whole-plane `L²` value represented by the two-component Ponomarenko mode. -/
def horizontalModeL2 (kappa : ℂ) (hkappa : 0 < kappa.re) : WholePlaneC2L2 :=
  (horizontalModeField_memLp hkappa).toLp (horizontalModeField kappa)

/-- The bundled `L²` value has the pointwise mode as an almost-everywhere representative. -/
theorem horizontalModeL2_coe_ae (kappa : ℂ) (hkappa : 0 < kappa.re) :
    (horizontalModeL2 kappa hkappa : WholePlane → C2) =ᵐ[volume]
      horizontalModeField kappa :=
  MemLp.coeFn_toLp _

/-! ## Classical partial derivatives -/

/-- The classical `j`-th Cartesian partial derivative of the smooth interior field. -/
def horizontalInteriorPartialDerivative (kappa : ℂ) (j : Fin 2) (y : WholePlane) : C2 :=
  fderiv ℝ (horizontalInteriorField kappa) y (wholePlaneBasis j)

/-- The interior partial derivative is continuous on the whole plane, the field being smooth
through the removable polar axis. -/
theorem horizontalInteriorPartialDerivative_continuous (kappa : ℂ) (j : Fin 2) :
    Continuous (horizontalInteriorPartialDerivative kappa j) := by
  unfold horizontalInteriorPartialDerivative
  exact ((horizontalInteriorField_contDiff kappa).continuous_fderiv (by simp)).clm_apply
    continuous_const

/-- Componentwise differential of the exterior two-component field.  Both components are the
`N`-free ones of `Local/PonomarenkoCartesianExteriorPhysicalDerivative.lean`. -/
def horizontalExteriorComponentDerivative (kappa : ℂ) (y : WholePlane) (a : Fin 2) :
    WholePlane →L[ℝ] ℂ :=
  match a with
  | 0 => exteriorComponentZeroDerivative kappa y
  | 1 => exteriorComponentOneDerivative kappa y

/-- The full real Fréchet differential of the exterior two-component field. -/
def horizontalExteriorFieldDerivative (kappa : ℂ) (y : WholePlane) : WholePlane →L[ℝ] C2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (horizontalExteriorComponentDerivative kappa y))

/-- The packaged `j`-th Cartesian partial derivative of the exterior field. -/
def horizontalExteriorPartialDerivative (kappa : ℂ) (j : Fin 2) (y : WholePlane) : C2 :=
  horizontalExteriorFieldDerivative kappa y (wholePlaneBasis j)

/-- Exact first derivative of the first exterior Cartesian component. -/
theorem horizontalExteriorField_component_zero_hasFDerivAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) :
    HasFDerivAt (fun x : WholePlane ↦ horizontalExteriorField kappa x 0)
      (exteriorComponentZeroDerivative kappa y) y := by
  have hq := exteriorPhase_hasFDerivAt hy
  have hp := plus_branch_hasFDerivAt hkappa hy
  have hm := minus_branch_hasFDerivAt hkappa hy
  have h := (hm.add ((hq.pow 2).mul hp)).mul_const ((2 : ℂ)⁻¹)
  unfold exteriorComponentZeroDerivative
  apply h.congr_of_eventuallyEq
  refine Filter.Eventually.of_forall fun x ↦ ?_
  simp only [horizontalExteriorField_apply_zero, plusOutsideReal, minusOutsideReal,
    complexRadius, Pi.add_apply, Pi.mul_apply]
  ring

/-- Exact first derivative of the second exterior Cartesian component. -/
theorem horizontalExteriorField_component_one_hasFDerivAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) :
    HasFDerivAt (fun x : WholePlane ↦ horizontalExteriorField kappa x 1)
      (exteriorComponentOneDerivative kappa y) y := by
  have hq := exteriorPhase_hasFDerivAt hy
  have hp := plus_branch_hasFDerivAt hkappa hy
  have hm := minus_branch_hasFDerivAt hkappa hy
  have h := ((hm.sub ((hq.pow 2).mul hp)).const_mul I).mul_const ((2 : ℂ)⁻¹)
  unfold exteriorComponentOneDerivative
  apply h.congr_of_eventuallyEq
  refine Filter.Eventually.of_forall fun x ↦ ?_
  simp only [horizontalExteriorField_apply_one, plusOutsideReal, minusOutsideReal,
    complexRadius, Pi.sub_apply, Pi.mul_apply]
  ring

/-- Away from the origin the exterior two-component field is Fréchet differentiable. -/
theorem horizontalExteriorField_hasFDerivAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) :
    HasFDerivAt (horizontalExteriorField kappa)
      (horizontalExteriorFieldDerivative kappa y) y := by
  have hpi : HasFDerivAt
      (fun x : WholePlane ↦ fun a : Fin 2 ↦ horizontalExteriorField kappa x a)
      (ContinuousLinearMap.pi (horizontalExteriorComponentDerivative kappa y)) y := by
    rw [hasFDerivAt_pi]
    intro a
    fin_cases a
    · simpa [horizontalExteriorComponentDerivative] using
        horizontalExteriorField_component_zero_hasFDerivAt hkappa hy
    · simpa [horizontalExteriorComponentDerivative] using
        horizontalExteriorField_component_one_hasFDerivAt hkappa hy
  have h := (PiLp.hasFDerivAt_toLp 2
    (fun a : Fin 2 ↦ horizontalExteriorField kappa y a)).comp y hpi
  unfold horizontalExteriorFieldDerivative
  apply h.congr_of_eventuallyEq
  refine Filter.Eventually.of_forall fun x ↦ ?_
  apply PiLp.ext
  intro a
  simp

/-- The packaged exterior partial derivative is the Fréchet derivative in the coordinate
direction. -/
theorem horizontalExteriorPartialDerivative_eq_fderiv
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : y ≠ 0) (j : Fin 2) :
    horizontalExteriorPartialDerivative kappa j y =
      fderiv ℝ (horizontalExteriorField kappa) y (wholePlaneBasis j) := by
  rw [(horizontalExteriorField_hasFDerivAt hkappa hy).fderiv]
  rfl

/-- First component of the exterior Cartesian partial derivative. -/
@[simp] theorem horizontalExteriorPartialDerivative_apply_zero
    (kappa : ℂ) (j : Fin 2) (y : WholePlane) :
    horizontalExteriorPartialDerivative kappa j y 0 =
      exteriorComponentZeroDerivative kappa y (wholePlaneBasis j) := by
  simp [horizontalExteriorPartialDerivative, horizontalExteriorFieldDerivative,
    horizontalExteriorComponentDerivative]

/-- Second component of the exterior Cartesian partial derivative. -/
@[simp] theorem horizontalExteriorPartialDerivative_apply_one
    (kappa : ℂ) (j : Fin 2) (y : WholePlane) :
    horizontalExteriorPartialDerivative kappa j y 1 =
      exteriorComponentOneDerivative kappa y (wholePlaneBasis j) := by
  simp [horizontalExteriorPartialDerivative, horizontalExteriorFieldDerivative,
    horizontalExteriorComponentDerivative]

/-! ## Exponential decay of the exterior derivative -/

/-- Envelope constant for the exterior derivative of the two-component mode.  It is the
constant of the Cartesian Ponomarenko field (`Local/PonomarenkoExteriorDerivativeDecay.lean`)
evaluated at the dummy axial wavenumber `1`;
only its finiteness and nonnegativity are ever used. -/
def horizontalExteriorDerivativeConstant (kappa : ℂ) : ℝ :=
  derivativeConstant 1 kappa

/-- The exterior derivative envelope constant is nonnegative. -/
theorem horizontalExteriorDerivativeConstant_nonneg (kappa : ℂ) :
    0 ≤ horizontalExteriorDerivativeConstant kappa :=
  derivativeConstant_nonneg 1 kappa

/-- Exponential decay of the exterior Cartesian partial derivative at rate `Re κ`. -/
theorem norm_horizontalExteriorPartialDerivative_le_exp
    {kappa : ℂ} (hkappa : 0 < kappa.re) (j : Fin 2) {y : WholePlane} (hy : 1 ≤ ‖y‖) :
    ‖horizontalExteriorPartialDerivative kappa j y‖ ≤
      2 * horizontalExteriorDerivativeConstant kappa *
        radialExponentialEnvelope kappa.re y := by
  set E : ℝ := radialExponentialEnvelope kappa.re y with hEdef
  set C : ℝ := horizontalExteriorDerivativeConstant kappa with hCdef
  have hE : (0 : ℝ) ≤ E := (Real.exp_pos _).le
  have hC : (0 : ℝ) ≤ C := horizontalExteriorDerivativeConstant_nonneg kappa
  have hzero : ‖horizontalExteriorPartialDerivative kappa j y 0‖ ≤ E * C := by
    rw [horizontalExteriorPartialDerivative_apply_zero]
    simpa [hEdef, hCdef, radialExponentialEnvelope, horizontalExteriorDerivativeConstant]
      using norm_exteriorComponentZeroDerivative_le_exp 1 hkappa j hy
  have hone : ‖horizontalExteriorPartialDerivative kappa j y 1‖ ≤ E * C := by
    rw [horizontalExteriorPartialDerivative_apply_one]
    simpa [hEdef, hCdef, radialExponentialEnvelope, horizontalExteriorDerivativeConstant]
      using norm_exteriorComponentOneDerivative_le_exp 1 hkappa j hy
  have hsq : ‖horizontalExteriorPartialDerivative kappa j y‖ ^ 2 ≤ (2 * C * E) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    nlinarith [norm_nonneg (horizontalExteriorPartialDerivative kappa j y 0),
      norm_nonneg (horizontalExteriorPartialDerivative kappa j y 1)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- On the unit exterior the exterior partial derivative is almost everywhere strongly
measurable. -/
theorem horizontalExteriorPartialDerivative_aestronglyMeasurable
    {kappa : ℂ} (hkappa : 0 < kappa.re) (j : Fin 2) :
    AEStronglyMeasurable (horizontalExteriorPartialDerivative kappa j)
      (volume.restrict unitExterior) := by
  have hfd : AEStronglyMeasurable
      (fun y : WholePlane ↦
        fderiv ℝ (horizontalExteriorField kappa) y (wholePlaneBasis j))
      (volume.restrict unitExterior) :=
    (measurable_fderiv_apply_const ℝ
      (horizontalExteriorField kappa) (wholePlaneBasis j)).aestronglyMeasurable.restrict
  apply hfd.congr
  filter_upwards [ae_restrict_mem measurableSet_unitExterior] with y hy
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hy
    norm_num [unitExterior] at hy
  exact (horizontalExteriorPartialDerivative_eq_fderiv hkappa hy0 j).symm

/-- The exterior partial derivative is square integrable outside the unit disk. -/
theorem horizontalExteriorPartialDerivative_memLp_two_unitExterior
    {kappa : ℂ} (hkappa : 0 < kappa.re) (j : Fin 2) :
    MemLp (horizontalExteriorPartialDerivative kappa j) 2
      (volume.restrict unitExterior) := by
  refine memLp_two_unitExterior_of_norm_le_radialExponential
    (C := 2 * horizontalExteriorDerivativeConstant kappa) hkappa
    (horizontalExteriorPartialDerivative_aestronglyMeasurable hkappa j) ?_
  filter_upwards [ae_restrict_mem measurableSet_unitExterior] with y hy
  exact norm_horizontalExteriorPartialDerivative_le_exp hkappa j hy

/-! ## The branchwise derivative representative -/

/-- The branchwise Cartesian derivative representative: the interior classical partial on the
closed unit disk, the exterior classical partial outside it. -/
def horizontalModePartialDerivative (kappa : ℂ) (j : Fin 2) (y : WholePlane) : C2 :=
  if ‖y‖ ≤ 1 then horizontalInteriorPartialDerivative kappa j y
  else horizontalExteriorPartialDerivative kappa j y

/-- On the closed unit disk the derivative representative is the interior classical partial. -/
@[simp] theorem horizontalModePartialDerivative_of_norm_le
    (kappa : ℂ) (j : Fin 2) {y : WholePlane} (hy : ‖y‖ ≤ 1) :
    horizontalModePartialDerivative kappa j y =
      horizontalInteriorPartialDerivative kappa j y := by
  simp [horizontalModePartialDerivative, hy]

/-- Strictly inside the disk the derivative representative is the interior classical
partial. -/
@[simp] theorem horizontalModePartialDerivative_of_norm_lt_one
    (kappa : ℂ) (j : Fin 2) {y : WholePlane} (hy : ‖y‖ < 1) :
    horizontalModePartialDerivative kappa j y =
      horizontalInteriorPartialDerivative kappa j y :=
  horizontalModePartialDerivative_of_norm_le kappa j hy.le

/-- Strictly outside the circle the derivative representative is the exterior classical
partial. -/
@[simp] theorem horizontalModePartialDerivative_of_one_lt_norm
    (kappa : ℂ) (j : Fin 2) {y : WholePlane} (hy : 1 < ‖y‖) :
    horizontalModePartialDerivative kappa j y =
      horizontalExteriorPartialDerivative kappa j y := by
  simp [horizontalModePartialDerivative, not_le_of_gt hy]

/-- The branchwise derivative representative is square integrable on the whole plane. -/
theorem horizontalModePartialDerivative_memLp
    {kappa : ℂ} (hkappa : 0 < kappa.re) (j : Fin 2) :
    MemLp (horizontalModePartialDerivative kappa j) 2 volume := by
  classical
  have hs : MeasurableSet (closedBall (0 : WholePlane) 1) :=
    isClosed_closedBall.measurableSet
  have hinter : MemLp (horizontalInteriorPartialDerivative kappa j) 2
      (volume.restrict (closedBall (0 : WholePlane) 1)) := by
    apply (memLp_two_iff_integrable_sq_norm
      (horizontalInteriorPartialDerivative_continuous kappa j).aestronglyMeasurable).2
    exact (((horizontalInteriorPartialDerivative_continuous kappa j).norm.pow
      2).continuousOn).integrableOn_compact (isCompact_closedBall (0 : WholePlane) 1)
  have hsub : (closedBall (0 : WholePlane) 1)ᶜ ⊆ unitExterior := by
    intro y hy
    have hy' : ¬ ‖y‖ ≤ 1 := by
      simpa [mem_closedBall, dist_zero_right] using hy
    exact le_of_lt (lt_of_not_ge hy')
  have hexterior : MemLp (horizontalExteriorPartialDerivative kappa j) 2
      (volume.restrict (closedBall (0 : WholePlane) 1)ᶜ) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hsub)
      (horizontalExteriorPartialDerivative_memLp_two_unitExterior hkappa j)
  have hp : MemLp
      ((closedBall (0 : WholePlane) 1).piecewise
        (horizontalInteriorPartialDerivative kappa j)
        (horizontalExteriorPartialDerivative kappa j)) 2
      (volume : Measure WholePlane) :=
    MemLp.piecewise hs.nullMeasurableSet hinter hexterior
  apply hp.ae_eq
  filter_upwards with y
  by_cases hy : ‖y‖ ≤ 1
  · simp [horizontalModePartialDerivative, Set.piecewise, mem_closedBall,
      dist_zero_right, hy]
  · simp [horizontalModePartialDerivative, Set.piecewise, mem_closedBall,
      dist_zero_right, hy]

/-- The two branchwise Cartesian derivative representatives, bundled in `L²(ℝ²; ℂ²)`. -/
def horizontalModePartialDerivativeL2 (kappa : ℂ) (hkappa : 0 < kappa.re) :
    Fin 2 → WholePlaneC2L2 :=
  fun j ↦ (horizontalModePartialDerivative_memLp hkappa j).toLp
    (horizontalModePartialDerivative kappa j)

/-- The bundled derivative has the branchwise classical partial as a representative. -/
theorem horizontalModePartialDerivativeL2_coe_ae
    (kappa : ℂ) (hkappa : 0 < kappa.re) (j : Fin 2) :
    (horizontalModePartialDerivativeL2 kappa hkappa j : WholePlane → C2) =ᵐ[volume]
      horizontalModePartialDerivative kappa j :=
  MemLp.coeFn_toLp _

/-! ## Classical derivatives of the glued mode off the interface -/

/-- Strictly inside the unit circle the glued mode has the interior classical derivative. -/
theorem horizontalModeField_hasFDerivAt_of_norm_lt_one
    (kappa : ℂ) {y : WholePlane} (hy : ‖y‖ < 1) :
    HasFDerivAt (horizontalModeField kappa)
      (fderiv ℝ (horizontalInteriorField kappa) y) y := by
  have hi : HasFDerivAt (horizontalInteriorField kappa)
      (fderiv ℝ (horizontalInteriorField kappa) y) y :=
    ((horizontalInteriorField_contDiff kappa).differentiable (by simp) y).hasFDerivAt
  have hnhds : {x : WholePlane | ‖x‖ < 1} ∈ nhds y :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hy
  apply hi.congr_of_eventuallyEq
  filter_upwards [hnhds] with x hx
  exact horizontalModeField_of_norm_le kappa hx.le

/-- Strictly outside the unit circle the glued mode has the exterior classical derivative. -/
theorem horizontalModeField_hasFDerivAt_of_one_lt_norm
    {kappa : ℂ} (hkappa : 0 < kappa.re) {y : WholePlane} (hy : 1 < ‖y‖) :
    HasFDerivAt (horizontalModeField kappa)
      (horizontalExteriorFieldDerivative kappa y) y := by
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hy
    norm_num at hy
  have ho := horizontalExteriorField_hasFDerivAt hkappa hy0
  have hnhds : {x : WholePlane | 1 < ‖x‖} ∈ nhds y :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hy
  apply ho.congr_of_eventuallyEq
  filter_upwards [hnhds] with x hx
  exact horizontalModeField_of_one_lt_norm kappa hx

/-! ## Slice limits -/

/-- Whenever the radius along a slice tends to infinity, the two-component mode tends to zero,
by the exponential majorant of the decaying branches. -/
private theorem horizontalModeField_along_slice_tendsto_zero
    {l : Filter ℝ} {kappa : ℂ} (hkappa : 0 < kappa.re) (j : Fin 2) (x : ℝ)
    (hr : Tendsto (fun t : ℝ ↦ ‖wholePlaneSliceEquiv j (x, t)‖) l atTop) :
    Tendsto (fun t : ℝ ↦ horizontalModeField kappa (wholePlaneSliceEquiv j (x, t)))
      l (nhds 0) := by
  have hshift : Tendsto
      (fun t : ℝ ↦ ‖wholePlaneSliceEquiv j (x, t)‖ - 1) l atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-1 : ℝ) hr
  have harg : Tendsto
      (fun t : ℝ ↦ -kappa.re * (‖wholePlaneSliceEquiv j (x, t)‖ - 1)) l atBot :=
    hshift.const_mul_atTop_of_neg (neg_lt_zero.mpr hkappa)
  have hexp : Tendsto
      (fun t : ℝ ↦ radialExponentialEnvelope kappa.re
        (wholePlaneSliceEquiv j (x, t))) l (nhds 0) :=
    Real.tendsto_exp_atBot.comp harg
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun t : ℝ ↦ 2 * horizontalExteriorDecayConstant kappa *
      radialExponentialEnvelope kappa.re (wholePlaneSliceEquiv j (x, t)))
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [hr (eventually_gt_atTop 1)] with t ht
    exact norm_horizontalModeField_le_exp hkappa ht
  · simpa only [mul_zero] using
      hexp.const_mul (2 * horizontalExteriorDecayConstant kappa)

/-- The mode tends to zero at the `+∞` end of every coordinate slice. -/
theorem tendsto_horizontalModeField_slice_atTop
    {kappa : ℂ} (hkappa : 0 < kappa.re) (j : Fin 2) (x : ℝ) :
    Tendsto (fun t : ℝ ↦ horizontalModeField kappa (wholePlaneSliceEquiv j (x, t)))
      atTop (nhds 0) :=
  horizontalModeField_along_slice_tendsto_zero hkappa j x
    (tendsto_norm_wholePlaneSliceEquiv_atTop j x)

/-- The mode tends to zero at the `-∞` end of every coordinate slice. -/
theorem tendsto_horizontalModeField_slice_atBot
    {kappa : ℂ} (hkappa : 0 < kappa.re) (j : Fin 2) (x : ℝ) :
    Tendsto (fun t : ℝ ↦ horizontalModeField kappa (wholePlaneSliceEquiv j (x, t)))
      atBot (nhds 0) :=
  horizontalModeField_along_slice_tendsto_zero hkappa j x
    (tendsto_norm_wholePlaneSliceEquiv_atBot j x)

/-- Multiplication by a Schwartz test function preserves decay along a slice. -/
private theorem tendsto_schwartz_smul_horizontalModeField_slice_zero
    {l : Filter ℝ} (kappa : ℂ) (phi : SchwartzMap WholePlane ℂ) (j : Fin 2) (x : ℝ)
    (hu : Tendsto (fun t : ℝ ↦ horizontalModeField kappa (wholePlaneSliceEquiv j (x, t)))
      l (nhds 0)) :
    Tendsto (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
      horizontalModeField kappa (wholePlaneSliceEquiv j (x, t))) l (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun t : ℝ ↦ (SchwartzMap.seminorm ℝ 0 0) phi *
      ‖horizontalModeField kappa (wholePlaneSliceEquiv j (x, t))‖)
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · refine Filter.Eventually.of_forall fun t ↦ ?_
    simpa only [norm_smul] using mul_le_mul_of_nonneg_right
      (SchwartzMap.norm_le_seminorm ℝ phi (wholePlaneSliceEquiv j (x, t)))
      (norm_nonneg _)
  · have hnorm := tendsto_zero_iff_norm_tendsto_zero.mp hu
    simpa only [mul_zero] using hnorm.const_mul ((SchwartzMap.seminorm ℝ 0 0) phi)

/-- The Schwartz-weighted mode vanishes at the `+∞` end of every slice. -/
theorem tendsto_schwartz_smul_horizontalModeField_slice_atTop
    {kappa : ℂ} (hkappa : 0 < kappa.re) (phi : SchwartzMap WholePlane ℂ)
    (j : Fin 2) (x : ℝ) :
    Tendsto (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
      horizontalModeField kappa (wholePlaneSliceEquiv j (x, t))) atTop (nhds 0) :=
  tendsto_schwartz_smul_horizontalModeField_slice_zero kappa phi j x
    (tendsto_horizontalModeField_slice_atTop hkappa j x)

/-- The Schwartz-weighted mode vanishes at the `-∞` end of every slice. -/
theorem tendsto_schwartz_smul_horizontalModeField_slice_atBot
    {kappa : ℂ} (hkappa : 0 < kappa.re) (phi : SchwartzMap WholePlane ℂ)
    (j : Fin 2) (x : ℝ) :
    Tendsto (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
      horizontalModeField kappa (wholePlaneSliceEquiv j (x, t))) atBot (nhds 0) :=
  tendsto_schwartz_smul_horizontalModeField_slice_zero kappa phi j x
    (tendsto_horizontalModeField_slice_atBot hkappa j x)

/-- Every Schwartz-test product is continuous on every coordinate slice. -/
theorem continuous_schwartz_smul_horizontalModeField_slice
    {kappa : ℂ} (hkappa : 0 < kappa.re) (phi : SchwartzMap WholePlane ℂ)
    (j : Fin 2) (x : ℝ) :
    Continuous (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
      horizontalModeField kappa (wholePlaneSliceEquiv j (x, t))) := by
  have hs := wholePlaneSliceEquiv_continuous j x
  exact (phi.continuous.comp hs).smul ((horizontalModeField_continuous hkappa).comp hs)

/-! ## Weak derivatives and the `H¹` mode -/

/-- Away from the finitely many intersections of a coordinate slice with the unit circle, the
derivative of a Schwartz-test product is the branchwise product rule. -/
theorem hasDerivAt_schwartz_smul_horizontalModeField_slice
    {kappa : ℂ} (hkappa : 0 < kappa.re) (phi : SchwartzMap WholePlane ℂ)
    (j : Fin 2) (x t : ℝ) (ht : t ∉ wholePlaneUnitCircleSliceExceptional j x) :
    HasDerivAt
      (fun v : ℝ ↦ phi (wholePlaneSliceEquiv j (x, v)) •
        horizontalModeField kappa (wholePlaneSliceEquiv j (x, v)))
      (((∂_{wholePlaneBasis j} phi) (wholePlaneSliceEquiv j (x, t))) •
          horizontalModeField kappa (wholePlaneSliceEquiv j (x, t)) +
        phi (wholePlaneSliceEquiv j (x, t)) •
          horizontalModePartialDerivative kappa j
            (wholePlaneSliceEquiv j (x, t))) t := by
  set y : WholePlane := wholePlaneSliceEquiv j (x, t) with hydef
  have hy_ne : ‖y‖ ≠ 1 := fun hy ↦ ht hy
  rcases lt_or_gt_of_ne hy_ne with hy | hy
  · have hfield := horizontalModeField_hasFDerivAt_of_norm_lt_one kappa hy
    have hproduct := hasDerivAt_schwartz_smul_wholePlaneSliceEquiv
      phi (horizontalModeField kappa)
      (fderiv ℝ (horizontalInteriorField kappa) y) j x t hfield
    simpa only [← hydef, horizontalModePartialDerivative_of_norm_lt_one kappa j hy,
      horizontalInteriorPartialDerivative] using hproduct
  · have hfield := horizontalModeField_hasFDerivAt_of_one_lt_norm hkappa hy
    have hproduct := hasDerivAt_schwartz_smul_wholePlaneSliceEquiv
      phi (horizontalModeField kappa)
      (horizontalExteriorFieldDerivative kappa y) j x t hfield
    simpa only [← hydef, horizontalModePartialDerivative_of_one_lt_norm kappa j hy,
      horizontalExteriorPartialDerivative] using hproduct

/-- The branchwise Cartesian partial is the whole-plane weak derivative of the mode. -/
theorem horizontalModeField_hasWholePlaneIntegralWeakDerivative
    {kappa : ℂ} (hkappa : 0 < kappa.re) (j : Fin 2) :
    HasWholePlaneIntegralWeakDerivative
      (horizontalModeL2 kappa hkappa)
      (horizontalModePartialDerivativeL2 kappa hkappa j) j := by
  apply hasWholePlaneIntegralWeakDerivative_of_ae_fiberwise_product
    (u := horizontalModeField kappa)
    (du := horizontalModePartialDerivative kappa j)
  · exact (horizontalModeL2_coe_ae kappa hkappa).symm
  · exact (horizontalModePartialDerivativeL2_coe_ae kappa hkappa j).symm
  · intro phi x
    exact continuous_schwartz_smul_horizontalModeField_slice hkappa phi j x
  · intro phi x
    refine ⟨wholePlaneUnitCircleSliceExceptional j x,
      countable_wholePlaneUnitCircleSliceExceptional j x, ?_⟩
    intro t ht
    exact hasDerivAt_schwartz_smul_horizontalModeField_slice hkappa phi j x t ht
  · intro phi x
    exact tendsto_schwartz_smul_horizontalModeField_slice_atBot hkappa phi j x
  · intro phi x
    exact tendsto_schwartz_smul_horizontalModeField_slice_atTop hkappa phi j x

/-- The two-component Ponomarenko mode as an element of `H¹(ℝ²; ℂ²)`. -/
def horizontalModeH1 (kappa : ℂ) (hkappa : 0 < kappa.re) : WholePlaneC2H1 :=
  wholePlaneH1OfIntegralWeakDerivatives
    (horizontalModeL2 kappa hkappa)
    (horizontalModePartialDerivativeL2 kappa hkappa)
    (horizontalModeField_hasWholePlaneIntegralWeakDerivative hkappa)

/-- The `L²` value projection of the `H¹` mode is the packaged pointwise mode. -/
theorem wholePlaneH1Embedding_horizontalModeH1 (kappa : ℂ) (hkappa : 0 < kappa.re) :
    wholePlaneH1Embedding C2 (horizontalModeH1 kappa hkappa) =
      horizontalModeL2 kappa hkappa :=
  rfl

/-- The `j`-th weak derivative of the `H¹` mode is the packaged branchwise partial. -/
theorem wholePlaneH1FirstDerivative_horizontalModeH1
    (kappa : ℂ) (hkappa : 0 < kappa.re) (j : Fin 2) :
    wholePlaneH1FirstDerivative C2 j (horizontalModeH1 kappa hkappa) =
      horizontalModePartialDerivativeL2 kappa hkappa j :=
  rfl

/-! ## Non-vanishing -/

/-- The `L²` mode is non-zero whenever `K₀(κ) ≠ 0`.

The witness is the value at the origin.  Equality of the bundled `L²` class with zero would
make the continuous concrete representative vanish everywhere, but its first component at the
origin is `-K₀(κ)/2`. -/
theorem horizontalModeL2_ne_zero
    {kappa : ℂ} (hkappa : 0 < kappa.re) (hK0 : ModifiedBessel.K0 kappa ≠ 0) :
    horizontalModeL2 kappa hkappa ≠ 0 := by
  intro hzero
  have hrepresentative := horizontalModeL2_coe_ae kappa hkappa
  rw [hzero] at hrepresentative
  have hae : horizontalModeField kappa =ᵐ[volume] (fun _ : WholePlane ↦ (0 : C2)) :=
    hrepresentative.symm.trans (Lp.coeFn_zero C2 2 (volume : Measure WholePlane))
  have hpointwise : horizontalModeField kappa = fun _ : WholePlane ↦ (0 : C2) :=
    MeasureTheory.Measure.eq_of_ae_eq hae
      (horizontalModeField_continuous hkappa) continuous_const
  have horigin := congrFun hpointwise (0 : WholePlane)
  have hfirst := congrArg (fun z : C2 ↦ z (0 : Fin 2)) horigin
  rw [horizontalModeField_zero] at hfirst
  apply hK0
  simpa using hfirst

/-- The `H¹` mode itself is non-zero whenever `K₀(κ) ≠ 0`. -/
theorem horizontalModeH1_ne_zero
    {kappa : ℂ} (hkappa : 0 < kappa.re) (hK0 : ModifiedBessel.K0 kappa ≠ 0) :
    horizontalModeH1 kappa hkappa ≠ 0 := by
  intro hzero
  apply horizontalModeL2_ne_zero hkappa hK0
  rw [← wholePlaneH1Embedding_horizontalModeH1 kappa hkappa, hzero, map_zero]

/-! ## Exponential tail outside a large disk -/

/-- The radial exponential envelope is integrable on the plane, being the square of the
envelope at half the rate. -/
theorem integrable_radialExponentialEnvelope {a : ℝ} (ha : 0 < a) :
    Integrable (radialExponentialEnvelope a) := by
  have h := integrable_sq_radialExponentialEnvelope (half_pos ha)
  apply h.congr
  filter_upwards with y
  rw [radialExponentialEnvelope, radialExponentialEnvelope, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The explicit constant in the exponential `L²` tail bound of the mode. -/
def horizontalModeTailConstant (kappa : ℂ) : ℝ :=
  (2 * horizontalExteriorDecayConstant kappa) ^ 2 *
    ∫ y : WholePlane, radialExponentialEnvelope kappa.re y

/-- Explicit exponential tail bound: the `L²` mass of the mode outside the disk of radius `L`
is at most `horizontalModeTailConstant κ · e^{-(Re κ)(L-1)}`.

This is the quantitative form of the paper's exponential decay (proof of
`lem:jump-horizontal-mode`), in the shape
needed by the truncation `f_* = χ b/‖b‖` of the local-seed witness step. -/
theorem integral_sq_norm_horizontalModeField_tail_le
    {kappa : ℂ} (hkappa : 0 < kappa.re) {L : ℝ} (hL : 1 ≤ L) :
    ∫ y in {y : WholePlane | L ≤ ‖y‖}, ‖horizontalModeField kappa y‖ ^ 2 ≤
      horizontalModeTailConstant kappa * Real.exp (-kappa.re * (L - 1)) := by
  have hC : (0 : ℝ) ≤ 2 * horizontalExteriorDecayConstant kappa := by
    have := horizontalExteriorDecayConstant_nonneg kappa
    linarith
  have hmeas : MeasurableSet {y : WholePlane | L ≤ ‖y‖} :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hintegrable : Integrable (fun y : WholePlane ↦
      (2 * horizontalExteriorDecayConstant kappa) ^ 2 * Real.exp (-kappa.re * (L - 1)) *
        radialExponentialEnvelope kappa.re y) :=
    (integrable_radialExponentialEnvelope hkappa).const_mul _
  have hself : IntegrableOn (fun y : WholePlane ↦ ‖horizontalModeField kappa y‖ ^ 2)
      {y : WholePlane | L ≤ ‖y‖} :=
    (integrable_sq_norm_horizontalModeField hkappa).integrableOn
  have hpointwise : ∀ y ∈ {y : WholePlane | L ≤ ‖y‖},
      ‖horizontalModeField kappa y‖ ^ 2 ≤
        (2 * horizontalExteriorDecayConstant kappa) ^ 2 *
          Real.exp (-kappa.re * (L - 1)) * radialExponentialEnvelope kappa.re y := by
    intro y hy
    have hyL : L ≤ ‖y‖ := hy
    have hbound : ‖horizontalModeField kappa y‖ ≤
        2 * horizontalExteriorDecayConstant kappa *
          radialExponentialEnvelope kappa.re y := by
      rcases lt_or_eq_of_le (hL.trans hyL) with h | h
      · exact norm_horizontalModeField_le_exp hkappa h
      · rw [horizontalModeField_of_norm_le kappa h.ge,
          horizontalInteriorField_eq_exteriorField_of_norm_eq_one kappa h.symm]
        exact norm_horizontalExteriorField_le_exp hkappa h.le
    have hsplit : radialExponentialEnvelope kappa.re y ^ 2 ≤
        Real.exp (-kappa.re * (L - 1)) * radialExponentialEnvelope kappa.re y := by
      rw [radialExponentialEnvelope, pow_two, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [hkappa, hyL]
    calc
      ‖horizontalModeField kappa y‖ ^ 2 ≤
          (2 * horizontalExteriorDecayConstant kappa *
            radialExponentialEnvelope kappa.re y) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbound 2
      _ = (2 * horizontalExteriorDecayConstant kappa) ^ 2 *
            radialExponentialEnvelope kappa.re y ^ 2 := by ring
      _ ≤ (2 * horizontalExteriorDecayConstant kappa) ^ 2 *
            (Real.exp (-kappa.re * (L - 1)) * radialExponentialEnvelope kappa.re y) :=
        mul_le_mul_of_nonneg_left hsplit (sq_nonneg _)
      _ = (2 * horizontalExteriorDecayConstant kappa) ^ 2 *
            Real.exp (-kappa.re * (L - 1)) * radialExponentialEnvelope kappa.re y := by
        ring
  calc
    ∫ y in {y : WholePlane | L ≤ ‖y‖}, ‖horizontalModeField kappa y‖ ^ 2 ≤
        ∫ y in {y : WholePlane | L ≤ ‖y‖},
          (2 * horizontalExteriorDecayConstant kappa) ^ 2 *
            Real.exp (-kappa.re * (L - 1)) * radialExponentialEnvelope kappa.re y :=
      setIntegral_mono_on hself hintegrable.integrableOn hmeas hpointwise
    _ ≤ ∫ y : WholePlane, (2 * horizontalExteriorDecayConstant kappa) ^ 2 *
          Real.exp (-kappa.re * (L - 1)) * radialExponentialEnvelope kappa.re y := by
        apply setIntegral_le_integral hintegrable
        filter_upwards with y
        have h1 : (0 : ℝ) ≤ radialExponentialEnvelope kappa.re y := (Real.exp_pos _).le
        have h2 : (0 : ℝ) ≤ Real.exp (-kappa.re * (L - 1)) := (Real.exp_pos _).le
        exact mul_nonneg (mul_nonneg (sq_nonneg _) h2) h1
    _ = horizontalModeTailConstant kappa * Real.exp (-kappa.re * (L - 1)) := by
        rw [integral_const_mul, horizontalModeTailConstant]
        ring

end HorizontalMode
end FastDynamo
