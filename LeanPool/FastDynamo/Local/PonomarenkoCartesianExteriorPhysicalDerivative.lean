/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.PonomarenkoCartesianExteriorDerivative

/-!
# Physical component derivatives of the exterior Ponomarenko branches

The Cartesian first derivatives of the two transverse exterior branch fields of
`FastDynamo/Local/PonomarenkoCartesianExteriorDerivative.lean`, assembled from the radius and
phase differentials and the exact real-radial derivatives proved there: the radial branch
differentials `plusBranchDerivative`, `minusBranchDerivative`, their coordinate bounds and
Fréchet derivatives (`plus_branch_hasFDerivAt`, `minus_branch_hasFDerivAt`), and the component
derivatives `exteriorComponentZeroDerivative`, `exteriorComponentOneDerivative`.  These are
consumed by `Local/PonomarenkoExteriorDerivativeDecay.lean` (their exponential decay) and
`Local/HorizontalModeH1.lean` (the `H¹` membership of the two-component mode).

This is a separate module from `FastDynamo/Local/PonomarenkoCartesianExteriorDerivative.lean`,
which has many dependents; nothing in that module refers to the declarations below.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace PonomarenkoCartesianExteriorDerivative

open Complex Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace
open PonomarenkoCrossNormalizedJump
open PonomarenkoCrossNormalizedAxial
open ComplexRadius
open CartesianRadialRegularity
open ModifiedBesselBoundaryBehavior
open ModifiedBesselDerivativeDecay

/-! ## Physical component derivatives -/

/-- The radial differential of the order-two exterior branch. -/
def plusBranchDerivative (kappa : ℂ) (y : WholePlane) : WholePlane →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℝ
    (deriv (plusOutsideReal kappa) ‖y‖)).comp (radiusDerivative y)

/-- The radial differential of the order-zero exterior branch. -/
def minusBranchDerivative (kappa : ℂ) (y : WholePlane) : WholePlane →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℝ
    (deriv (minusOutsideReal kappa) ‖y‖)).comp (radiusDerivative y)

/-- Evaluation of the order-two branch differential: the radius differential times the
one-dimensional radial derivative. -/
@[simp] theorem plusBranchDerivative_apply
    (kappa : ℂ) (y v : WholePlane) :
    plusBranchDerivative kappa y v =
      radiusDerivative y v • deriv (plusOutsideReal kappa) ‖y‖ := by
  simp [plusBranchDerivative]

/-- Evaluation of the order-zero branch differential: the radius differential times the
one-dimensional radial derivative. -/
@[simp] theorem minusBranchDerivative_apply
    (kappa : ℂ) (y v : WholePlane) :
    minusBranchDerivative kappa y v =
      radiusDerivative y v • deriv (minusOutsideReal kappa) ‖y‖ := by
  simp [minusBranchDerivative]

/-- A radial branch differential in a coordinate direction is no larger than
the corresponding one-dimensional radial derivative. -/
theorem norm_plusBranchDerivative_basis_le {y : WholePlane} (hy : y ≠ 0)
    (kappa : ℂ) (j : Fin 2) :
    ‖plusBranchDerivative kappa y (wholePlaneBasis j)‖ ≤
      ‖deriv (plusOutsideReal kappa) ‖y‖‖ := by
  rw [plusBranchDerivative_apply, norm_smul]
  have hcoord : |y j| ≤ ‖y‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y j
  have hrpos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  rw [radiusDerivative_apply, inner_wholePlaneBasis, Real.norm_eq_abs,
    abs_div, abs_of_nonneg (norm_nonneg y)]
  have hratio : |y j| / ‖y‖ ≤ 1 := (div_le_one (norm_pos_iff.mpr hy)).mpr hcoord
  nlinarith [norm_nonneg (deriv (plusOutsideReal kappa) ‖y‖)]

/-- A coordinate direction picks up at most the full one-dimensional radial derivative of the
order-zero branch, since `|yⱼ| ≤ ‖y‖`. -/
theorem norm_minusBranchDerivative_basis_le {y : WholePlane} (hy : y ≠ 0)
    (kappa : ℂ) (j : Fin 2) :
    ‖minusBranchDerivative kappa y (wholePlaneBasis j)‖ ≤
      ‖deriv (minusOutsideReal kappa) ‖y‖‖ := by
  rw [minusBranchDerivative_apply, norm_smul]
  have hcoord : |y j| ≤ ‖y‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y j
  have hratio : |y j| / ‖y‖ ≤ 1 :=
    (div_le_one (norm_pos_iff.mpr hy)).mpr hcoord
  rw [radiusDerivative_apply, inner_wholePlaneBasis, Real.norm_eq_abs,
    abs_div, abs_of_nonneg (norm_nonneg y)]
  nlinarith [norm_nonneg (deriv (minusOutsideReal kappa) ‖y‖)]

/-- Away from the origin the radial composition `x ↦ B₊(‖x‖)` is Fréchet differentiable with
differential `plusBranchDerivative kappa y`. -/
theorem plus_branch_hasFDerivAt {kappa : ℂ} (hkappa : 0 < kappa.re)
    {y : WholePlane} (hy : y ≠ 0) :
    HasFDerivAt (fun x : WholePlane ↦ plusOutsideReal kappa ‖x‖)
      (plusBranchDerivative kappa y) y := by
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hp := plusOutsideReal_hasDerivAt hkappa hr
  unfold plusBranchDerivative
  rw [hp.deriv]
  exact hp.hasFDerivAt.comp y (radius_hasFDerivAt hy)

/-- Away from the origin the radial composition `x ↦ B₋(‖x‖)` is Fréchet differentiable with
differential `minusBranchDerivative kappa y`. -/
theorem minus_branch_hasFDerivAt {kappa : ℂ} (hkappa : 0 < kappa.re)
    {y : WholePlane} (hy : y ≠ 0) :
    HasFDerivAt (fun x : WholePlane ↦ minusOutsideReal kappa ‖x‖)
      (minusBranchDerivative kappa y) y := by
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hm := minusOutsideReal_hasDerivAt hkappa hr
  unfold minusBranchDerivative
  rw [hm.deriv]
  exact hm.hasFDerivAt.comp y (radius_hasFDerivAt hy)

/-- Differential of the first exterior Cartesian component. -/
def exteriorComponentZeroDerivative (kappa : ℂ)
    (y : WholePlane) : WholePlane →L[ℝ] ℂ :=
  (2 : ℂ)⁻¹ • (minusBranchDerivative kappa y +
    (exteriorPhase y ^ 2 • plusBranchDerivative kappa y +
      plusOutsideReal kappa ‖y‖ •
        (2 • exteriorPhase y ^ (2 - 1)) • exteriorPhaseDerivative y))

/-- Differential of the second exterior Cartesian component. -/
def exteriorComponentOneDerivative (kappa : ℂ)
    (y : WholePlane) : WholePlane →L[ℝ] ℂ :=
  (2 : ℂ)⁻¹ • I • (minusBranchDerivative kappa y -
    (exteriorPhase y ^ 2 • plusBranchDerivative kappa y +
      plusOutsideReal kappa ‖y‖ •
        (2 • exteriorPhase y ^ (2 - 1)) • exteriorPhaseDerivative y))

end PonomarenkoCartesianExteriorDerivative
end FastDynamo
