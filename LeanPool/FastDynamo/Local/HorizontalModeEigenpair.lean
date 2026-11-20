/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneUnitDiskFibreBranches
public import LeanPool.FastDynamo.Local.HorizontalModeInterface
public import LeanPool.FastDynamo.Local.HorizontalModeBulkL2

/-!
# The horizontal Ponomarenko mode is an eigenvector of the jump form operator

This module completes `lem:jump-horizontal-mode`.
`Local/HorizontalModeSurface.lean` reduces the weak eigenvalue identity to three
hypotheses, supplied as follows:

1. the **coordinate sources** `∂_j D_j = {∂_j D_j} + [D_j] n_j δ_{r=1}` for the pivot field
   `D_j = ∂_j b + b_j V⁰_⊥`, obtained here from the fibre-generic one-sided `C¹` constructor of
   `Analysis/WholePlaneUnitDiskFibreBranches.lean` and the pointwise regularity of the two
   branches;
2. the **bulk identity** `bulk₀ + bulk₁ = M + λ_* b`, which is `horizontalModeBulk_add`;
3. the **interface cancellation** `density₀ = -density₁`, which is
   `unitCircleJumpDensity_add_eq_zero_of_pivotBranches`, i.e. `[∂_r b] = Ω b_r e_θ` at `r = 1`.

Feeding them into `horizontalModeDistributionalEquation_of_coordinate_sources` gives, for
arbitrary certified interface data, the distributional identity, the weak identity
`𝔩_{V⁰}(b, φ) = -λ_*⟨b, φ⟩`, and hence that the certified two-component mode
is an eigenvector of the seed's form operator with eigenvalue `λ_* = κ² - N²`, of positive
real part.

The last section instantiates this at the certified data of
`exists_certifiedInterfaceData_two_pi` (`N = 2π`, `Re λ_* ≥ 448 - 4π²`), which is the statement
`prop:local-seed` consumes.  The paper does not fix the radial scale: it proves
`Re λ_* ≥ (7/16)ϱ² - 4π² > 0` for `ϱ` sufficiently large (`eq:local-eigenvalue`); the
formalisation takes `ϱ = 32`, whence `448 - 4π²`.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace HorizontalMode

open Complex Filter MeasureTheory Metric Set Topology
open HorizontalWeakForm
open WholePlaneSliceRadius
open PonomarenkoFreeOmegaInterface
open WholePlaneFibreSource
open WholePlaneRadialExponential

/-! ## Decay of the exterior pivot branch along coordinate slices -/

/-- Whenever the radius along a slice tends to infinity, the exterior pivot branch tends to
zero, by the exponential majorant of the decaying derivative. -/
private theorem horizontalExteriorPivotField_slice_tendsto_zero
    {l : Filter ℝ} {kappa : ℂ} (hkappa : 0 < kappa.re) (j : Fin 2) (x : ℝ)
    (hr : Tendsto (fun t : ℝ ↦ ‖wholePlaneSliceEquiv j (x, t)‖) l atTop) :
    Tendsto (fun t : ℝ ↦
        horizontalExteriorPivotField kappa j (wholePlaneSliceEquiv j (x, t))) l (nhds 0) := by
  have hshift : Tendsto (fun t : ℝ ↦ ‖wholePlaneSliceEquiv j (x, t)‖ - 1) l atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-1 : ℝ) hr
  have harg : Tendsto
      (fun t : ℝ ↦ -kappa.re * (‖wholePlaneSliceEquiv j (x, t)‖ - 1)) l atBot :=
    hshift.const_mul_atTop_of_neg (neg_lt_zero.mpr hkappa)
  have hexp : Tendsto
      (fun t : ℝ ↦ radialExponentialEnvelope kappa.re
        (wholePlaneSliceEquiv j (x, t))) l (nhds 0) :=
    Real.tendsto_exp_atBot.comp harg
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun t : ℝ ↦ 2 * horizontalExteriorDerivativeConstant kappa *
      radialExponentialEnvelope kappa.re (wholePlaneSliceEquiv j (x, t)))
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [hr (eventually_ge_atTop 1)] with t ht
    exact norm_horizontalExteriorPartialDerivative_le_exp hkappa j ht
  · simpa only [mul_zero] using
      hexp.const_mul (2 * horizontalExteriorDerivativeConstant kappa)

/-- Multiplication by a Schwartz test function preserves decay along a slice. -/
private theorem tendsto_schwartz_smul_slice_zero
    {l : Filter ℝ} (u : WholePlane → C2) (phi : SchwartzMap WholePlane ℂ)
    (j : Fin 2) (x : ℝ)
    (hu : Tendsto (fun t : ℝ ↦ u (wholePlaneSliceEquiv j (x, t))) l (nhds 0)) :
    Tendsto (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
      u (wholePlaneSliceEquiv j (x, t))) l (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun t : ℝ ↦ (SchwartzMap.seminorm ℝ 0 0) phi *
      ‖u (wholePlaneSliceEquiv j (x, t))‖)
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · refine Filter.Eventually.of_forall fun t ↦ ?_
    simpa only [norm_smul] using mul_le_mul_of_nonneg_right
      (SchwartzMap.norm_le_seminorm ℝ phi (wholePlaneSliceEquiv j (x, t)))
      (norm_nonneg _)
  · have hnorm := tendsto_zero_iff_norm_tendsto_zero.mp hu
    simpa only [mul_zero] using hnorm.const_mul ((SchwartzMap.seminorm ℝ 0 0) phi)

/-- The Schwartz-weighted exterior pivot branch vanishes at the `-∞` end of every slice. -/
theorem tendsto_schwartz_smul_horizontalExteriorPivotField_slice_atBot
    {kappa : ℂ} (hkappa : 0 < kappa.re) (phi : SchwartzMap WholePlane ℂ)
    (j : Fin 2) (x : ℝ) :
    Tendsto (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
        horizontalExteriorPivotField kappa j (wholePlaneSliceEquiv j (x, t)))
      atBot (nhds 0) :=
  tendsto_schwartz_smul_slice_zero _ phi j x
    (horizontalExteriorPivotField_slice_tendsto_zero hkappa j x
      (tendsto_norm_wholePlaneSliceEquiv_atBot j x))

/-- The Schwartz-weighted exterior pivot branch vanishes at the `+∞` end of every slice. -/
theorem tendsto_schwartz_smul_horizontalExteriorPivotField_slice_atTop
    {kappa : ℂ} (hkappa : 0 < kappa.re) (phi : SchwartzMap WholePlane ℂ)
    (j : Fin 2) (x : ℝ) :
    Tendsto (fun t : ℝ ↦ phi (wholePlaneSliceEquiv j (x, t)) •
        horizontalExteriorPivotField kappa j (wholePlaneSliceEquiv j (x, t)))
      atTop (nhds 0) :=
  tendsto_schwartz_smul_slice_zero _ phi j x
    (horizontalExteriorPivotField_slice_tendsto_zero hkappa j x
      (tendsto_norm_wholePlaneSliceEquiv_atTop j x))

/-! ## The coordinate sources -/

/-- The generic unit-disk gluing of the two pivot branches is the pointwise pivot field of
`HorizontalModeBulkIdentity`. -/
theorem unitDiskPiecewiseField_horizontalPivot (Omega : ℝ) (kappa : ℂ) (j : Fin 2) :
    unitDiskPiecewiseField (horizontalInteriorPivotField Omega kappa j)
        (horizontalExteriorPivotField kappa j) =
      horizontalModePivotField Omega kappa j := by
  funext y
  by_cases hy : ‖y‖ ≤ 1
  · have hmem : y ∈ wholePlaneUnitDisk := by
      simpa [wholePlaneUnitDisk, Metric.mem_closedBall] using hy
    rw [unitDiskPiecewiseField_of_mem _ _ hmem,
      horizontalModePivotField_of_norm_le Omega kappa j hy]
  · have hy' : 1 < ‖y‖ := lt_of_not_ge hy
    rw [unitDiskPiecewiseField_of_notMem _ _ (notMem_unitDisk_of_one_lt_norm hy'),
      horizontalModePivotField_of_one_lt_norm Omega kappa j hy']

/-- The unit-circle source density of the `j`-th pivot field: the outward-minus-inward
coordinate trace `n_j [D_j]` on `r = 1`. -/
def horizontalModeSourceDensity (Omega : ℝ) (kappa : ℂ) (j : Fin 2) :
    WholePlaneUnitCircle → C2 :=
  unitCircleJumpDensity (horizontalInteriorPivotField Omega kappa j)
    (horizontalExteriorPivotField kappa j) j

/-- The source density is integrable on the unit circle. -/
theorem horizontalModeSourceDensity_integrable
    (Omega : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re) (j : Fin 2) :
    Integrable (horizontalModeSourceDensity Omega kappa j)
      wholePlaneUnitCircleMeasure :=
  unitCircleJumpDensity_integrable j
    (horizontalInteriorPivotField_continuous Omega kappa j)
    (fun _y hy ↦ horizontalExteriorPivotField_continuousAt hkappa hy j)

/-- **Obligation 1 of `lem:jump-horizontal-mode`**, in the repository's two-component
vocabulary: the distributional `j`-th derivative of the pivot field `D_j = ∂_j b + b_j V⁰_⊥` is
its branchwise derivative plus the oriented unit-circle jump. -/
theorem horizontalModePivot_hasSource
    (N Omega : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re) (j : Fin 2) :
    HasUnitCircleSourceDerivative
      (horizontalWeakFormDerivativePivot (horizontalModeVelocity N Omega)
        (horizontalModeH1 kappa hkappa) j)
      (horizontalModeBulkL2 Omega kappa hkappa j)
      (horizontalModeSourceDensity Omega kappa j) j := by
  apply hasUnitCircleSourceDerivative_of_unitDisk_branches
    (horizontalInteriorPivotField Omega kappa j) (horizontalExteriorPivotField kappa j)
    (horizontalModeBulkField Omega kappa j)
    (fun y ↦ fderiv ℝ (horizontalInteriorPivotField Omega kappa j) y)
    (fun y ↦ fderiv ℝ (horizontalExteriorPivotField kappa j) y)
  · rw [unitDiskPiecewiseField_horizontalPivot]
    exact (horizontalWeakFormDerivativePivot_coe_ae N Omega hkappa j).symm
  · exact (horizontalModeBulkL2_coe_ae Omega kappa hkappa j).symm
  · exact fun y ↦ (horizontalInteriorPivotField_differentiable Omega kappa j y).hasFDerivAt
  · exact fun y hy ↦ horizontalExteriorPivotField_hasFDerivAt hkappa hy j
  · intro y hy
    rw [horizontalModeBulkField_of_norm_le Omega kappa j hy,
      fderiv_horizontalInteriorPivotField_self Omega kappa j y]
  · intro y hy
    rw [horizontalModeBulkField_of_one_lt_norm Omega kappa j hy,
      fderiv_horizontalExteriorPivotField_self kappa j y]
  · exact fun phi x ↦
      tendsto_schwartz_smul_horizontalExteriorPivotField_slice_atBot hkappa phi j x
  · exact fun phi x ↦
      tendsto_schwartz_smul_horizontalExteriorPivotField_slice_atTop hkappa phi j x

/-! ## The interface cancellation -/

/-- **Obligation 3 of `lem:jump-horizontal-mode`**: the two coordinate source densities are
pointwise opposite on the unit circle.  This is `[∂_r b] - Ω b_r e_θ = 0`, i.e.
`eq:transmission-horizontal`. -/
theorem horizontalModeSourceDensity_cancel {N Omega : ℝ} {kappa : ℂ}
    (hd : CertifiedInterfaceData N Omega kappa) (y : WholePlaneUnitCircle) :
    horizontalModeSourceDensity Omega kappa 0 y =
      -horizontalModeSourceDensity Omega kappa 1 y :=
  eq_neg_of_add_eq_zero_left
    (unitCircleJumpDensity_add_eq_zero_of_pivotBranches hd
      (horizontalInteriorPivotField Omega kappa) (horizontalExteriorPivotField kappa)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) y)

/-! ## The weak identity and the eigenpair -/

/-- **The weak eigenvalue identity of `lem:jump-horizontal-mode`**:
`𝔩_{V⁰}(b, φ) = -λ_*⟨b, φ⟩` for every `φ ∈ H¹(ℝ²;ℂ²)`, at every certified interface root. -/
theorem horizontalModeWeakIdentity_holds {N Omega : ℝ} {kappa : ℂ}
    (hd : CertifiedInterfaceData N Omega kappa) :
    HorizontalModeWeakIdentity hd :=
  horizontalModeWeakEquation_of_coordinate_sources N (horizontalModeVelocity N Omega)
    (horizontalMode hd) (horizontalEigenvalue N kappa) (horizontalModeBulk hd)
    (horizontalModeSourceDensity Omega kappa)
    (fun j ↦ horizontalModeSourceDensity_integrable Omega hd.kappa_re_pos j)
    (fun j ↦ horizontalModePivot_hasSource N Omega hd.kappa_re_pos j)
    (horizontalModeBulk_add hd) (horizontalModeSourceDensity_cancel hd)

/-- **`lem:jump-horizontal-mode`**: the certified two-component Ponomarenko mode lies in the
form domain of `A_{V⁰}` and is an eigenvector with eigenvalue `λ_* = κ² - N²`. -/
theorem horizontalMode_isEigenpair_of_certified {N Omega : ℝ} {kappa : ℂ}
    (hd : CertifiedInterfaceData N Omega kappa) :
    ∃ u : HorizontalFormDomain N (horizontalModeVelocity N Omega),
      u.1.1 = horizontalMode hd ∧
        (horizontalFormOperator N (horizontalModeVelocity N Omega)).IsEigenpair
          (horizontalEigenvalue N kappa) u :=
  horizontalMode_isEigenpair hd (horizontalModeWeakIdentity_holds hd)

/-- The eigenvalue has positive real part, so the mode is a growing local seed. -/
theorem re_ponomarenkoLocalEigenvalue_pos_of_certified {N Omega : ℝ} {kappa : ℂ}
    (hd : CertifiedInterfaceData N Omega kappa) :
    0 < (horizontalEigenvalue N kappa).re :=
  re_ponomarenkoLocalEigenvalue_pos hd

/-! ## The concrete seed at `N = 2π` -/

/-- **`lem:jump-horizontal-mode` at the paper's axial wavenumber `2π`.**  There are an angular
speed `Ω > 0` and a radial parameter `κ` with `Re κ > 0` such that the two-component mode is
a non-zero eigenvector of `A_{V⁰}` with eigenvalue `λ_* = κ² - (2π)²`, and
`Re λ_* ≥ 448 - 4π²` (`eq:local-eigenvalue` at the radial scale `ϱ = 32` fixed by the
formalisation; the paper only takes `ϱ` sufficiently large). -/
theorem exists_horizontalMode_eigenpair_two_pi :
    ∃ (Omega : ℝ) (kappa : ℂ) (hd : CertifiedInterfaceData (2 * Real.pi) Omega kappa),
      0 < Omega ∧
        (448 : ℝ) - (2 * Real.pi) ^ 2 ≤ (horizontalEigenvalue (2 * Real.pi) kappa).re ∧
        0 < (horizontalEigenvalue (2 * Real.pi) kappa).re ∧
        horizontalMode hd ≠ 0 ∧
        ∃ u : HorizontalFormDomain (2 * Real.pi)
            (horizontalModeVelocity (2 * Real.pi) Omega),
          u.1.1 = horizontalMode hd ∧
            (horizontalFormOperator (2 * Real.pi)
                (horizontalModeVelocity (2 * Real.pi) Omega)).IsEigenpair
              (horizontalEigenvalue (2 * Real.pi) kappa) u := by
  obtain ⟨Omega, kappa, hd, _, _, _, _, hgrowth⟩ := exists_certifiedInterfaceData_two_pi
  exact ⟨Omega, kappa, hd, hd.omega_pos, hgrowth,
    re_ponomarenkoLocalEigenvalue_pos_of_certified hd, horizontalMode_ne_zero hd,
    horizontalMode_isEigenpair_of_certified hd⟩

end HorizontalMode
end FastDynamo
