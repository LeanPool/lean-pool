/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteZoomCutoffSecondDeriv

/-!
# Instantiating `step_finite_contradiction` at the cutoff-multiplied zoom fields

This file assembles every piece built in `FiniteZoomCutoffField.lean`,
`FiniteZoomCutoffData.lean`, `FiniteZoomCutoffBounds.lean` and
`FiniteZoomCutoffSecondDeriv.lean` into the exact hypothesis block of
`CIV.step_finite_contradiction_of_dr_dz`, with `Vseq := cutoffZoomV`, `Wseq := cutoffZoomW`.
The selection data `Rsel`, `c₀` and the lower bound `hlower` belong to a different step of the
proof (the meridional-smallness dichotomy that produces the selected
sequence) and are taken here as hypotheses, exactly as `step_finite_contradiction_of_dr_dz`
already takes them; likewise `Ω_n → 0` is the endpoint vanishing of the comparison
argument and is taken as a hypothesis rather than re-derived.
-/

public section

open Set Filter Topology Metric
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### The second-derivative equalities, specialised to `zoomV`/`zoomW` -/

private theorem isOpen_zoomPoint_slice_preimage (lam h zc : ℝ) :
    IsOpen {q : ℝ × ℝ | zoomPoint lam h zc (q, -1) ∈ unitCylinder} :=
  isOpen_unitCylinder_prod.preimage
    ((continuous_zoomPoint lam h zc).comp (continuous_id.prodMk continuous_const))

theorem fderiv2_zoomV_slice_apply_rr {h zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : zoomPoint lam h zc (y, -1) ∈ unitCylinder) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomV lam h zc u (q, -1))) y (1, 0) (1, 0)
      = dr (dr (zoomV lam h zc u)) (y, -1) :=
  fderiv_fderiv_apply_radial_radial_eq_drdr (isOpen_zoomPoint_slice_preimage lam h zc)
    (contDiffOn_zoomV_slice hsol) hy

theorem fderiv2_zoomV_slice_apply_rz {h zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : zoomPoint lam h zc (y, -1) ∈ unitCylinder) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomV lam h zc u (q, -1))) y (1, 0) (0, 1)
      = dr (dz (zoomV lam h zc u)) (y, -1) :=
  fderiv_fderiv_apply_radial_axial_eq_drdz (isOpen_zoomPoint_slice_preimage lam h zc)
    (contDiffOn_zoomV_slice hsol) hy

theorem fderiv2_zoomV_slice_apply_zz {h zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : zoomPoint lam h zc (y, -1) ∈ unitCylinder) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomV lam h zc u (q, -1))) y (0, 1) (0, 1)
      = dz (dz (zoomV lam h zc u)) (y, -1) :=
  fderiv_fderiv_apply_axial_axial_eq_dzdz (isOpen_zoomPoint_slice_preimage lam h zc)
    (contDiffOn_zoomV_slice hsol) hy

theorem fderiv2_zoomW_slice_apply_rr {h zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : zoomPoint lam h zc (y, -1) ∈ unitCylinder) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomW lam h zc u (q, -1))) y (1, 0) (1, 0)
      = dr (dr (zoomW lam h zc u)) (y, -1) :=
  fderiv_fderiv_apply_radial_radial_eq_drdr (isOpen_zoomPoint_slice_preimage lam h zc)
    (contDiffOn_zoomW_slice hsol) hy

theorem fderiv2_zoomW_slice_apply_rz {h zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : zoomPoint lam h zc (y, -1) ∈ unitCylinder) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomW lam h zc u (q, -1))) y (1, 0) (0, 1)
      = dr (dz (zoomW lam h zc u)) (y, -1) :=
  fderiv_fderiv_apply_radial_axial_eq_drdz (isOpen_zoomPoint_slice_preimage lam h zc)
    (contDiffOn_zoomW_slice hsol) hy

theorem fderiv2_zoomW_slice_apply_zz {h zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : zoomPoint lam h zc (y, -1) ∈ unitCylinder) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomW lam h zc u (q, -1))) y (0, 1) (0, 1)
      = dz (dz (zoomW lam h zc u)) (y, -1) :=
  fderiv_fderiv_apply_axial_axial_eq_dzdz (isOpen_zoomPoint_slice_preimage lam h zc)
    (contDiffOn_zoomW_slice hsol) hy

/-! ### The cutoff-multiplied field's second derivative reads off the raw slice's -/

theorem eventually_fderiv2_cutoffZoomV_eq {h : ℝ} (hh1 : h < 1 / 2) {zc : ℕ → ℝ} {ζ : ℝ}
    (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {u : ParabolicPoint → Vec3} {lam : ℕ → ℝ}
    (hlam0 : ∀ n, 0 < lam n) (hlamTendsto : Tendsto lam atTop (nhds 0)) (y : ℝ × ℝ) :
    ∀ᶠ n in atTop, fderiv ℝ (fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n)) y
      = fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1))) y := by
  filter_upwards [eventually_cutoffBump_eq_one_of_norm_le hh1 hzc hζ hlam0 hlamTendsto
    (‖y‖ + 1)] with n hn
  have heqOn : Set.EqOn (cutoffZoomV h zc hzc hζ u lam hlam0 n)
      (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1)) (ball (0 : ℝ × ℝ) (‖y‖ + 1)) := by
    intro q hq
    rw [mem_ball, dist_eq_norm, sub_zero] at hq
    exact cutoffZoomV_eqOn_ball hzc hζ hlam0 n hn hq.le
  have hyball : y ∈ ball (0 : ℝ × ℝ) (‖y‖ + 1) := by
    rw [mem_ball, dist_eq_norm, sub_zero]; linarith only
  have hfderivEq : Set.EqOn (fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n))
      (fderiv ℝ (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1))) (ball (0 : ℝ × ℝ)
      (‖y‖ + 1)) := by
    intro q hq
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [isOpen_ball.mem_nhds hq] with q' hq' using heqOn hq'
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [isOpen_ball.mem_nhds hyball] with q hq using hfderivEq hq

theorem eventually_fderiv2_cutoffZoomW_eq {h : ℝ} (hh1 : h < 1 / 2) {zc : ℕ → ℝ} {ζ : ℝ}
    (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {u : ParabolicPoint → Vec3} {lam : ℕ → ℝ}
    (hlam0 : ∀ n, 0 < lam n) (hlamTendsto : Tendsto lam atTop (nhds 0)) (y : ℝ × ℝ) :
    ∀ᶠ n in atTop, fderiv ℝ (fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n)) y
      = fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1))) y := by
  filter_upwards [eventually_cutoffBump_eq_one_of_norm_le hh1 hzc hζ hlam0 hlamTendsto
    (‖y‖ + 1)] with n hn
  have heqOn : Set.EqOn (cutoffZoomW h zc hzc hζ u lam hlam0 n)
      (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1)) (ball (0 : ℝ × ℝ) (‖y‖ + 1)) := by
    intro q hq
    rw [mem_ball, dist_eq_norm, sub_zero] at hq
    exact cutoffZoomW_eqOn_ball hzc hζ hlam0 n hn hq.le
  have hyball : y ∈ ball (0 : ℝ × ℝ) (‖y‖ + 1) := by
    rw [mem_ball, dist_eq_norm, sub_zero]; linarith only
  have hfderivEq : Set.EqOn (fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n))
      (fderiv ℝ (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1))) (ball (0 : ℝ × ℝ)
      (‖y‖ + 1)) := by
    intro q hq
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [isOpen_ball.mem_nhds hq] with q' hq' using heqOn hq'
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [isOpen_ball.mem_nhds hyball] with q hq using hfderivEq hq

/-! ### The uniform second-derivative operator-norm bound, eventually in `n` -/

/-- The fourth (axial-radial) entry, for the cutoff-multiplied radial field, agrees with the
radial-axial one: `Vseq n` is globally `ContDiff ℝ (⊤ : ℕ∞)`
(`CIV.contDiff_cutoffZoomV`), so `second_derivative_symmetric` applies to it directly, even
though the raw slice underneath is only locally smooth. -/
theorem eventually_norm_fderiv2_cutoffZoomV_le {C h : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hh1 : h < 1 / 2) {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {pres : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsClassicalSolutionOn u pres f unitCylinder)
    {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1)
    (hlamTendsto : Tendsto lam atTop (nhds 0)) (y : ℝ × ℝ) :
    ∀ᶠ n in atTop, ‖fderiv ℝ (fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n)) y‖ ≤
      4 * C := by
  filter_upwards [eventually_fderiv2_cutoffZoomV_eq hh1 hzc hζ hlam0 hlamTendsto y,
    eventually_zoomPoint_slice_mem_unitCylinder hh0 hh1 hzc hζ hlam0 hlam1 hlamTendsto y]
    with n hFeq hy
  have hCD : ContDiff ℝ (⊤ : ℕ∞) (cutoffZoomV h zc hzc hζ u lam hlam0 n) :=
    contDiff_cutoffZoomV hh0 hzc hζ hsol hlam0 hlam1 n
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1.of_le (by norm_num)
  have hzr : fderiv ℝ (fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n)) y (0, 1) (1, 0)
      = fderiv ℝ (fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n)) y (1, 0) (0, 1) :=
    fderiv_fderiv_apply_axial_radial_eq_of_contDiff hCD y
  have hrr := fderiv2_zoomV_slice_apply_rr (lam := lam n) hsol hy
  have hrz := fderiv2_zoomV_slice_apply_rz (lam := lam n) hsol hy
  have hzz := fderiv2_zoomV_slice_apply_zz (lam := lam n) hsol hy
  have hzr' : fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1))) y
      (0, 1) (1, 0) = dr (dz (zoomV (lam n) h (zc n) u)) (y, -1) := by
    rw [← hFeq, hzr, hFeq]; exact hrz
  have hb1 : |dr (dr (zoomV (lam n) h (zc n) u)) (y, -1)| ≤ C := by
    have := abs_drdr_zoomV_le_rpow_neg_half (hlam0 n) hb hu2 hy hC (by norm_num)
    simpa using this
  have hb2 : |dr (dz (zoomV (lam n) h (zc n) u)) (y, -1)| ≤ C := by
    have := abs_drdz_zoomV_le_rpow_neg_half (hlam0 n) hb hu2 hy hC hh1.le (by norm_num)
    simpa using this
  have hb3 : |dz (dz (zoomV (lam n) h (zc n) u)) (y, -1)| ≤ C := by
    have := abs_dzdz_zoomV_le_rpow_neg_half (hlam0 n) hb hu2 hy hC hh1.le (by norm_num)
    simpa using this
  have hnorm := norm_fderiv_fderiv_le_of_apply (cutoffZoomV h zc hzc hζ u lam hlam0 n) y
  rw [hFeq]
  rw [hFeq, hrr, hrz, hzr', hzz] at hnorm
  linarith only [hnorm, hb1, hb2, hb3]

/-- The vertical counterpart of `eventually_norm_fderiv2_cutoffZoomV_le`. -/
theorem eventually_norm_fderiv2_cutoffZoomW_le {C h : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hh1 : h < 1 / 2) {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {pres : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsClassicalSolutionOn u pres f unitCylinder)
    {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1)
    (hlamTendsto : Tendsto lam atTop (nhds 0)) (y : ℝ × ℝ) :
    ∀ᶠ n in atTop, ‖fderiv ℝ (fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n)) y‖ ≤
      4 * C := by
  filter_upwards [eventually_fderiv2_cutoffZoomW_eq hh1 hzc hζ hlam0 hlamTendsto y,
    eventually_zoomPoint_slice_mem_unitCylinder hh0 hh1 hzc hζ hlam0 hlam1 hlamTendsto y]
    with n hFeq hy
  have hCD : ContDiff ℝ (⊤ : ℕ∞) (cutoffZoomW h zc hzc hζ u lam hlam0 n) :=
    contDiff_cutoffZoomW hh0 hzc hζ hsol hlam0 hlam1 n
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1.of_le (by norm_num)
  have hzr : fderiv ℝ (fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n)) y (0, 1) (1, 0)
      = fderiv ℝ (fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n)) y (1, 0) (0, 1) :=
    fderiv_fderiv_apply_axial_radial_eq_of_contDiff hCD y
  have hrr := fderiv2_zoomW_slice_apply_rr (lam := lam n) hsol hy
  have hrz := fderiv2_zoomW_slice_apply_rz (lam := lam n) hsol hy
  have hzz := fderiv2_zoomW_slice_apply_zz (lam := lam n) hsol hy
  have hzr' : fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1))) y
      (0, 1) (1, 0) = dr (dz (zoomW (lam n) h (zc n) u)) (y, -1) := by
    rw [← hFeq, hzr, hFeq]; exact hrz
  have hb1 : |dr (dr (zoomW (lam n) h (zc n) u)) (y, -1)| ≤ C := by
    have := abs_drdr_zoomW_le_rpow_neg_half (hlam0 n) hb hu2 hy hC hh0 (by norm_num)
    simpa using this
  have hb2 : |dr (dz (zoomW (lam n) h (zc n) u)) (y, -1)| ≤ C := by
    have := abs_drdz_zoomW_le_rpow_neg_half (hlam0 n) hb hu2 hy hC (by norm_num)
    simpa using this
  have hb3 : |dz (dz (zoomW (lam n) h (zc n) u)) (y, -1)| ≤ C := by
    have := abs_dzdz_zoomW_le_rpow_neg_half (hlam0 n) hb hu2 hy hC hh1.le (by norm_num)
    simpa using this
  have hnorm := norm_fderiv_fderiv_le_of_apply (cutoffZoomW h zc hzc hζ u lam hlam0 n) y
  rw [hFeq]
  rw [hFeq, hrr, hrz, hzr', hzz] at hnorm
  linarith only [hnorm, hb1, hb2, hb3]

end CIV
