/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteZoomCutoffInstantiation
public import LeanPool.CIVAxisymmetric.Zoom.FiniteContradictionClosure

/-!
# `step_finite_contradiction` at the cutoff-multiplied zoom fields

The final assembly: `hVbdd`/`hWbdd` on every `halfPlaneRectangle j` (value, first- and
second-derivative operator norm, by one shared constant `L = 4C`), together with `hVsmooth`,
`hWsmooth`, `haxis`, `hdivn`, `hdWn` from the earlier files, discharge every hypothesis of
`CIV.step_finite_contradiction_of_dr_dz` except the selection data `Rsel`, `c₀`, `hlower` (a
different step) and `Ω_n → 0` (the endpoint vanishing of the comparison argument,
`CIV/Zoom/ZoomLimitEndpoint.lean`), which are taken as hypotheses.

The zoom centre `zc : ℕ → ℝ` moves with `n`, uniformly bounded by `ζ < 1` (`hzc`, `hζ`): the
paper zooms about a moving axial offset `z_n`, and the finite-axis selection
`CIV.exists_seq_three_terms_dichotomy` this adapter is eventually fed returns exactly such a
moving height sequence, not a single fixed real number.
-/

public section

open Set Filter Topology Metric
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Every point of a rectangle enters `unitCylinder` under the zoom map, eventually -/

theorem eventually_forall_mem_halfPlaneRectangle_zoomPoint_mem {h : ℝ} (hh0 : 0 ≤ h)
    (hh1 : h < 1 / 2) {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {lam : ℕ → ℝ}
    (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1) (hlamTendsto : Tendsto lam atTop (nhds 0))
    (j : ℕ) :
    ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      zoomPoint (lam n) h (zc n) (y, -1) ∈ unitCylinder := by
  filter_upwards [eventually_cutoffBump_rIn_gt hh1 hzc hζ hlam0 hlamTendsto ((j : ℝ) + 1)]
    with n hn
  intro y hy
  apply cutoffBump_safe hh0 hzc hζ (hlam0 n) (hlam1 n) n
  rw [mem_closedBall, dist_eq_norm, sub_zero]
  have hrOut := (cutoffBump h zc hzc hζ (lam n) (hlam0 n) n).rIn_lt_rOut
  have := norm_le_of_mem_halfPlaneRectangle hy
  linarith only [hn, hrOut, this]

/-! ### The second derivative on a rectangle reads off the raw slice's, eventually -/

theorem eventually_forall_mem_halfPlaneRectangle_fderiv2_cutoffZoomV_eq {h : ℝ}
    (hh1 : h < 1 / 2) {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    {u : ParabolicPoint → Vec3} {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n)
    (hlamTendsto : Tendsto lam atTop (nhds 0)) (j : ℕ) :
    ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      fderiv ℝ (fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n)) y
        = fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1))) y := by
  filter_upwards [eventually_cutoffBump_eq_one_of_norm_le hh1 hzc hζ hlam0 hlamTendsto
    ((j : ℝ) + 2)] with n hn y hy
  have heqOn : Set.EqOn (cutoffZoomV h zc hzc hζ u lam hlam0 n)
      (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1)) (ball (0 : ℝ × ℝ) ((j : ℝ) + 2)) := by
    intro q hq
    rw [mem_ball, dist_eq_norm, sub_zero] at hq
    exact cutoffZoomV_eqOn_ball hzc hζ hlam0 n hn hq.le
  have hyball : y ∈ ball (0 : ℝ × ℝ) ((j : ℝ) + 2) := by
    rw [mem_ball, dist_eq_norm, sub_zero]
    linarith only [norm_le_of_mem_halfPlaneRectangle hy]
  have hfderivEq : Set.EqOn (fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n))
      (fderiv ℝ (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1)))
      (ball (0 : ℝ × ℝ) ((j : ℝ) + 2)) := by
    intro q hq
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [isOpen_ball.mem_nhds hq] with q' hq' using heqOn hq'
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [isOpen_ball.mem_nhds hyball] with q hq using hfderivEq hq

theorem eventually_forall_mem_halfPlaneRectangle_fderiv2_cutoffZoomW_eq {h : ℝ}
    (hh1 : h < 1 / 2) {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    {u : ParabolicPoint → Vec3} {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n)
    (hlamTendsto : Tendsto lam atTop (nhds 0)) (j : ℕ) :
    ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      fderiv ℝ (fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n)) y
        = fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1))) y := by
  filter_upwards [eventually_cutoffBump_eq_one_of_norm_le hh1 hzc hζ hlam0 hlamTendsto
    ((j : ℝ) + 2)] with n hn y hy
  have heqOn : Set.EqOn (cutoffZoomW h zc hzc hζ u lam hlam0 n)
      (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1)) (ball (0 : ℝ × ℝ) ((j : ℝ) + 2)) := by
    intro q hq
    rw [mem_ball, dist_eq_norm, sub_zero] at hq
    exact cutoffZoomW_eqOn_ball hzc hζ hlam0 n hn hq.le
  have hyball : y ∈ ball (0 : ℝ × ℝ) ((j : ℝ) + 2) := by
    rw [mem_ball, dist_eq_norm, sub_zero]
    linarith only [norm_le_of_mem_halfPlaneRectangle hy]
  have hfderivEq : Set.EqOn (fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n))
      (fderiv ℝ (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1)))
      (ball (0 : ℝ × ℝ) ((j : ℝ) + 2)) := by
    intro q hq
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [isOpen_ball.mem_nhds hq] with q' hq' using heqOn hq'
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [isOpen_ball.mem_nhds hyball] with q hq using hfderivEq hq

/-! ### `hVbdd`, `hWbdd` on `halfPlaneRectangle j`, eventually, with the shared constant `4C` -/

theorem eventually_forall_mem_halfPlaneRectangle_cutoffZoomV_bounds {C h : ℝ} (hC : 0 ≤ C)
    (hh0 : 0 ≤ h) (hh1 : h < 1 / 2) {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {pres : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsClassicalSolutionOn u pres f unitCylinder)
    {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1)
    (hlamTendsto : Tendsto lam atTop (nhds 0)) (j : ℕ) :
    ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      |cutoffZoomV h zc hzc hζ u lam hlam0 n y| ≤ 4 * C ∧
        ‖fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n) y‖ ≤ 4 * C ∧
        ‖fderiv ℝ (fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n)) y‖ ≤ 4 * C := by
  have hCD : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (cutoffZoomV h zc hzc hζ u lam hlam0 n) :=
    fun n => contDiff_cutoffZoomV hh0 hzc hζ hsol hlam0 hlam1 n
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1.of_le (by norm_num)
  filter_upwards [eventually_forall_mem_halfPlaneRectangle_cutoffZoomV_eq hh1 hzc hζ hlam0
      hlamTendsto j,
    eventually_forall_mem_halfPlaneRectangle_zoomPoint_mem hh0 hh1 hzc hζ hlam0 hlam1
      hlamTendsto j,
    eventually_forall_mem_halfPlaneRectangle_fderiv2_cutoffZoomV_eq hh1 hzc hζ hlam0
      hlamTendsto j] with n hEq hMem hFeq2
  intro y hy
  obtain ⟨hVeq, hFVeq⟩ := hEq y hy
  have hMemy := hMem y hy
  have hFeqy := hFeq2 y hy
  refine ⟨?_, ?_, ?_⟩
  · rw [hVeq]
    have := abs_zoomV_slice_le (hlam0 n) hb hMemy
    linarith only [this, hC]
  · rw [hFVeq]
    have := norm_fderiv_zoomV_slice_le (hlam0 n) hb hsol hMemy
    linarith only [this, hC]
  · have hzr : fderiv ℝ (fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n)) y (0, 1) (1, 0)
        = fderiv ℝ (fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n)) y (1, 0) (0, 1) :=
      fderiv_fderiv_apply_axial_radial_eq_of_contDiff (hCD n) y
    have hrr := fderiv2_zoomV_slice_apply_rr (lam := lam n) hsol hMemy
    have hrz := fderiv2_zoomV_slice_apply_rz (lam := lam n) hsol hMemy
    have hzz := fderiv2_zoomV_slice_apply_zz (lam := lam n) hsol hMemy
    have hzr' : fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1))) y
        (0, 1) (1, 0) = dr (dz (zoomV (lam n) h (zc n) u)) (y, -1) := by
      rw [← hFeqy, hzr, hFeqy]; exact hrz
    have hb1 : |dr (dr (zoomV (lam n) h (zc n) u)) (y, -1)| ≤ C := by
      have := abs_drdr_zoomV_le_rpow_neg_half (hlam0 n) hb hu2 hMemy hC (by norm_num)
      simpa using this
    have hb2 : |dr (dz (zoomV (lam n) h (zc n) u)) (y, -1)| ≤ C := by
      have := abs_drdz_zoomV_le_rpow_neg_half (hlam0 n) hb hu2 hMemy hC hh1.le (by norm_num)
      simpa using this
    have hb3 : |dz (dz (zoomV (lam n) h (zc n) u)) (y, -1)| ≤ C := by
      have := abs_dzdz_zoomV_le_rpow_neg_half (hlam0 n) hb hu2 hMemy hC hh1.le (by norm_num)
      simpa using this
    have hnorm := norm_fderiv_fderiv_le_of_apply (cutoffZoomV h zc hzc hζ u lam hlam0 n) y
    rw [hFeqy]
    rw [hFeqy, hrr, hrz, hzr', hzz] at hnorm
    linarith only [hnorm, hb1, hb2, hb3]

theorem eventually_forall_mem_halfPlaneRectangle_cutoffZoomW_bounds {C h : ℝ} (hC : 0 ≤ C)
    (hh0 : 0 ≤ h) (hh1 : h < 1 / 2) {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {pres : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsClassicalSolutionOn u pres f unitCylinder)
    {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1)
    (hlamTendsto : Tendsto lam atTop (nhds 0)) (j : ℕ) :
    ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      |cutoffZoomW h zc hzc hζ u lam hlam0 n y| ≤ 4 * C ∧
        ‖fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n) y‖ ≤ 4 * C ∧
        ‖fderiv ℝ (fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n)) y‖ ≤ 4 * C := by
  have hCD : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (cutoffZoomW h zc hzc hζ u lam hlam0 n) :=
    fun n => contDiff_cutoffZoomW hh0 hzc hζ hsol hlam0 hlam1 n
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1.of_le (by norm_num)
  filter_upwards [eventually_forall_mem_halfPlaneRectangle_cutoffZoomW_eq hh1 hzc hζ hlam0
      hlamTendsto j,
    eventually_forall_mem_halfPlaneRectangle_zoomPoint_mem hh0 hh1 hzc hζ hlam0 hlam1
      hlamTendsto j,
    eventually_forall_mem_halfPlaneRectangle_fderiv2_cutoffZoomW_eq hh1 hzc hζ hlam0
      hlamTendsto j] with n hEq hMem hFeq2
  intro y hy
  obtain ⟨hVeq, hFVeq⟩ := hEq y hy
  have hMemy := hMem y hy
  have hFeqy := hFeq2 y hy
  refine ⟨?_, ?_, ?_⟩
  · rw [hVeq]
    have := abs_zoomW_slice_le (hlam0 n) hb hMemy
    linarith only [this, hC]
  · rw [hFVeq]
    have := norm_fderiv_zoomW_slice_le (hlam0 n) hb hsol hMemy
    linarith only [this, hC]
  · have hzr : fderiv ℝ (fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n)) y (0, 1) (1, 0)
        = fderiv ℝ (fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n)) y (1, 0) (0, 1) :=
      fderiv_fderiv_apply_axial_radial_eq_of_contDiff (hCD n) y
    have hrr := fderiv2_zoomW_slice_apply_rr (lam := lam n) hsol hMemy
    have hrz := fderiv2_zoomW_slice_apply_rz (lam := lam n) hsol hMemy
    have hzz := fderiv2_zoomW_slice_apply_zz (lam := lam n) hsol hMemy
    have hzr' : fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1))) y
        (0, 1) (1, 0) = dr (dz (zoomW (lam n) h (zc n) u)) (y, -1) := by
      rw [← hFeqy, hzr, hFeqy]; exact hrz
    have hb1 : |dr (dr (zoomW (lam n) h (zc n) u)) (y, -1)| ≤ C := by
      have := abs_drdr_zoomW_le_rpow_neg_half (hlam0 n) hb hu2 hMemy hC hh0 (by norm_num)
      simpa using this
    have hb2 : |dr (dz (zoomW (lam n) h (zc n) u)) (y, -1)| ≤ C := by
      have := abs_drdz_zoomW_le_rpow_neg_half (hlam0 n) hb hu2 hMemy hC (by norm_num)
      simpa using this
    have hb3 : |dz (dz (zoomW (lam n) h (zc n) u)) (y, -1)| ≤ C := by
      have := abs_dzdz_zoomW_le_rpow_neg_half (hlam0 n) hb hu2 hMemy hC hh1.le (by norm_num)
      simpa using this
    have hnorm := norm_fderiv_fderiv_le_of_apply (cutoffZoomW h zc hzc hζ u lam hlam0 n) y
    rw [hFeqy]
    rw [hFeqy, hrr, hrz, hzr', hzz] at hnorm
    linarith only [hnorm, hb1, hb2, hb3]

/-! ### The instantiation: `step_finite_contradiction` at the cutoff-multiplied zoom fields -/

/-- `step_finite_contradiction`, instantiated at the cutoff-multiplied zoom fields
`Vseq n := cutoffZoomV h zc hzc hζ u lam hlam0 n`,
`Wseq n := cutoffZoomW h zc hzc hζ u lam hlam0 n`, with the shared bound `L := 4C`. Every
hypothesis is discharged from the standing classical-solution, anisotropic-bound and
axisymmetry data except the selection data `Rsel`, `c₀`, `hlower` — the conclusion of the
meridional-smallness dichotomy — and `Ω_n → 0`, the endpoint vanishing of the
comparison argument; both are taken here as hypotheses. The
zoom centre `zc n` moves with `n`, so `hΩ0` and `hlower` are stated at the same moving centre,
matching a selection whose axial heights are themselves a sequence. -/
theorem false_of_finiteZoomCutoff_selection {C h : ℝ} (hC : 0 ≤ C) (hh0 : 0 < h)
    (hh1 : h < 1 / 2) {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {pres : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsClassicalSolutionOn u pres f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n)
    (hlam1 : ∀ n, lam n < 1) (hlamTendsto : Tendsto lam atTop (nhds 0))
    (hΩ0 : ∀ q : ℝ × ℝ, 0 < q.1 →
      Tendsto (fun n => zoomOmega (lam n) h (zc n) u (q, -1)) atTop (nhds 0))
    {A c₀ : ℝ} (hA : 0 < A) (hc₀ : 0 < c₀) {Rsel : ℕ → ℝ}
    (hRmem : ∀ n, Rsel n ∈ Icc (0 : ℝ) A)
    (hlower : ∀ᶠ n in atTop,
      c₀ ≤ 2 * |fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n) (Rsel n, 0) (1, 0)|
      + |cutoffZoomV h zc hzc hζ u lam hlam0 n (Rsel n, 0) / Rsel n|
      + |fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n) (Rsel n, 0) (0, 1)|) :
    False :=
  step_finite_contradiction hA hc₀ (by linarith only [hC] : (0 : ℝ) ≤ 4 * C)
    (cutoffZoomV h zc hzc hζ u lam hlam0) (cutoffZoomW h zc hzc hζ u lam hlam0)
    (fun n => contDiff_cutoffZoomV hh0.le hzc hζ hsol hlam0 hlam1 n)
    (fun n => contDiff_cutoffZoomW hh0.le hzc hζ hsol hlam0 hlam1 n)
    (fun j => eventually_forall_mem_halfPlaneRectangle_cutoffZoomV_bounds hC hh0.le hh1 hzc hζ
      hb hsol hlam0 hlam1 hlamTendsto j)
    (fun j => eventually_forall_mem_halfPlaneRectangle_cutoffZoomW_bounds hC hh0.le hh1 hzc hζ
      hb hsol hlam0 hlam1 hlamTendsto j)
    (fun n => cutoffZoomV_axis_eq_zero hh0.le hzc hζ haxi hlam0 hlam1 n)
    (fun p hp => eventually_cutoffZoom_divergence_eq_zero hh0.le hh1 hzc hζ hsol haxi hlam0
      hlam1 hlamTendsto hp)
    (fun p hp => tendsto_fderiv_cutoffZoomW_apply_zero hh0 hh1 hzc hζ hsol hC hb hlam0 hlam1
      hlamTendsto hΩ0 hp)
    hRmem hlower

/-! ### The payoff: `hlower` is supplied, eventually, by the real raw selection bound -/

/-- `false_of_finiteZoomCutoff_selection`'s `hlower` in `∀ᶠ n` form, produced from the raw-field
selection bound at real data: once `n` is large enough that the cutoff equals `1` throughout the
fixed square containing `[0, A] × {0}`
(`CIV.eventually_forall_mem_halfPlaneRectangle_cutoffZoomV_eq`,
`..._cutoffZoomW_eq`), the cutoff-multiplied fields and their derivatives at `(Rsel n, 0)`
coincide with the raw zoom slices there, at the same moving centre `zc n`, whose `dr`/`dz`
values are exactly what `CIV.lt_of_neg_t_mul_meridionalQuantity_selection_lt` bounds below by
`c₀`. So the `∀ n` raw-field selection bound — the real selected sequence, moving centre
included, not a substitute — supplies the weaker `∀ᶠ n` hypothesis that
`CIV.step_finite_contradiction` now needs, where it could not supply the former `∀ n`
cutoff-field requirement at every finite `n`. -/
theorem eventually_cutoffZoom_hlower_of_raw_selection {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {lam : ℕ → ℝ}
    (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1) (hlamTendsto : Tendsto lam atTop (nhds 0))
    {A c₀ : ℝ} {Rsel : ℕ → ℝ} (hRmem : ∀ n, Rsel n ∈ Icc (0 : ℝ) A)
    (hlowerRaw : ∀ n, c₀ ≤ 2 * |dr (zoomV (lam n) h (zc n) u) ((Rsel n, 0), (-1 : ℝ))|
      + |zoomV (lam n) h (zc n) u ((Rsel n, 0), (-1 : ℝ)) / Rsel n|
      + |dz (zoomW (lam n) h (zc n) u) ((Rsel n, 0), (-1 : ℝ))|) :
    ∀ᶠ n in atTop,
      c₀ ≤ 2 * |fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n) (Rsel n, 0) (1, 0)|
      + |cutoffZoomV h zc hzc hζ u lam hlam0 n (Rsel n, 0) / Rsel n|
      + |fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n) (Rsel n, 0) (0, 1)| := by
  obtain ⟨jA, hjA⟩ := exists_nat_ge A
  have hAle : A ≤ (jA : ℝ) + 1 := by linarith only [hjA]
  have hsub : Icc (0 : ℝ) A ×ˢ ({0} : Set ℝ) ⊆ halfPlaneRectangle jA :=
    segment_subset_halfPlaneRectangle hAle
  have hmem : ∀ n, (Rsel n, 0) ∈ halfPlaneRectangle jA := fun n => hsub ⟨hRmem n, rfl⟩
  filter_upwards [eventually_forall_mem_halfPlaneRectangle_cutoffZoomV_eq hh1 hzc hζ hlam0
      hlamTendsto jA,
    eventually_forall_mem_halfPlaneRectangle_cutoffZoomW_eq hh1 hzc hζ hlam0 hlamTendsto jA,
    eventually_forall_mem_halfPlaneRectangle_zoomPoint_mem hh0 hh1 hzc hζ hlam0 hlam1
      hlamTendsto jA] with n hVeq hWeq hMem
  have hVeqn := hVeq (Rsel n, 0) (hmem n)
  have hWeqn := hWeq (Rsel n, 0) (hmem n)
  have hMemn := hMem (Rsel n, 0) (hmem n)
  have hHFV := hasFDerivAt_zoomV_slice_of_mem hsol hMemn
  have hHFW := hasFDerivAt_zoomW_slice_of_mem hsol hMemn
  have hdrn : dr (zoomV (lam n) h (zc n) u) ((Rsel n, 0), (-1 : ℝ))
      = fderiv ℝ (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1)) (Rsel n, 0) (1, 0) :=
    dr_eq_of_hasFDerivAt (zoomV (lam n) h (zc n) u) (-1) hHFV
  have hdzn : dz (zoomW (lam n) h (zc n) u) ((Rsel n, 0), (-1 : ℝ))
      = fderiv ℝ (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1)) (Rsel n, 0) (0, 1) :=
    dz_eq_of_hasFDerivAt (zoomW (lam n) h (zc n) u) (-1) hHFW
  have h := hlowerRaw n
  rw [hdrn, hdzn, ← hVeqn.2, ← hWeqn.2, ← hVeqn.1] at h
  exact h

/-- `step_finite_contradiction` closes end to end at real data: given the raw-field selection
bound `hlowerRaw` — exactly the conclusion of `CIV.lt_of_neg_t_mul_meridionalQuantity_selection_lt`
at the selected sequence, moving centre included, and nothing manufactured — the cutoff adapter
now supplies every hypothesis of `CIV.step_finite_contradiction`, `hlower` included via
`CIV.eventually_cutoffZoom_hlower_of_raw_selection`. Only the endpoint vanishing
of the comparison argument (`hΩ0`) and the meridional-smallness dichotomy that produces
`hlowerRaw` itself remain external. -/
theorem false_of_finiteZoomCutoff_raw_selection {C h : ℝ} (hC : 0 ≤ C) (hh0 : 0 < h)
    (hh1 : h < 1 / 2) {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {pres : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsClassicalSolutionOn u pres f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n)
    (hlam1 : ∀ n, lam n < 1) (hlamTendsto : Tendsto lam atTop (nhds 0))
    (hΩ0 : ∀ q : ℝ × ℝ, 0 < q.1 →
      Tendsto (fun n => zoomOmega (lam n) h (zc n) u (q, -1)) atTop (nhds 0))
    {A c₀ : ℝ} (hA : 0 < A) (hc₀ : 0 < c₀) {Rsel : ℕ → ℝ}
    (hRmem : ∀ n, Rsel n ∈ Icc (0 : ℝ) A)
    (hlowerRaw : ∀ n, c₀ ≤ 2 * |dr (zoomV (lam n) h (zc n) u) ((Rsel n, 0), (-1 : ℝ))|
      + |zoomV (lam n) h (zc n) u ((Rsel n, 0), (-1 : ℝ)) / Rsel n|
      + |dz (zoomW (lam n) h (zc n) u) ((Rsel n, 0), (-1 : ℝ))|) :
    False :=
  false_of_finiteZoomCutoff_selection hC hh0 hh1 hzc hζ hb hsol haxi hlam0 hlam1 hlamTendsto hΩ0
    hA hc₀ hRmem
    (eventually_cutoffZoom_hlower_of_raw_selection hh0.le hh1 hzc hζ hsol hlam0 hlam1
      hlamTendsto hRmem hlowerRaw)

end CIV
