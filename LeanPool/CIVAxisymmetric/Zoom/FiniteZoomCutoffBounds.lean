/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteZoomCutoffData
public import LeanPool.CIVAxisymmetric.Zoom.VBoundedRectangle
public import LeanPool.CIVAxisymmetric.Analysis.ArzelaAscoliC1HalfPlane

/-!
# `hVbdd`/`hWbdd`: value and first-derivative operator-norm bounds on growing squares

For every fixed `j`, once `n` is large enough that the cutoff equals `1` throughout
`halfPlaneRectangle (j + 1)`, the cutoff-multiplied field coincides there with the raw zoom
slice, together with its Fréchet derivative — so the uniform, `n`-independent pointwise
bounds of `CIV.VBoundedRectangle` and `CIV.RescaledBounds` transfer directly, through the
dual-norm bound of `CIV.OperatorNormProd`.
-/

public section

open Set Filter Topology Metric
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Local agreement, as functions, on an open ball around a rectangle -/

/-- Every point of `halfPlaneRectangle j` has sup norm at most `j + 1`. -/
theorem norm_le_of_mem_halfPlaneRectangle {j : ℕ} {y : ℝ × ℝ} (hy : y ∈ halfPlaneRectangle j) :
    ‖y‖ ≤ (j : ℝ) + 1 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  refine max_le ?_ ?_
  · rw [abs_of_nonneg hy.1.1]; exact hy.1.2
  · exact abs_le.mpr ⟨hy.2.1, hy.2.2⟩

/-- Once `n` is large enough, the cutoff-multiplied radial field agrees with the raw zoom
slice, together with its Fréchet derivative, throughout `halfPlaneRectangle j`. -/
theorem eventually_forall_mem_halfPlaneRectangle_cutoffZoomV_eq {h : ℝ} (hh1 : h < 1 / 2)
    {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {u : ParabolicPoint → Vec3}
    {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n) (hlamTendsto : Tendsto lam atTop (nhds 0)) (j : ℕ) :
    ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      cutoffZoomV h zc hzc hζ u lam hlam0 n y = zoomV (lam n) h (zc n) u (y, -1) ∧
        fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n) y
          = fderiv ℝ (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1)) y := by
  filter_upwards [eventually_cutoffBump_eq_one_of_norm_le hh1 hzc hζ hlam0 hlamTendsto
    ((j : ℝ) + 2)] with n hn
  have heqOn : Set.EqOn (cutoffZoomV h zc hzc hζ u lam hlam0 n)
      (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1)) (ball (0 : ℝ × ℝ) ((j : ℝ) + 2)) := by
    intro q hq
    rw [mem_ball, dist_eq_norm, sub_zero] at hq
    exact cutoffZoomV_eqOn_ball hzc hζ hlam0 n hn hq.le
  intro y hy
  have hyball : y ∈ ball (0 : ℝ × ℝ) ((j : ℝ) + 2) := by
    rw [mem_ball, dist_eq_norm, sub_zero]
    linarith only [norm_le_of_mem_halfPlaneRectangle hy]
  refine ⟨heqOn hyball, ?_⟩
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [isOpen_ball.mem_nhds hyball] with q hq using heqOn hq

/-- The vertical counterpart of `eventually_forall_mem_halfPlaneRectangle_cutoffZoomV_eq`. -/
theorem eventually_forall_mem_halfPlaneRectangle_cutoffZoomW_eq {h : ℝ} (hh1 : h < 1 / 2)
    {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {u : ParabolicPoint → Vec3}
    {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n) (hlamTendsto : Tendsto lam atTop (nhds 0)) (j : ℕ) :
    ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      cutoffZoomW h zc hzc hζ u lam hlam0 n y = zoomW (lam n) h (zc n) u (y, -1) ∧
        fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n) y
          = fderiv ℝ (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1)) y := by
  filter_upwards [eventually_cutoffBump_eq_one_of_norm_le hh1 hzc hζ hlam0 hlamTendsto
    ((j : ℝ) + 2)] with n hn
  have heqOn : Set.EqOn (cutoffZoomW h zc hzc hζ u lam hlam0 n)
      (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1)) (ball (0 : ℝ × ℝ) ((j : ℝ) + 2)) := by
    intro q hq
    rw [mem_ball, dist_eq_norm, sub_zero] at hq
    exact cutoffZoomW_eqOn_ball hzc hζ hlam0 n hn hq.le
  intro y hy
  have hyball : y ∈ ball (0 : ℝ × ℝ) ((j : ℝ) + 2) := by
    rw [mem_ball, dist_eq_norm, sub_zero]
    linarith only [norm_le_of_mem_halfPlaneRectangle hy]
  refine ⟨heqOn hyball, ?_⟩
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [isOpen_ball.mem_nhds hyball] with q hq using heqOn hq

/-! ### The Fréchet derivative of the raw slice, read off `dr`/`dz`, wherever it is smooth -/

/-- On the preimage of `unitCylinder`, the Fréchet derivative of the raw radial zoom slice is
read off `dr`, `dz`: it is `ContDiffOn` there (`contDiffOn_zoomV_slice`), and the preimage is
open, so `HasFDerivAt` holds pointwise and `CIV.dr_eq_of_hasFDerivAt`/`dz_eq_of_hasFDerivAt`
apply. -/
theorem hasFDerivAt_zoomV_slice_of_mem {h zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : zoomPoint lam h zc (y, -1) ∈ unitCylinder) :
    HasFDerivAt (fun q : ℝ × ℝ => zoomV lam h zc u (q, -1))
      (fderiv ℝ (fun q : ℝ × ℝ => zoomV lam h zc u (q, -1)) y) y := by
  have hSopen : IsOpen {q : ℝ × ℝ | zoomPoint lam h zc (q, -1) ∈ unitCylinder} :=
    isOpen_unitCylinder_prod.preimage
      ((continuous_zoomPoint lam h zc).comp (continuous_id.prodMk continuous_const))
  exact (((contDiffOn_zoomV_slice hsol).contDiffAt (hSopen.mem_nhds hy)).differentiableAt
    (by norm_num)).hasFDerivAt

theorem hasFDerivAt_zoomW_slice_of_mem {h zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : zoomPoint lam h zc (y, -1) ∈ unitCylinder) :
    HasFDerivAt (fun q : ℝ × ℝ => zoomW lam h zc u (q, -1))
      (fderiv ℝ (fun q : ℝ × ℝ => zoomW lam h zc u (q, -1)) y) y := by
  have hSopen : IsOpen {q : ℝ × ℝ | zoomPoint lam h zc (q, -1) ∈ unitCylinder} :=
    isOpen_unitCylinder_prod.preimage
      ((continuous_zoomPoint lam h zc).comp (continuous_id.prodMk continuous_const))
  exact (((contDiffOn_zoomW_slice hsol).contDiffAt (hSopen.mem_nhds hy)).differentiableAt
    (by norm_num)).hasFDerivAt

/-! ### Uniform value and first-derivative bounds on the raw slices -/

/-- The uniform (`lam`-independent) value bound on the raw radial zoom slice at the frozen
time `τ = -1`. -/
theorem abs_zoomV_slice_le {C h zc lam : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) {y : ℝ × ℝ} (hy : zoomPoint lam h zc (y, -1) ∈ unitCylinder) :
    |zoomV lam h zc u (y, -1)| ≤ C := by
  have h1 := abs_zoomV_le C h lam zc hlam u hb (y, -1) hy
  simpa using h1

/-- The uniform value bound on the raw vertical zoom slice, dropping the swirl term. -/
theorem abs_zoomW_slice_le {C h zc lam : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {y : ℝ × ℝ}
    (hy : zoomPoint lam h zc (y, -1) ∈ unitCylinder) :
    |zoomW lam h zc u (y, -1)| ≤ C := by
  have h1 := abs_zoomW_add_abs_zoomS_le C h lam zc hlam u hb (y, -1) hy
  have h2 : |zoomW lam h zc u (y, -1)| ≤
      |zoomW lam h zc u (y, -1)| + |zoomS lam h zc u (y, -1)| :=
    le_add_of_nonneg_right (abs_nonneg _)
  have h3 : |zoomW lam h zc u (y, -1)| + |zoomS lam h zc u (y, -1)| ≤ C := by simpa using h1
  linarith only [h2, h3]

/-- The uniform operator-norm bound on the Fréchet derivative of the raw radial zoom slice. -/
theorem norm_fderiv_zoomV_slice_le {C h zc lam : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {pres : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : zoomPoint lam h zc (y, -1) ∈ unitCylinder) :
    ‖fderiv ℝ (fun q : ℝ × ℝ => zoomV lam h zc u (q, -1)) y‖ ≤ 2 * C := by
  have hHF := hasFDerivAt_zoomV_slice_of_mem hsol hy
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1.of_le (by norm_num)
  have heq1 : (fderiv ℝ (fun q : ℝ × ℝ => zoomV lam h zc u (q, -1)) y) (1, 0)
      = dr (zoomV lam h zc u) (y, -1) := (dr_eq_of_hasFDerivAt (zoomV lam h zc u) (-1) hHF).symm
  have heq2 : (fderiv ℝ (fun q : ℝ × ℝ => zoomV lam h zc u (q, -1)) y) (0, 1)
      = dz (zoomV lam h zc u) (y, -1) := (dz_eq_of_hasFDerivAt (zoomV lam h zc u) (-1) hHF).symm
  have hb1 : |dr (zoomV lam h zc u) (y, -1)| ≤ C := by
    have := abs_dr_zoomV_le C h lam zc hlam u hb hu2 (y, -1) hy
    simpa using this
  have hb2 : |dz (zoomV lam h zc u) (y, -1)| ≤ C := by
    have := abs_dz_zoomV_le C h lam zc hlam u hb hu2 (y, -1) hy
    simpa using this
  have hnorm := norm_clm_le_norm_apply_add_norm_apply
    (fderiv ℝ (fun q : ℝ × ℝ => zoomV lam h zc u (q, -1)) y)
  rw [heq1, heq2, Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
  linarith only [hnorm, hb1, hb2]

/-- The uniform operator-norm bound on the Fréchet derivative of the raw vertical zoom
slice. -/
theorem norm_fderiv_zoomW_slice_le {C h zc lam : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {pres : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : zoomPoint lam h zc (y, -1) ∈ unitCylinder) :
    ‖fderiv ℝ (fun q : ℝ × ℝ => zoomW lam h zc u (q, -1)) y‖ ≤ 2 * C := by
  have hHF := hasFDerivAt_zoomW_slice_of_mem hsol hy
  have heq1 : (fderiv ℝ (fun q : ℝ × ℝ => zoomW lam h zc u (q, -1)) y) (1, 0)
      = dr (zoomW lam h zc u) (y, -1) := (dr_eq_of_hasFDerivAt (zoomW lam h zc u) (-1) hHF).symm
  have heq2 : (fderiv ℝ (fun q : ℝ × ℝ => zoomW lam h zc u (q, -1)) y) (0, 1)
      = dz (zoomW lam h zc u) (y, -1) := (dz_eq_of_hasFDerivAt (zoomW lam h zc u) (-1) hHF).symm
  have hb1 : |dr (zoomW lam h zc u) (y, -1)| ≤ C := by
    have h1 : |dr (zoomW lam h zc u) (y, -1)| + |dr (zoomS lam h zc u) (y, -1)| ≤ C := by
      have := abs_dr_zoomW_add_abs_dr_zoomS_le C h lam zc hlam u hb
        (hsol.1.of_le (by norm_num)) (y, -1) hy
      simpa using this
    have h2 : |dr (zoomW lam h zc u) (y, -1)| ≤
        |dr (zoomW lam h zc u) (y, -1)| + |dr (zoomS lam h zc u) (y, -1)| :=
      le_add_of_nonneg_right (abs_nonneg _)
    linarith only [h1, h2]
  have hb2 : |dz (zoomW lam h zc u) (y, -1)| ≤ C := by
    have h1 : |dz (zoomW lam h zc u) (y, -1)| + |dz (zoomS lam h zc u) (y, -1)| ≤ C := by
      have := abs_dz_zoomW_add_abs_dz_zoomS_le C h lam zc hlam u hb
        (hsol.1.of_le (by norm_num)) (y, -1) hy
      simpa using this
    have h2 : |dz (zoomW lam h zc u) (y, -1)| ≤
        |dz (zoomW lam h zc u) (y, -1)| + |dz (zoomS lam h zc u) (y, -1)| :=
      le_add_of_nonneg_right (abs_nonneg _)
    linarith only [h1, h2]
  have hnorm := norm_clm_le_norm_apply_add_norm_apply
    (fderiv ℝ (fun q : ℝ × ℝ => zoomW lam h zc u (q, -1)) y)
  rw [heq1, heq2, Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
  linarith only [hnorm, hb1, hb2]

end CIV
