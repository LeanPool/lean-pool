/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteZoomCutoffField
public import LeanPool.CIVAxisymmetric.Zoom.OperatorNormProd
public import LeanPool.CIVAxisymmetric.Zoom.PotentialVorticityRescaled
public import LeanPool.CIVAxisymmetric.Zoom.FiniteAxisSecondDerivativeBoundsV
public import LeanPool.CIVAxisymmetric.Zoom.FiniteAxisSecondDerivativeBoundsW
public import LeanPool.CIVAxisymmetric.Zoom.PassToLimit
public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric

/-!
# The cutoff-multiplied zoom fields: smoothness, axis, divergence, and the drift limit

For a shrinking zoom scale `lam n → 0⁺` and a moving axial offset `zc n` uniformly bounded by
`ζ < 1`, this file builds, for every `n`, the globally smooth fields

  `Vseq n := cutoffBump h zc hzc hζ (lam n) (hlam0 n) n * (zoomV (lam n) h (zc n) u ·, -1))`
  `Wseq n := cutoffBump h zc hzc hζ (lam n) (hlam0 n) n * (zoomW (lam n) h (zc n) u ·, -1))`

and proves each of the hypotheses of `CIV.step_finite_contradiction` other than the selection
bound `hlower`, which belongs to the (separately tracked) dichotomy argument that selects
`Rsel` and `c₀`:

- `hVsmooth`, `hWsmooth`: global `ContDiff ℝ (⊤ : ℕ∞)`, for every `n` — the repair this file
  is for; the raw zoom slices are smooth only on the preimage of `unitCylinder` at scale
  `lam n`, centre `zc n` (`CIV.FiniteZoomCutoffField`), and the cutoff makes the product
  globally smooth by vanishing identically outside a compact subset of that preimage.
- `haxis`: `Vseq n (0, 0) = 0` for every `n`, from `CIV.zoomV_axis` and axisymmetry.
- `hdivn`: the finite-`n` divergence identity `CIV.zoom_divergence_identity`, transported to
  `Vseq`/`Wseq` because the cutoff equals `1` near any fixed off-axis point once `n` is large.
- `hdWn`: `∂_R W_n → 0`, from the potential-vorticity identity `CIV.zoomOmega_eq` applied
  pointwise (not merely in the limit): `∂_R W_n = lam^{4h} ∂_Z V_n − R Ω_n`, and the first
  summand `→ 0` because `lam^{4h} → 0` while `∂_Z V_n` stays bounded
  (`CIV.abs_dz_zoomV_le`), so `∂_R W_n → 0` once `Ω_n → 0` is supplied (the endpoint vanishing of
  the comparison argument, `CIV/Zoom/ZoomLimitEndpoint.lean`, taken here as a hypothesis at the
  same moving centre `zc n`).

The zoom centre `zc : ℕ → ℝ` is one axial offset per stage, uniformly bounded by a single
`ζ < 1` (`hzc`, `hζ`) rather than fixed for every `n`: the finite-axis selection this adapter is
eventually fed (`CIV.exists_seq_three_terms_dichotomy`) returns a moving height sequence, not a
single real number.
-/

public section

open Set Filter Topology Metric
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### The cutoff-multiplied fields -/

/-- The cutoff-multiplied radial field at stage `n`. -/
@[expose] def cutoffZoomV (h : ℝ) (zc : ℕ → ℝ) {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    (u : ParabolicPoint → Vec3) (lam : ℕ → ℝ) (hlam0 : ∀ n, 0 < lam n) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => cutoffBump h zc hzc hζ (lam n) (hlam0 n) n q * zoomV (lam n) h (zc n) u (q, -1)

/-- The cutoff-multiplied vertical field at stage `n`. -/
@[expose] def cutoffZoomW (h : ℝ) (zc : ℕ → ℝ) {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    (u : ParabolicPoint → Vec3) (lam : ℕ → ℝ) (hlam0 : ∀ n, 0 < lam n) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => cutoffBump h zc hzc hζ (lam n) (hlam0 n) n q * zoomW (lam n) h (zc n) u (q, -1)

/-! ### The cutoff equals `1` throughout any bounded square, eventually -/

/-- For every compact bound `r`, once `n` is large enough that the cutoff's inner radius
exceeds `r`, the cutoff equals `1` throughout the sup-ball of radius `r`, so `Vseq n` (resp.
`Wseq n`) equals the raw zoom slice there and the raw slice's own `dr`/`dz` bounds transfer
directly. -/
theorem eventually_cutoffBump_eq_one_of_norm_le {h : ℝ} (hh1 : h < 1 / 2) {zc : ℕ → ℝ} {ζ : ℝ}
    (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n)
    (hlamTendsto : Tendsto lam atTop (nhds 0)) (r : ℝ) :
    ∀ᶠ n in atTop, ∀ q : ℝ × ℝ, ‖q‖ ≤ r → cutoffBump h zc hzc hζ (lam n) (hlam0 n) n q = 1 := by
  filter_upwards [eventually_cutoffBump_rIn_gt hh1 hzc hζ hlam0 hlamTendsto r] with n hn q hq
  exact (cutoffBump h zc hzc hζ (lam n) (hlam0 n) n).one_of_mem_closedBall
    (by rw [mem_closedBall, dist_eq_norm, sub_zero]; linarith only [hq, hn])

/-- The cutoff's own smoothness, restricted to the sup-ball where it equals `1`, is enough to
transport a `HasFDerivAt` fact of the raw slice to the cutoff-multiplied field: on that open
ball the two functions agree pointwise, so their derivatives agree too. -/
theorem cutoffZoomV_eqOn_ball {h : ℝ} {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    {u : ParabolicPoint → Vec3} {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n) (n : ℕ) {r : ℝ}
    (hr : ∀ q : ℝ × ℝ, ‖q‖ ≤ r → cutoffBump h zc hzc hζ (lam n) (hlam0 n) n q = 1) :
    Set.EqOn (cutoffZoomV h zc hzc hζ u lam hlam0 n)
      (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1)) {q | ‖q‖ ≤ r} := by
  intro q hq
  change cutoffBump h zc hzc hζ (lam n) (hlam0 n) n q * zoomV (lam n) h (zc n) u (q, -1) = _
  rw [hr q hq, one_mul]

theorem cutoffZoomW_eqOn_ball {h : ℝ} {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1)
    {u : ParabolicPoint → Vec3} {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n) (n : ℕ) {r : ℝ}
    (hr : ∀ q : ℝ × ℝ, ‖q‖ ≤ r → cutoffBump h zc hzc hζ (lam n) (hlam0 n) n q = 1) :
    Set.EqOn (cutoffZoomW h zc hzc hζ u lam hlam0 n)
      (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1)) {q | ‖q‖ ≤ r} := by
  intro q hq
  change cutoffBump h zc hzc hζ (lam n) (hlam0 n) n q * zoomW (lam n) h (zc n) u (q, -1) = _
  rw [hr q hq, one_mul]

/-! ### Global smoothness -/

/-- The raw radial zoom slice at scale `lam` and centre `zc` is `ContDiffOn ℝ (⊤ : ℕ∞)` on the
preimage of `unitCylinder` under the zoom map, because it is `lam` times the zeroth component of
`u` composed with the globally smooth `zoomPoint` map, and `u` itself is smooth wherever the
zoom point lands. -/
theorem contDiffOn_zoomV_slice {h zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => zoomV lam h zc u (q, -1))
      {q : ℝ × ℝ | zoomPoint lam h zc (q, -1) ∈ unitCylinder} := by
  have hzoomSmooth : ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => zoomPoint lam h zc (q, -1)) :=
    (contDiff_zoomPoint lam h zc).comp (contDiff_id.prodMk contDiff_const)
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => u (zoomPoint lam h zc (q, -1)) 0)
      {q : ℝ × ℝ | zoomPoint lam h zc (q, -1) ∈ unitCylinder} :=
    (contDiffOn_component hsol.1 0).comp hzoomSmooth.contDiffOn (fun q hq => hq)
  have heq : (fun q : ℝ × ℝ => zoomV lam h zc u (q, -1))
      = fun q : ℝ × ℝ => lam * u (zoomPoint lam h zc (q, -1)) 0 := rfl
  rw [heq]
  exact contDiffOn_const.mul hcomp

theorem contDiffOn_zoomW_slice {h zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => zoomW lam h zc u (q, -1))
      {q : ℝ × ℝ | zoomPoint lam h zc (q, -1) ∈ unitCylinder} := by
  have hzoomSmooth : ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => zoomPoint lam h zc (q, -1)) :=
    (contDiff_zoomPoint lam h zc).comp (contDiff_id.prodMk contDiff_const)
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => u (zoomPoint lam h zc (q, -1)) 2)
      {q : ℝ × ℝ | zoomPoint lam h zc (q, -1) ∈ unitCylinder} :=
    (contDiffOn_component hsol.1 2).comp hzoomSmooth.contDiffOn (fun q hq => hq)
  have heq : (fun q : ℝ × ℝ => zoomW lam h zc u (q, -1))
      = fun q : ℝ × ℝ => lam * lam ^ (2 * h) * u (zoomPoint lam h zc (q, -1)) 2 := rfl
  rw [heq]
  exact contDiffOn_const.mul hcomp

/-- `hVsmooth`: for every `n`, `Vseq n` is globally `ContDiff ℝ (⊤ : ℕ∞)`. -/
theorem contDiff_cutoffZoomV {h : ℝ} (hh0 : 0 ≤ h) {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ)
    (hζ : ζ < 1) {u : ParabolicPoint → Vec3} {pres : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsClassicalSolutionOn u pres f unitCylinder)
    {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffZoomV h zc hzc hζ u lam hlam0 n) :=
  contDiff_bump_mul_of_contDiffOn_of_subset_closedBall
    (cutoffBump h zc hzc hζ (lam n) (hlam0 n) n)
    (isOpen_unitCylinder_prod.preimage
      ((continuous_zoomPoint (lam n) h (zc n)).comp (continuous_id.prodMk continuous_const)))
    (contDiffOn_zoomV_slice hsol) (cutoffBump_safe hh0 hzc hζ (hlam0 n) (hlam1 n) n)

/-- `hWsmooth`: for every `n`, `Wseq n` is globally `ContDiff ℝ (⊤ : ℕ∞)`. -/
theorem contDiff_cutoffZoomW {h : ℝ} (hh0 : 0 ≤ h) {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ)
    (hζ : ζ < 1) {u : ParabolicPoint → Vec3} {pres : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsClassicalSolutionOn u pres f unitCylinder)
    {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffZoomW h zc hzc hζ u lam hlam0 n) :=
  contDiff_bump_mul_of_contDiffOn_of_subset_closedBall
    (cutoffBump h zc hzc hζ (lam n) (hlam0 n) n)
    (isOpen_unitCylinder_prod.preimage
      ((continuous_zoomPoint (lam n) h (zc n)).comp (continuous_id.prodMk continuous_const)))
    (contDiffOn_zoomW_slice hsol) (cutoffBump_safe hh0 hzc hζ (hlam0 n) (hlam1 n) n)

/-! ### The axis value -/

/-- `haxis`: `Vseq n (0, 0) = 0` for every `n`, since the cutoff is `1` at the origin (its
inner radius is always positive) and `zoomV` vanishes on the axis of an axisymmetric field. -/
theorem cutoffZoomV_axis_eq_zero {h : ℝ} (hh0 : 0 ≤ h) {zc : ℕ → ℝ} {ζ : ℝ}
    (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder) {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n)
    (hlam1 : ∀ n, lam n < 1) (n : ℕ) :
    cutoffZoomV h zc hzc hζ u lam hlam0 n (0, 0) = 0 := by
  have hb0 : cutoffBump h zc hzc hζ (lam n) (hlam0 n) n (0, 0) = 1 := by
    apply (cutoffBump h zc hzc hζ (lam n) (hlam0 n) n).one_of_mem_closedBall
    rw [mem_closedBall, dist_eq_norm, sub_zero]
    simpa using (cutoffBump h zc hzc hζ (lam n) (hlam0 n) n).rIn_pos.le
  have hzero : zoomV (lam n) h (zc n) u ((0, 0), (-1 : ℝ)) = 0 := by
    refine zoomV_axis (lam n) h (zc n) u haxi ?_
    have hsafe := cutoffBump_safe (lam := lam n) hh0 hzc hζ (hlam0 n) (hlam1 n) n
    refine hsafe ?_
    rw [mem_closedBall, dist_eq_norm, sub_zero]
    simpa using (cutoffBump h zc hzc hζ (lam n) (hlam0 n) n).rOut_pos.le
  change cutoffBump h zc hzc hζ (lam n) (hlam0 n) n (0, 0) *
      zoomV (lam n) h (zc n) u ((0, 0), (-1 : ℝ)) = 0
  rw [hzero, mul_zero]

/-! ### Eventually the cutoff-multiplied field's derivative reads off the raw slice -/

/-- Once `n` is large enough that the cutoff equals `1` on a neighbourhood of `p`, the raw
radial zoom slice has a Fréchet derivative at `p` equal to that of the cutoff-multiplied
field: the two functions agree on that whole open neighbourhood, so their derivatives agree,
by `HasFDerivAt.congr_of_eventuallyEq` applied to the globally smooth `Vseq n`'s own derivative
(`CIV.contDiff_cutoffZoomV`, unpacked through `contDiff_infty_iff_fderiv`). -/
theorem eventually_hasFDerivAt_zoomV_slice {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {lam : ℕ → ℝ}
    (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1) (hlamTendsto : Tendsto lam atTop (nhds 0))
    (p : ℝ × ℝ) :
    ∀ᶠ n in atTop, HasFDerivAt (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1))
      (fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n) p) p := by
  filter_upwards [eventually_cutoffBump_eq_one_of_norm_le hh1 hzc hζ hlam0 hlamTendsto
    (‖p‖ + 1)] with n hn
  have hVeq : Set.EqOn (cutoffZoomV h zc hzc hζ u lam hlam0 n)
      (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1)) {q : ℝ × ℝ | ‖q‖ ≤ ‖p‖ + 1} :=
    cutoffZoomV_eqOn_ball hzc hζ hlam0 n hn
  have hpmem : p ∈ ball (0 : ℝ × ℝ) (‖p‖ + 1) := by
    rw [mem_ball, dist_eq_norm, sub_zero]; linarith only
  have heqNhds : (fun q : ℝ × ℝ => zoomV (lam n) h (zc n) u (q, -1)) =ᶠ[nhds p]
      (cutoffZoomV h zc hzc hζ u lam hlam0 n) := by
    filter_upwards [isOpen_ball.mem_nhds hpmem] with q hq
    exact (hVeq (by rw [mem_ball, dist_eq_norm, sub_zero] at hq; exact hq.le)).symm
  have hCD : ContDiff ℝ (⊤ : ℕ∞) (cutoffZoomV h zc hzc hζ u lam hlam0 n) :=
    contDiff_cutoffZoomV hh0 hzc hζ hsol hlam0 hlam1 n
  have hHF : HasFDerivAt (cutoffZoomV h zc hzc hζ u lam hlam0 n)
      (fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n) p) p :=
    ((contDiff_infty_iff_fderiv.mp hCD).1 p).hasFDerivAt
  exact hHF.congr_of_eventuallyEq heqNhds

/-- The vertical counterpart of `eventually_hasFDerivAt_zoomV_slice`. -/
theorem eventually_hasFDerivAt_zoomW_slice {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {lam : ℕ → ℝ}
    (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1) (hlamTendsto : Tendsto lam atTop (nhds 0))
    (p : ℝ × ℝ) :
    ∀ᶠ n in atTop, HasFDerivAt (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1))
      (fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n) p) p := by
  filter_upwards [eventually_cutoffBump_eq_one_of_norm_le hh1 hzc hζ hlam0 hlamTendsto
    (‖p‖ + 1)] with n hn
  have hWeq : Set.EqOn (cutoffZoomW h zc hzc hζ u lam hlam0 n)
      (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1)) {q : ℝ × ℝ | ‖q‖ ≤ ‖p‖ + 1} :=
    cutoffZoomW_eqOn_ball hzc hζ hlam0 n hn
  have hpmem : p ∈ ball (0 : ℝ × ℝ) (‖p‖ + 1) := by
    rw [mem_ball, dist_eq_norm, sub_zero]; linarith only
  have heqNhds : (fun q : ℝ × ℝ => zoomW (lam n) h (zc n) u (q, -1)) =ᶠ[nhds p]
      (cutoffZoomW h zc hzc hζ u lam hlam0 n) := by
    filter_upwards [isOpen_ball.mem_nhds hpmem] with q hq
    exact (hWeq (by rw [mem_ball, dist_eq_norm, sub_zero] at hq; exact hq.le)).symm
  have hCD : ContDiff ℝ (⊤ : ℕ∞) (cutoffZoomW h zc hzc hζ u lam hlam0 n) :=
    contDiff_cutoffZoomW hh0 hzc hζ hsol hlam0 hlam1 n
  have hHF : HasFDerivAt (cutoffZoomW h zc hzc hζ u lam hlam0 n)
      (fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n) p) p :=
    ((contDiff_infty_iff_fderiv.mp hCD).1 p).hasFDerivAt
  exact hHF.congr_of_eventuallyEq heqNhds

/-- The cutoff-multiplied field's radial derivative reads off `dr` of the raw slice, once `n`
is large enough. -/
theorem eventually_fderiv_cutoffZoomV_apply_eq_dr {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {lam : ℕ → ℝ}
    (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1) (hlamTendsto : Tendsto lam atTop (nhds 0))
    (p : ℝ × ℝ) :
    ∀ᶠ n in atTop, fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n) p (1, 0)
      = dr (zoomV (lam n) h (zc n) u) (p, -1) := by
  filter_upwards [eventually_hasFDerivAt_zoomV_slice hh0 hh1 hzc hζ hsol hlam0 hlam1
    hlamTendsto p] with n hn
  exact (dr_eq_of_hasFDerivAt (zoomV (lam n) h (zc n) u) (-1) hn).symm

/-- The cutoff-multiplied field's axial derivative reads off `dz` of the raw slice, once `n`
is large enough. -/
theorem eventually_fderiv_cutoffZoomW_apply_eq_dz {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {lam : ℕ → ℝ}
    (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1) (hlamTendsto : Tendsto lam atTop (nhds 0))
    (p : ℝ × ℝ) :
    ∀ᶠ n in atTop, fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n) p (0, 1)
      = dz (zoomW (lam n) h (zc n) u) (p, -1) := by
  filter_upwards [eventually_hasFDerivAt_zoomW_slice hh0 hh1 hzc hζ hsol hlam0 hlam1
    hlamTendsto p] with n hn
  exact (dz_eq_of_hasFDerivAt (zoomW (lam n) h (zc n) u) (-1) hn).symm

/-- The cutoff-multiplied vertical field's radial derivative reads off `dr` of the raw slice,
once `n` is large enough. -/
theorem eventually_fderiv_cutoffZoomW_apply_eq_dr {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {lam : ℕ → ℝ}
    (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1) (hlamTendsto : Tendsto lam atTop (nhds 0))
    (p : ℝ × ℝ) :
    ∀ᶠ n in atTop, fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n) p (1, 0)
      = dr (zoomW (lam n) h (zc n) u) (p, -1) := by
  filter_upwards [eventually_hasFDerivAt_zoomW_slice hh0 hh1 hzc hζ hsol hlam0 hlam1
    hlamTendsto p] with n hn
  exact (dr_eq_of_hasFDerivAt (zoomW (lam n) h (zc n) u) (-1) hn).symm

/-- The cutoff-multiplied field's radial derivative also reads off `dr` of the raw slice for
`Wseq`, and the value at `p` reads off the raw slice, once `n` is large enough: the three
facts a single application of `zoom_divergence_identity` needs. -/
theorem eventually_cutoffZoom_divergence_eq_zero {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1)
    (hlamTendsto : Tendsto lam atTop (nhds 0)) {p : ℝ × ℝ} (hp : 0 < p.1) :
    ∀ᶠ n in atTop, fderiv ℝ (cutoffZoomV h zc hzc hζ u lam hlam0 n) p (1, 0)
      + cutoffZoomV h zc hzc hζ u lam hlam0 n p / p.1
      + fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n) p (0, 1) = 0 := by
  filter_upwards [eventually_fderiv_cutoffZoomV_apply_eq_dr hh0 hh1 hzc hζ hsol hlam0 hlam1
      hlamTendsto p,
    eventually_fderiv_cutoffZoomW_apply_eq_dz hh0 hh1 hzc hζ hsol hlam0 hlam1 hlamTendsto p,
    eventually_cutoffBump_eq_one_of_norm_le hh1 hzc hζ hlam0 hlamTendsto (‖p‖ + 1),
    eventually_cutoffBump_rIn_gt hh1 hzc hζ hlam0 hlamTendsto (‖p‖ + 1)] with n hVdr hWdz hbump
    hrIn
  have hVval : cutoffZoomV h zc hzc hζ u lam hlam0 n p = zoomV (lam n) h (zc n) u (p, -1) :=
    cutoffZoomV_eqOn_ball hzc hζ hlam0 n hbump (show ‖p‖ ≤ ‖p‖ + 1 by linarith only)
  have hpsafe : zoomPoint (lam n) h (zc n) (p, -1) ∈ unitCylinder := by
    apply cutoffBump_safe hh0 hzc hζ (hlam0 n) (hlam1 n) n
    rw [mem_closedBall, dist_eq_norm, sub_zero]
    have := (cutoffBump h zc hzc hζ (lam n) (hlam0 n) n).rIn_lt_rOut
    linarith only [hrIn, this]
  have hRne : p.1 ≠ 0 := hp.ne'
  have hident := zoom_divergence_identity (lam n) h (zc n) (hlam0 n) u pres f hsol haxi (p, -1)
    hpsafe hRne
  rw [hVdr, hWdz, hVval]
  linarith only [hident]

/-! ### The drift limit `∂_R W_n → 0`, from `Ω_n → 0` -/

/-- Once `n` is large enough that the zoom point at `p` lands in `unitCylinder`, it stays
there: this is the same threshold `eventually_cutoffBump_rIn_gt` supplies for the cutoff's
inner radius, chained through `cutoffBump_safe`. -/
theorem eventually_zoomPoint_slice_mem_unitCylinder {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {lam : ℕ → ℝ}
    (hlam0 : ∀ n, 0 < lam n) (hlam1 : ∀ n, lam n < 1) (hlamTendsto : Tendsto lam atTop (nhds 0))
    (p : ℝ × ℝ) :
    ∀ᶠ n in atTop, zoomPoint (lam n) h (zc n) (p, -1) ∈ unitCylinder := by
  filter_upwards [eventually_cutoffBump_rIn_gt hh1 hzc hζ hlam0 hlamTendsto ‖p‖] with n hn
  apply cutoffBump_safe hh0 hzc hζ (hlam0 n) (hlam1 n) n
  rw [mem_closedBall, dist_eq_norm, sub_zero]
  have := (cutoffBump h zc hzc hζ (lam n) (hlam0 n) n).rIn_lt_rOut
  linarith only [hn, this]

/-- The sandwich estimate for a sequence that is only *eventually* bounded: if `a n → 0` and
`|D n| ≤ M` for all large `n`, then `a n * D n → 0`. The eventual form is needed here
because the pointwise bound on `dz (zoomV …)` is only available once the zoom point at the
fixed test point `p` has entered `unitCylinder`. -/
theorem tendsto_zero_of_mul_eventually_bounded {a D : ℕ → ℝ} {M : ℝ}
    (ha : Tendsto a atTop (nhds 0)) (hD : ∀ᶠ n in atTop, |D n| ≤ M) :
    Tendsto (fun n => a n * D n) atTop (nhds 0) := by
  have habs : Tendsto (fun n => |a n| * M) atTop (nhds 0) := by
    have ha_abs : Tendsto (fun n => |a n|) atTop (nhds |(0 : ℝ)|) := ha.abs
    simpa using ha_abs.mul_const M
  refine squeeze_zero_norm' ?_ habs
  filter_upwards [hD] with n hDn
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hDn (abs_nonneg _)

/-- `hdWn`: the radial derivative of the cutoff-multiplied vertical field tends to `0`, once
`Ω_n → 0` at `p`, along the same moving centre `zc n`, is supplied. The pointwise
potential-vorticity identity `CIV.zoomOmega_eq` gives, at *every* large `n`,
`dr (zoomW …) = lam ^ (4h) dz (zoomV …) − R Ω_n`: the first summand tends to `0` because
`lam ^ (4h) → 0` while `dz (zoomV …)` stays uniformly bounded (`CIV.abs_dz_zoomV_le`), and the
second because `Ω_n → 0` by hypothesis. -/
theorem tendsto_fderiv_cutoffZoomW_apply_zero {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1 / 2)
    {zc : ℕ → ℝ} {ζ : ℝ} (hzc : ∀ n, |zc n| ≤ ζ) (hζ : ζ < 1) {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {C : ℝ} (hC : 0 ≤ C)
    (hb : AnisotropicBounds C h u) {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n)
    (hlam1 : ∀ n, lam n < 1) (hlamTendsto : Tendsto lam atTop (nhds 0))
    (hΩ0 : ∀ q : ℝ × ℝ, 0 < q.1 →
      Tendsto (fun n => zoomOmega (lam n) h (zc n) u (q, -1)) atTop (nhds 0))
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    Tendsto (fun n => fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n) p (1, 0)) atTop
      (nhds 0) := by
  have hlamW : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within lam hlamTendsto
      (Eventually.of_forall hlam0)
  have hDzbdd : ∀ᶠ n in atTop, |dz (zoomV (lam n) h (zc n) u) (p, -1)| ≤
      C * (1 : ℝ) ^ (-(1 / 2 : ℝ) - (1 / 2 - h)) := by
    filter_upwards [eventually_zoomPoint_slice_mem_unitCylinder hh0.le hh1 hzc hζ hlam0 hlam1
      hlamTendsto p] with n hn
    have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1.of_le (by norm_num)
    have hb' := abs_dz_zoomV_le C h (lam n) (zc n) (hlam0 n) u hb hu2 (p, -1) hn
    simpa using hb'
  have hM : (0 : ℝ) ≤ C * (1 : ℝ) ^ (-(1 / 2 : ℝ) - (1 / 2 - h)) := by
    simpa using hC
  have hnum : Tendsto (fun n =>
      (((lam n) ^ (2 * h)) ^ 2 * dz (zoomV (lam n) h (zc n) u) (p, -1))
      - p.1 * zoomOmega (lam n) h (zc n) u (p, -1)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n =>
        ((lam n) ^ (2 * h)) ^ 2 * dz (zoomV (lam n) h (zc n) u) (p, -1)) atTop (nhds 0) :=
      tendsto_zero_of_mul_eventually_bounded
        ((tendsto_zoomDeltaSq_nhdsWithin_zero hh0).comp hlamW) hDzbdd
    have h2 : Tendsto (fun n => p.1 * zoomOmega (lam n) h (zc n) u (p, -1)) atTop (nhds 0) := by
      have := (hΩ0 p hp).const_mul p.1
      simpa using this
    simpa using h1.sub h2
  have hdrEq : ∀ᶠ n in atTop, dr (zoomW (lam n) h (zc n) u) (p, -1) =
      (((lam n) ^ (2 * h)) ^ 2 * dz (zoomV (lam n) h (zc n) u) (p, -1))
        - p.1 * zoomOmega (lam n) h (zc n) u (p, -1) := by
    filter_upwards [eventually_zoomPoint_slice_mem_unitCylinder hh0.le hh1 hzc hζ hlam0 hlam1
      hlamTendsto p] with n hn
    have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1.of_le (by norm_num)
    have heq := zoomOmega_eq (lam n) h (zc n) (hlam0 n) u hu1 (p, -1) hn hp.ne'
    have hRne : (p, (-1 : ℝ)).1.1 ≠ 0 := hp.ne'
    field_simp at heq
    linarith only [heq]
  have hdr : Tendsto (fun n => dr (zoomW (lam n) h (zc n) u) (p, -1)) atTop (nhds 0) :=
    Tendsto.congr' (Filter.EventuallyEq.symm hdrEq) hnum
  have hFdr : ∀ᶠ n in atTop, fderiv ℝ (cutoffZoomW h zc hzc hζ u lam hlam0 n) p (1, 0)
      = dr (zoomW (lam n) h (zc n) u) (p, -1) :=
    eventually_fderiv_cutoffZoomW_apply_eq_dr hh0.le hh1 hzc hζ hsol hlam0 hlam1 hlamTendsto p
  exact Tendsto.congr' (Filter.EventuallyEq.symm hFdr) hdr

end CIV
