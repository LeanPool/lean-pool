/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.Receding
public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric
public import LeanPool.CIVAxisymmetric.Setting.AngularMeanSmooth

/-!
# The raw (uncut) receding zoom slices are smooth on the preimage of `unitCylinder`

These are the receding-axis analogues of `CIV.contDiffOn_zoomV_slice` and
`CIV.contDiffOn_zoomW_slice` (`CIV/Zoom/FiniteZoomCutoffData.lean`).  The raw
receding zoom slices `zoomVRec`, `zoomWRec` at `τ = -1` are smooth on the preimage of
`unitCylinder` under the recentred zoom map, since that map is itself smooth (affine) and `u`
is smooth on `unitCylinder` — together with the pointwise `HasFDerivAt` facts this
openness-and-smoothness combination yields, the same shape as the finite-axis
`CIV.hasFDerivAt_zoomV_slice_of_mem` / `CIV.hasFDerivAt_zoomW_slice_of_mem`
(`CIV/Zoom/FiniteZoomCutoffBounds.lean`) already use to read off `dr`/`dz` as components of
the Frechet derivative wherever the raw slice is smooth.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Smoothness of the raw receding zoom slices -/

/-- The raw receding radial zoom slice at scale `lam` is `ContDiffOn ℝ (⊤ : ℕ∞)` on the
preimage of `unitCylinder` under the recentred zoom map, because it is `lam` times the
zeroth component of `u` composed with the globally smooth `zoomPointRec` map, and `u` itself is
smooth wherever the zoom point lands. -/
theorem contDiffOn_zoomVRec_slice {h rc zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => zoomVRec lam h rc zc u (q, -1))
      {q : ℝ × ℝ | zoomPointRec lam h rc zc (q, -1) ∈ unitCylinder} := by
  have hzoomSmooth : ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => zoomPointRec lam h rc zc (q, -1)) :=
    (contDiff_zoomPointRec lam h rc zc).comp (contDiff_id.prodMk contDiff_const)
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => u (zoomPointRec lam h rc zc (q, -1)) 0)
      {q : ℝ × ℝ | zoomPointRec lam h rc zc (q, -1) ∈ unitCylinder} :=
    (contDiffOn_component hsol.1 0).comp hzoomSmooth.contDiffOn (fun q hq => hq)
  have heq : (fun q : ℝ × ℝ => zoomVRec lam h rc zc u (q, -1))
      = fun q : ℝ × ℝ => lam * u (zoomPointRec lam h rc zc (q, -1)) 0 := rfl
  rw [heq]
  exact contDiffOn_const.mul hcomp

/-- The raw receding vertical zoom slice at scale `lam` is `ContDiffOn ℝ (⊤ : ℕ∞)` on the
preimage of `unitCylinder` under the recentred zoom map, because it is `lam * lam ^ (2 * h)`
times the second component of `u` composed with the globally smooth `zoomPointRec` map, and `u`
itself is smooth wherever the zoom point lands. -/
theorem contDiffOn_zoomWRec_slice {h rc zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => zoomWRec lam h rc zc u (q, -1))
      {q : ℝ × ℝ | zoomPointRec lam h rc zc (q, -1) ∈ unitCylinder} := by
  have hzoomSmooth : ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => zoomPointRec lam h rc zc (q, -1)) :=
    (contDiff_zoomPointRec lam h rc zc).comp (contDiff_id.prodMk contDiff_const)
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => u (zoomPointRec lam h rc zc (q, -1)) 2)
      {q : ℝ × ℝ | zoomPointRec lam h rc zc (q, -1) ∈ unitCylinder} :=
    (contDiffOn_component hsol.1 2).comp hzoomSmooth.contDiffOn (fun q hq => hq)
  have heq : (fun q : ℝ × ℝ => zoomWRec lam h rc zc u (q, -1))
      = fun q : ℝ × ℝ => lam * lam ^ (2 * h) * u (zoomPointRec lam h rc zc (q, -1)) 2 := rfl
  rw [heq]
  exact contDiffOn_const.mul hcomp

/-! ### Pointwise `HasFDerivAt` on the open set where the zoom point is in `unitCylinder` -/

/-- On the preimage of `unitCylinder`, the Fréchet derivative of the raw receding radial zoom
slice is read off `dr`, `dz`: it is `ContDiffOn` there (`contDiffOn_zoomVRec_slice`), and the
preimage is open, so `HasFDerivAt` holds pointwise and
`CIV.dr_eq_of_hasFDerivAt` / `CIV.dz_eq_of_hasFDerivAt` apply. -/
theorem hasFDerivAt_zoomVRec_slice_of_mem {h rc zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : zoomPointRec lam h rc zc (y, -1) ∈ unitCylinder) :
    HasFDerivAt (fun q : ℝ × ℝ => zoomVRec lam h rc zc u (q, -1))
      (fderiv ℝ (fun q : ℝ × ℝ => zoomVRec lam h rc zc u (q, -1)) y) y := by
  have hSopen : IsOpen {q : ℝ × ℝ | zoomPointRec lam h rc zc (q, -1) ∈ unitCylinder} :=
    isOpen_unitCylinder_prod.preimage
      ((continuous_zoomPointRec lam h rc zc).comp (continuous_id.prodMk continuous_const))
  exact (((contDiffOn_zoomVRec_slice hsol).contDiffAt (hSopen.mem_nhds hy)).differentiableAt
    (by norm_num)).hasFDerivAt

theorem hasFDerivAt_zoomWRec_slice_of_mem {h rc zc lam : ℝ} {u : ParabolicPoint → Vec3}
    {pres : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pres f unitCylinder) {y : ℝ × ℝ}
    (hy : zoomPointRec lam h rc zc (y, -1) ∈ unitCylinder) :
    HasFDerivAt (fun q : ℝ × ℝ => zoomWRec lam h rc zc u (q, -1))
      (fderiv ℝ (fun q : ℝ × ℝ => zoomWRec lam h rc zc u (q, -1)) y) y := by
  have hSopen : IsOpen {q : ℝ × ℝ | zoomPointRec lam h rc zc (q, -1) ∈ unitCylinder} :=
    isOpen_unitCylinder_prod.preimage
      ((continuous_zoomPointRec lam h rc zc).comp (continuous_id.prodMk continuous_const))
  exact (((contDiffOn_zoomWRec_slice hsol).contDiffAt (hSopen.mem_nhds hy)).differentiableAt
    (by norm_num)).hasFDerivAt

end CIV
