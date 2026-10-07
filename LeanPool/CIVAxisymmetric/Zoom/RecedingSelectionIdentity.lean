/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.Receding
public import LeanPool.CIVAxisymmetric.Statements.RadialQuotient

/-!
# The receding-axis zoom: selected-point identities

These identities connect the recentred zoom variables at the *selected* rescaled time
`τ = -1` and radial coordinate `R` to the corresponding Cartesian meridional quantities
at the physical time `t = -λ²` and radius `rc + λR`. They are the receding-axis analog of
`CIV.Zoom.FiniteSelectionIdentity` and form the chain-rule bridge used in Step 3's
contradiction argument.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem zoomPointRec_selected_eq (lam h rc zc : ℝ) {t : ℝ} (hlamsq : lam ^ 2 = -t) (R : ℝ) :
    zoomPointRec lam h rc zc ((R, 0), (-1 : ℝ)) = (meridional (rc + lam * R) zc, t) := by
  unfold zoomPointRec
  have hfst : meridional (rc + lam * R) (zc + lam ^ (1 - 2 * h) * 0) = meridional (rc + lam * R)
    zc := by
    simp
  have hsnd : lam ^ 2 * (-1 : ℝ) = t := by
    rw [hlamsq]
    ring
  exact Prod.ext hfst hsnd

theorem meridional_selected_mem_unitCylinder_of_zoomPointRec {lam h rc zc t : ℝ}
    (hlamsq : lam ^ 2 = -t) {R : ℝ}
    (hp : zoomPointRec lam h rc zc ((R, 0), (-1 : ℝ)) ∈ unitCylinder) :
    (meridional (rc + lam * R) zc, t) ∈ unitCylinder := by
  rwa [zoomPointRec_selected_eq lam h rc zc hlamsq R] at hp

theorem neg_t_mul_meridionalQuantity_receding_selection_eq {h : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {t : ℝ} (ht : t < 0) {lam R rc zc : ℝ} (hlam : 0 < lam)
    (hR : R ≠ -(rc / lam)) (hlamsq : lam ^ 2 = -t)
    (hp : zoomPointRec lam h rc zc ((R, 0), (-1 : ℝ)) ∈ unitCylinder) :
    (-t) * (|CKN.spatialPartial (fun w => u w 0) 0 (meridional (rc + lam * R) zc, t)|
        + |radialQuotient u (meridional (rc + lam * R) zc, t)|
        + |CKN.spatialPartial (fun w => u w 2) 2 (meridional (rc + lam * R) zc, t)|)
      = |dr (zoomVRec lam h rc zc u) ((R, 0), (-1 : ℝ))|
        + |zoomVRec lam h rc zc u ((R, 0), (-1 : ℝ)) / (rc / lam + R)|
        + |dz (zoomWRec lam h rc zc u) ((R, 0), (-1 : ℝ))| := by
  have hnegt_pos : 0 < -t := by linarith only [ht]
  have hz0_ne : rc + lam * R ≠ 0 := by
    intro hzero
    apply hR
    have hlam_ne : lam ≠ 0 := hlam.ne'
    field_simp [hlam_ne]
    linarith only [hzero]
  have h_exp : lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) = lam ^ 2 := by
    calc
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h)
          = lam * (lam ^ (1 - 2 * h) * lam ^ (2 * h)) := by ring_nf
      _ = lam * lam ^ ((1 - 2 * h) + (2 * h)) := by
        rw [← Real.rpow_add hlam (1 - 2 * h) (2 * h)]
      _ = lam * lam ^ (1 : ℝ) := by ring_nf
      _ = lam * lam := by simp
      _ = lam ^ 2 := by ring_nf
  have hzp_eq : zoomPointRec lam h rc zc ((R, (0 : ℝ)), (-1 : ℝ)) = (meridional (rc + lam * R)
    zc, t) := by
    rw [zoomPointRec_selected_eq lam h rc zc hlamsq R]
  have hp_mem : zoomPointRec lam h rc zc ((R, (0 : ℝ)), (-1 : ℝ)) ∈ unitCylinder := hp
  have hRp : ((R, (0 : ℝ)), (-1 : ℝ)).1.1 ≠ -(rc / lam) := by
    simpa using hR
  have hsum1 : dr (zoomVRec lam h rc zc u) ((R, (0 : ℝ)), (-1 : ℝ))
      = (-t) * spatialPartial (fun w => u w 0) 0 ((meridional (rc + lam * R) zc, t) :
        ParabolicPoint) := by
    rw [dr_zoomVRec lam h rc zc u hu ((R, (0 : ℝ)), (-1 : ℝ)) hp_mem, hzp_eq, hlamsq]
  have hsum2 : zoomVRec lam h rc zc u ((R, (0 : ℝ)), (-1 : ℝ)) / (rc / lam + R)
      = (-t) * radialQuotient u (meridional (rc + lam * R) zc, t) := by
    rw [zoomVRec_div_eq lam h rc zc hlam u ((R, (0 : ℝ)), (-1 : ℝ)) hRp, hzp_eq, hlamsq]
    unfold radialQuotient
    simp [hz0_ne, meridional]
  have hsum3 : dz (zoomWRec lam h rc zc u) ((R, (0 : ℝ)), (-1 : ℝ))
      = (-t) * spatialPartial (fun w => u w 2) 2 ((meridional (rc + lam * R) zc, t) :
        ParabolicPoint) := by
    calc
      dz (zoomWRec lam h rc zc u) ((R, (0 : ℝ)), (-1 : ℝ))
          = lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
            spatialPartial (fun w => u w 2) 2 (zoomPointRec lam h rc zc ((R, (0 : ℝ)), (-1 :
              ℝ))) := by
        rw [dz_zoomWRec lam h rc zc u hu ((R, (0 : ℝ)), (-1 : ℝ)) hp_mem]
      _ = lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
            spatialPartial (fun w => u w 2) 2 ((meridional (rc + lam * R) zc, t) :
              ParabolicPoint) := by
        rw [hzp_eq]
      _ = lam ^ 2 * spatialPartial (fun w => u w 2) 2 ((meridional (rc + lam * R) zc, t) :
        ParabolicPoint) := by
        rw [h_exp]
      _ = (-t) * spatialPartial (fun w => u w 2) 2 ((meridional (rc + lam * R) zc, t) :
        ParabolicPoint) := by
        rw [hlamsq]
  rw [hsum1, hsum2, hsum3]
  simp only [abs_mul, abs_of_pos hnegt_pos]
  ring

end CIV
