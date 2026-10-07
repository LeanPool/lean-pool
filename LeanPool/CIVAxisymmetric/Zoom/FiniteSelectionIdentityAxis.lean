/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteSelectionIdentity
public import LeanPool.CIVAxisymmetric.Identities.RadialQuotientBranches

/-!
The on-axis (`R = 0`) counterpart of `CIV.Zoom.FiniteSelectionIdentity`'s selected-point
identity for Step 2's contradiction (paragraph after `eq:aniso:zoom:finite:limit`): at the axis the
manuscript's `u_r/r` term is by definition `∂_r u_r` (`radialQuotient_on_axis`), so the identity
becomes `(-t)(2|∂_r u_r| + |∂_z u_z|) = 2|∂_R V_n| + |∂_Z W_n|` at `((0,0),-1)`, with no division
by the vanishing radius; this is the case the finite-axis dichotomy's on-axis branch needs and
that `CIV.Zoom.FiniteSelectionIdentity`'s own `R ≠ 0` hypothesis excludes.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem neg_t_mul_meridionalQuantity_selection_eq_of_axis {h : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {t : ℝ} (ht : t < 0) {lam zc : ℝ} (hlam : 0 < lam) (hlamsq : lam ^ 2 = -t)
    (hp : zoomPoint lam h zc ((0, 0), (-1 : ℝ)) ∈ unitCylinder) :
    (-t) * (|CKN.spatialPartial (fun w => u w 0) 0 (meridional 0 zc, t)|
        + |radialQuotient u (meridional 0 zc, t)|
        + |CKN.spatialPartial (fun w => u w 2) 2 (meridional 0 zc, t)|)
      = |dr (zoomV lam h zc u) ((0, 0), (-1 : ℝ))|
        + |dr (zoomV lam h zc u) ((0, 0), (-1 : ℝ))|
        + |dz (zoomW lam h zc u) ((0, 0), (-1 : ℝ))| := by
  set p : (ℝ × ℝ) × ℝ := ((0, 0), (-1 : ℝ)) with hp_def
  have hnegt_pos : 0 < -t := by linarith only [ht]
  have hzp_eq : zoomPoint lam h zc p = (meridional (0 : ℝ) zc, t) := by
    have hfst : (zoomPoint lam h zc p).1 = meridional (0 : ℝ) zc := by
      change meridional (lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2) = meridional (0 : ℝ) zc
      simp [hp_def]
    have hsnd : (zoomPoint lam h zc p).2 = t := by
      change lam ^ 2 * p.2 = t
      rw [hlamsq]; simp [hp_def]
    exact Prod.ext hfst hsnd
  have hstep1 : dr (zoomV lam h zc u) p
      = (-t) * CKN.spatialPartial (fun w => u w 0) 0 (meridional (0 : ℝ) zc, t) := by
    have := dr_zoomV lam h zc u hu p hp
    rw [hzp_eq] at this
    rw [this, hlamsq]
  have h_exp : lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) = lam ^ 2 := by
    calc
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) = lam * (lam ^ (1 - 2 * h) * lam ^ (2 * h)) := by ring
      _ = lam * lam ^ ((1 - 2 * h) + (2 * h)) := by rw [← Real.rpow_add hlam (1 - 2 * h) (2 * h)]
      _ = lam * lam ^ (1 : ℝ) := by
        have h_exp_simp : (1 - 2 * h) + (2 * h) = (1 : ℝ) := by ring
        rw [h_exp_simp]
      _ = lam * lam := by simp
      _ = lam ^ 2 := by ring
  have hstep3 : dz (zoomW lam h zc u) p
      = (-t) * CKN.spatialPartial (fun w => u w 2) 2 (meridional (0 : ℝ) zc, t) := by
    have := dz_zoomW lam h zc u hu p hp
    rw [hzp_eq] at this
    rw [this, h_exp, hlamsq]
  have haxis0 : (meridional (0 : ℝ) zc, t).1 0 = 0 := by simp [meridional]
  have hradq : radialQuotient u (meridional (0 : ℝ) zc, t)
      = CKN.spatialPartial (fun w => u w 0) 0 (meridional (0 : ℝ) zc, t) :=
    radialQuotient_on_axis u haxis0
  have habs1 : |dr (zoomV lam h zc u) p|
      = (-t) * |CKN.spatialPartial (fun w => u w 0) 0 (meridional (0 : ℝ) zc, t)| := by
    rw [hstep1, abs_mul, abs_of_pos hnegt_pos]
  have habs3 : |dz (zoomW lam h zc u) p|
      = (-t) * |CKN.spatialPartial (fun w => u w 2) 2 (meridional (0 : ℝ) zc, t)| := by
    rw [hstep3, abs_mul, abs_of_pos hnegt_pos]
  rw [hradq, habs1, habs3]
  ring

end CIV
