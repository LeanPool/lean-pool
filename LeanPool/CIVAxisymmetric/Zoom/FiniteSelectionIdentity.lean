/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.DivergenceIdentity
public import LeanPool.CIVAxisymmetric.Statements.RadialQuotient

/-!
The chain-rule bridge between the meridional-plane quantities `∂_r u_r`, `u_r/r`, `∂_z u_z`
of `eq:aniso:zoom:selected` at a time `t < 0` and the finite-axis rescaled fields `V_n, W_n` of
`eq:aniso:zoom:fields`, evaluated at the corresponding rescaled point `(R, 0, -1)` with `lam² = -t`:
the identity that lets Step 2's contradiction (paragraph after `eq:aniso:zoom:finite:limit`)
read the selected sequence's scaled quantity off the zoom variables at `τ = -1`.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem neg_t_mul_meridionalQuantity_selection_eq {h : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {t : ℝ} (ht : t < 0) {lam R zc : ℝ} (hlam : 0 < lam) (hR : R ≠ 0)
    (hlamsq : lam ^ 2 = -t)
    (hp : zoomPoint lam h zc ((R, 0), (-1 : ℝ)) ∈ unitCylinder) :
    (-t) * (|CKN.spatialPartial (fun w => u w 0) 0 (meridional (lam * R) zc, t)|
        + |radialQuotient u (meridional (lam * R) zc, t)|
        + |CKN.spatialPartial (fun w => u w 2) 2 (meridional (lam * R) zc, t)|)
      = |dr (zoomV lam h zc u) ((R, 0), (-1 : ℝ))|
        + |zoomV lam h zc u ((R, 0), (-1 : ℝ)) / R|
        + |dz (zoomW lam h zc u) ((R, 0), (-1 : ℝ))| := by
  set p : (ℝ × ℝ) × ℝ := ((R, 0), (-1 : ℝ)) with hp_def
  have hnegt_pos : 0 < -t := by linarith only [ht]
  have hzp_eq : zoomPoint lam h zc p = (meridional (lam * R) zc, t) := by
    have hfst : (zoomPoint lam h zc p).1 = meridional (lam * R) zc := by
      change meridional (lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2) = meridional (lam * R) zc
      simp [hp_def]
    have hsnd : (zoomPoint lam h zc p).2 = t := by
      change lam ^ 2 * p.2 = t
      rw [hlamsq]
      simp [hp_def]
    exact Prod.ext hfst hsnd
  -- First summand: the radial derivative.
  have hstep1 : dr (zoomV lam h zc u) p
      = (-t) * CKN.spatialPartial (fun w => u w 0) 0 (meridional (lam * R) zc, t) := by
    have := dr_zoomV lam h zc u hu p hp
    rw [hzp_eq] at this
    rw [this, hlamsq]
  -- Third summand: the vertical derivative.
  have h_exp : lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) = lam ^ 2 := by
    calc
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) = lam * (lam ^ (1 - 2 * h) * lam ^ (2 * h)) := by
        ring
      _ = lam * lam ^ ((1 - 2 * h) + (2 * h)) := by rw [← Real.rpow_add hlam (1 - 2 * h) (2 * h)]
      _ = lam * lam ^ (1 : ℝ) := by
        have h_exp_simp : (1 - 2 * h) + (2 * h) = (1 : ℝ) := by ring
        rw [h_exp_simp]
      _ = lam * lam := by simp
      _ = lam ^ 2 := by ring
  have hstep3 : dz (zoomW lam h zc u) p
      = (-t) * CKN.spatialPartial (fun w => u w 2) 2 (meridional (lam * R) zc, t) := by
    have := dz_zoomW lam h zc u hu p hp
    rw [hzp_eq] at this
    rw [this, h_exp, hlamsq]
  -- Middle summand: the radial quotient.
  have hR' : p.1.1 ≠ 0 := by simpa [hp_def] using hR
  have hlamR_ne : lam * R ≠ 0 := mul_ne_zero hlam.ne' hR
  have hradq : radialQuotient u (meridional (lam * R) zc, t)
      = u (meridional (lam * R) zc, t) 0 / (lam * R) := by
    set zpt : ParabolicPoint := (meridional (lam * R) zc, t) with hzpt_def
    have hz0 : zpt.1 0 = lam * R := by simp [hzpt_def, meridional]
    have hz_ne : zpt.1 0 ≠ 0 := by rw [hz0]; exact hlamR_ne
    change radialQuotient u zpt = u zpt 0 / (lam * R)
    rw [radialQuotient, ite_eq_right hz_ne, hz0]
  have hstep2 : zoomV lam h zc u p / R
      = (-t) * radialQuotient u (meridional (lam * R) zc, t) := by
    have hdiv := zoomV_div_eq lam h zc hlam u p hR'
    have hpR : p.1.1 = R := by simp [hp_def]
    rw [hpR] at hdiv
    have hzfst : (zoomPoint lam h zc p).1 0 = lam * R := by
      rw [hzp_eq]; simp [meridional]
    rw [hzfst] at hdiv
    have huzp : u (zoomPoint lam h zc p) 0 = u (meridional (lam * R) zc, t) 0 := by
      rw [hzp_eq]
    rw [huzp] at hdiv
    rw [hdiv, hlamsq, hradq]
  have habs1 : |dr (zoomV lam h zc u) p|
      = (-t) * |CKN.spatialPartial (fun w => u w 0) 0 (meridional (lam * R) zc, t)| := by
    rw [hstep1, abs_mul, abs_of_pos hnegt_pos]
  have habs2 : |zoomV lam h zc u p / R|
      = (-t) * |radialQuotient u (meridional (lam * R) zc, t)| := by
    rw [hstep2, abs_mul, abs_of_pos hnegt_pos]
  have habs3 : |dz (zoomW lam h zc u) p|
      = (-t) * |CKN.spatialPartial (fun w => u w 2) 2 (meridional (lam * R) zc, t)| := by
    rw [hstep3, abs_mul, abs_of_pos hnegt_pos]
  rw [habs1, habs2, habs3]
  ring

end CIV
