/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ChainRule
public import LeanPool.CIVAxisymmetric.Identities.ScalarSystemDiv
public import LeanPool.CIVAxisymmetric.Statements.IsClassicalSolutionOn

/-!
# Divergence Identity

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- Off the axis, the rescaled radial velocity divided by `r` equals `lam²` times the
meridional radial component at the zoomed point. This is the algebraic identity
`eq:aniso:zoom:fields` for the `V` component. -/
theorem zoomV_div_eq (lam h zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (p : (ℝ × ℝ) × ℝ) (hR : p.1.1 ≠ 0) :
    zoomV lam h zc u p / p.1.1 = lam ^ 2 * (u (zoomPoint lam h zc p) 0 / (zoomPoint lam h zc
      p).1 0) := by
  unfold zoomV
  have hz0 : (zoomPoint lam h zc p).1 0 = lam * p.1.1 := by
    simp [zoomPoint, meridional]
  rw [hz0]
  field_simp [hR, hlam.ne']

/-- The divergence of the rescaled velocity field vanishes pointwise on the meridional plane
off the axis. This is `eq:aniso:zoom:finite:identities` — the zoom-in of the divergence-free
condition. -/
theorem zoom_divergence_identity (lam h zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (hR : p.1.1 ≠ 0) :
    dr (zoomV lam h zc u) p + zoomV lam h zc u p / p.1.1 + dz (zoomW lam h zc u) p = 0 := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hsol.1.of_le (by exact_mod_cast le_top)
  have hz0 : (zoomPoint lam h zc p).1 0 = lam * p.1.1 := by
    simp [zoomPoint, meridional]
  have hplane : (zoomPoint lam h zc p).1 1 = 0 := by
    simp [zoomPoint, meridional]
  have hr_zoom : (zoomPoint lam h zc p).1 0 ≠ 0 := by
    rw [hz0]
    exact mul_ne_zero hlam.ne' hR
  have h_exp : lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) = lam ^ 2 := by
    calc
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) = lam * (lam ^ (1 - 2 * h) * lam ^ (2 * h)) := by ring
      _ = lam * lam ^ ((1 - 2 * h) + (2 * h)) := by rw [← Real.rpow_add hlam (1 - 2 * h) (2 * h)]
      _ = lam * lam ^ (1 : ℝ) := by
        have h_exp_simp : (1 - 2 * h) + (2 * h) = (1 : ℝ) := by ring
        rw [h_exp_simp]
      _ = lam * lam := by simp
      _ = lam ^ 2 := by ring
  rw [dr_zoomV lam h zc u hu1 p hp, dz_zoomW lam h zc u hu1 p hp, zoomV_div_eq lam h zc hlam u p hR]
  rw [hz0]
  rw [h_exp]
  have h_scalar := scalar_nse_div u pr f hsol haxi (zoomPoint lam h zc p) hp hplane hr_zoom
  rw [hz0] at h_scalar
  calc
    lam ^ 2 * spatialPartial (fun w => u w 0) 0 (zoomPoint lam h zc p)
      + lam ^ 2 * (u (zoomPoint lam h zc p) 0 / (lam * p.1.1))
      + lam ^ 2 * spatialPartial (fun w => u w 2) 2 (zoomPoint lam h zc p)
        = lam ^ 2 * (spatialPartial (fun w => u w 0) 0 (zoomPoint lam h zc p)
            + u (zoomPoint lam h zc p) 0 / (lam * p.1.1)
            + spatialPartial (fun w => u w 2) 2 (zoomPoint lam h zc p)) := by ring
    _ = lam ^ 2 * 0 := by rw [h_scalar]
    _ = 0 := by ring

end CIV
