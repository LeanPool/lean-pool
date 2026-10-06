/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.Rescaling
public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric

/-!
# First-order chain rules for the zoomed fields

The zoom map `zoomPoint` of `eq:aniso:zoom:finite:variables` sends `((r, z), τ)` to the
point `(meridional (lam r) (zc + lam^(1-2h) z), lam² τ)`. Its time slot does not depend on
`r` or on `z`, so the `r`- and `z`-derivatives of a zoomed field are derivatives along a
straight line inside a *fixed* spatial slice `{t = lam² τ}`. Every derivative below is
therefore taken on `Vec3`, never on the parabolic carrier itself (design note R2:
`ParabolicPoint` carries the parabolic metric and no linear structure of its own).

The resulting formulas are the first-order part of `eq:aniso:zoom:fields`:
`∂_r V = lam² ∂₁u₁`, `∂_z V = lam · lam^{1-2h} ∂₃u₁`, and the analogous identities for
`W` and `S` with the extra factor `lam^{2h}`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Derivatives of the meridional line -/

/-- Moving the radial coordinate of a meridional point at speed `a` moves it along `e₁`. -/
theorem hasDerivAt_meridional_fst (a c x : ℝ) :
    HasDerivAt (fun s : ℝ => meridional (a * s) c) (a • basisVec 0) x := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [meridional, basisVec_apply] using (hasDerivAt_id x).const_mul a
  · simpa [meridional, basisVec_apply] using hasDerivAt_const x (0 : ℝ)
  · simpa [meridional, basisVec_apply] using hasDerivAt_const x c

/-- Moving the vertical coordinate of a meridional point at speed `a` moves it along `e₃`. -/
theorem hasDerivAt_meridional_snd (c b a x : ℝ) :
    HasDerivAt (fun s : ℝ => meridional c (b + a * s)) (a • basisVec 2) x := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [meridional, basisVec_apply] using hasDerivAt_const x c
  · simpa [meridional, basisVec_apply] using hasDerivAt_const x (0 : ℝ)
  · simpa [meridional, basisVec_apply] using
      ((hasDerivAt_id x).const_mul a).const_add b

/-! ### Chain rule inside a fixed time slice -/

/-- A component of a `C¹` field, read along a curve `f` that stays in the time slice of `z`
and passes through `z` with velocity `a • e_j`, has derivative `a ∂_j u_i (z)`. Only the
spatial slice `fun y : Vec3 => u (y, z.2)` is differentiated, so no linear structure on the
parabolic carrier is required. -/
theorem hasDerivAt_comp_spatialSlice {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) {f : ℝ → Vec3} {a x : ℝ} {j : Fin 3}
    (hf : HasDerivAt f (a • basisVec j) x) (hx : f x = z.1) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => u (f s, z.2) i)
      (a * spatialPartial (fun w => u w i) j z) x := by
  have hF : HasFDerivAt (fun y : Vec3 => u (y, z.2))
      (fderiv ℝ (fun y : Vec3 => u (y, z.2)) z.1) z.1 :=
    (differentiableAt_spatialSlice hu hz).hasFDerivAt
  have hcomp : HasDerivAt (fun s : ℝ => u (f s, z.2))
      ((fderiv ℝ (fun y : Vec3 => u (y, z.2)) z.1) (a • basisVec j)) x :=
    HasFDerivAt.comp_hasDerivAt_of_eq (hl := hF) (hf := hf) (hy := hx.symm)
  have hi := hasDerivAt_pi.1 hcomp i
  rw [spatialPartial_eq_fderiv_apply hu hz i j]
  simpa [map_smul] using hi

/-! ### The zoom map differentiated in `r` and in `z` -/

/-- Differentiating a component of `u ∘ zoomPoint` in the radial variable. -/
theorem hasDerivAt_zoom_component_r (lam h zc : ℝ) {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (i : Fin 3) :
    HasDerivAt (fun r : ℝ => u (zoomPoint lam h zc ((r, p.1.2), p.2)) i)
      (lam * spatialPartial (fun w => u w i) 0 (zoomPoint lam h zc p)) p.1.1 :=
  hasDerivAt_comp_spatialSlice hu hp
    (hasDerivAt_meridional_fst lam (zc + lam ^ (1 - 2 * h) * p.1.2) p.1.1) rfl i

/-- Differentiating a component of `u ∘ zoomPoint` in the vertical variable. -/
theorem hasDerivAt_zoom_component_z (lam h zc : ℝ) {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => u (zoomPoint lam h zc ((p.1.1, s), p.2)) i)
      (lam ^ (1 - 2 * h) * spatialPartial (fun w => u w i) 2 (zoomPoint lam h zc p)) p.1.2 :=
  hasDerivAt_comp_spatialSlice hu hp
    (hasDerivAt_meridional_snd (lam * p.1.1) zc (lam ^ (1 - 2 * h)) p.1.2) rfl i

/-! ### First-order chain rules for the rescaled fields -/

/-- `∂_r V_n` in terms of the radial partial derivative of `u_r`. -/
theorem dr_zoomV (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dr (zoomV lam h zc u) p
      = lam ^ 2 * spatialPartial (fun w => u w 0) 0 (zoomPoint lam h zc p) := by
  have hbase := (hasDerivAt_zoom_component_r lam h zc hu p hp 0).const_mul lam
  have heq : lam * (lam * spatialPartial (fun w => u w 0) 0 (zoomPoint lam h zc p))
      = lam ^ 2 * spatialPartial (fun w => u w 0) 0 (zoomPoint lam h zc p) := by ring
  rw [heq] at hbase
  exact hbase.deriv

/-- `∂_z V_n` in terms of the vertical partial derivative of `u_r`. -/
theorem dz_zoomV (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dz (zoomV lam h zc u) p
      = lam * lam ^ (1 - 2 * h) * spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc p) := by
  have hbase := (hasDerivAt_zoom_component_z lam h zc hu p hp 0).const_mul lam
  have heq : lam * (lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc p))
      = lam * lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 0) 2 (zoomPoint lam h zc p) := by ring
  rw [heq] at hbase
  exact hbase.deriv

/-- `∂_r W_n` in terms of the radial partial derivative of `u_z`. -/
theorem dr_zoomW (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dr (zoomW lam h zc u) p
      = lam ^ 2 * lam ^ (2 * h) * spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc p) := by
  have hbase := (hasDerivAt_zoom_component_r lam h zc hu p hp 2).const_mul (lam * lam ^ (2 * h))
  have heq : lam * lam ^ (2 * h) *
        (lam * spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc p))
      = lam ^ 2 * lam ^ (2 * h) *
        spatialPartial (fun w => u w 2) 0 (zoomPoint lam h zc p) := by ring
  rw [heq] at hbase
  exact hbase.deriv

/-- `∂_z W_n` in terms of the vertical partial derivative of `u_z`. -/
theorem dz_zoomW (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dz (zoomW lam h zc u) p
      = lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) * spatialPartial (fun w => u w 2) 2 (zoomPoint
        lam h zc p) := by
  have hbase := (hasDerivAt_zoom_component_z lam h zc hu p hp 2).const_mul (lam * lam ^ (2 * h))
  have heq : lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 2) 2 (zoomPoint lam h zc p))
      = lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
        spatialPartial (fun w => u w 2) 2 (zoomPoint lam h zc p) := by ring
  rw [heq] at hbase
  exact hbase.deriv

/-- `∂_r S_n` in terms of the radial partial derivative of `u_θ`. -/
theorem dr_zoomS (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dr (zoomS lam h zc u) p
      = lam ^ 2 * lam ^ (2 * h) * spatialPartial (fun w => u w 1) 0 (zoomPoint lam h zc p) := by
  have hbase := (hasDerivAt_zoom_component_r lam h zc hu p hp 1).const_mul (lam * lam ^ (2 * h))
  have heq : lam * lam ^ (2 * h) *
        (lam * spatialPartial (fun w => u w 1) 0 (zoomPoint lam h zc p))
      = lam ^ 2 * lam ^ (2 * h) *
        spatialPartial (fun w => u w 1) 0 (zoomPoint lam h zc p) := by ring
  rw [heq] at hbase
  exact hbase.deriv

/-- `∂_z S_n` in terms of the vertical partial derivative of `u_θ`. -/
theorem dz_zoomS (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) :
    dz (zoomS lam h zc u) p
      = lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) * spatialPartial (fun w => u w 1) 2 (zoomPoint
        lam h zc p) := by
  have hbase := (hasDerivAt_zoom_component_z lam h zc hu p hp 1).const_mul (lam * lam ^ (2 * h))
  have heq : lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 1) 2 (zoomPoint lam h zc p))
      = lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
        spatialPartial (fun w => u w 1) 2 (zoomPoint lam h zc p) := by ring
  rw [heq] at hbase
  exact hbase.deriv

end CIV
