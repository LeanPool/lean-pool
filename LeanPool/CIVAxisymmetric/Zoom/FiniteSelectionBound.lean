/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteSelectionIdentityAxis
public import Mathlib.Analysis.Real.Sqrt

/-!
Upper bound on the selected sequence's scaled meridional quantity from
`eq:aniso:zoom:selected`, unifying `CIV.neg_t_mul_meridionalQuantity_selection_eq`
(the off-axis, `R ≠ 0` identity) and its axis counterpart
`CIV.neg_t_mul_meridionalQuantity_selection_eq_of_axis` (the `R = 0` case) into a
single inequality valid for every `R ≥ 0`. Step 2's contradiction argument needs
this bound to cover the axis-included range `R ∈ [0, A]`. -/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem neg_t_mul_meridionalQuantity_selection_le {h : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {t : ℝ} (ht : t < 0) {lam R zc : ℝ} (hlam : 0 < lam) (hR : 0 ≤ R)
    (hlamsq : lam ^ 2 = -t)
    (hp : zoomPoint lam h zc ((R, 0), (-1 : ℝ)) ∈ unitCylinder) :
    (-t) * (|CKN.spatialPartial (fun w => u w 0) 0 (meridional (lam * R) zc, t)|
        + |radialQuotient u (meridional (lam * R) zc, t)|
        + |CKN.spatialPartial (fun w => u w 2) 2 (meridional (lam * R) zc, t)|)
      ≤ 2 * |dr (zoomV lam h zc u) ((R, 0), (-1 : ℝ))|
        + |zoomV lam h zc u ((R, 0), (-1 : ℝ)) / R|
        + |dz (zoomW lam h zc u) ((R, 0), (-1 : ℝ))| := by
  rcases eq_or_lt_of_le hR with (hR0 | hR0)
  · -- axis branch: R = 0
    subst hR0
    have heq := neg_t_mul_meridionalQuantity_selection_eq_of_axis hu ht hlam hlamsq hp
    have hdiv : zoomV lam h zc u ((0, 0), (-1 : ℝ)) / (0 : ℝ) = 0 := div_zero _
    have hsum : |dr (zoomV lam h zc u) ((0, 0), (-1 : ℝ))|
        + |dr (zoomV lam h zc u) ((0, 0), (-1 : ℝ))|
        = 2 * |dr (zoomV lam h zc u) ((0, 0), (-1 : ℝ))| := by ring
    have hgoal : (-t) * (|CKN.spatialPartial (fun w => u w 0) 0 (meridional (lam * 0) zc, t)|
        + |radialQuotient u (meridional (lam * 0) zc, t)|
        + |CKN.spatialPartial (fun w => u w 2) 2 (meridional (lam * 0) zc, t)|)
        = 2 * |dr (zoomV lam h zc u) ((0, 0), (-1 : ℝ))|
          + |zoomV lam h zc u ((0, 0), (-1 : ℝ)) / (0 : ℝ)|
          + |dz (zoomW lam h zc u) ((0, 0), (-1 : ℝ))| := by
      simpa [mul_zero, hsum] using heq
    rw [hgoal, hdiv]
  · -- off-axis branch: R > 0
    have hR' : R ≠ 0 := hR0.ne'
    have heq := neg_t_mul_meridionalQuantity_selection_eq hu ht hlam hR' hlamsq hp
    rw [heq]
    have h_nonneg : 0 ≤ |dr (zoomV lam h zc u) ((R, 0), (-1 : ℝ))| := abs_nonneg _
    linarith only [h_nonneg]

theorem neg_t_mul_meridionalQuantity_selection_le_sqrt {h : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {t : ℝ} (ht : t < 0) {R zc : ℝ} (hR : 0 ≤ R)
    (hp : zoomPoint (Real.sqrt (-t)) h zc ((R, 0), (-1 : ℝ)) ∈ unitCylinder) :
    (-t) * (|CKN.spatialPartial (fun w => u w 0) 0 (meridional (Real.sqrt (-t) * R) zc, t)|
        + |radialQuotient u (meridional (Real.sqrt (-t) * R) zc, t)|
        + |CKN.spatialPartial (fun w => u w 2) 2 (meridional (Real.sqrt (-t) * R) zc, t)|)
      ≤ 2 * |dr (zoomV (Real.sqrt (-t)) h zc u) ((R, 0), (-1 : ℝ))|
        + |zoomV (Real.sqrt (-t)) h zc u ((R, 0), (-1 : ℝ)) / R|
        + |dz (zoomW (Real.sqrt (-t)) h zc u) ((R, 0), (-1 : ℝ))| := by
  have hlam : 0 < Real.sqrt (-t) := Real.sqrt_pos.mpr (by linarith only [ht])
  have hlamsq : (Real.sqrt (-t)) ^ 2 = -t := Real.sq_sqrt (by linarith only [ht] : (0 : ℝ) ≤ -t)
  exact neg_t_mul_meridionalQuantity_selection_le hu ht hlam hR hlamsq hp

theorem lt_of_neg_t_mul_meridionalQuantity_selection_lt {h : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {t c₀ : ℝ} (ht : t < 0) {lam R zc : ℝ} (hlam : 0 < lam) (hR : 0 ≤ R)
    (hlamsq : lam ^ 2 = -t)
    (hp : zoomPoint lam h zc ((R, 0), (-1 : ℝ)) ∈ unitCylinder)
    (hineq : c₀ < (-t) * (|CKN.spatialPartial (fun w => u w 0) 0 (meridional (lam * R) zc, t)|
        + |radialQuotient u (meridional (lam * R) zc, t)|
        + |CKN.spatialPartial (fun w => u w 2) 2 (meridional (lam * R) zc, t)|)) :
    c₀ < 2 * |dr (zoomV lam h zc u) ((R, 0), (-1 : ℝ))|
        + |zoomV lam h zc u ((R, 0), (-1 : ℝ)) / R|
        + |dz (zoomW lam h zc u) ((R, 0), (-1 : ℝ))| := by
  exact lt_of_lt_of_le hineq
    (neg_t_mul_meridionalQuantity_selection_le hu ht hlam hR hlamsq hp)

theorem lt_of_neg_t_mul_meridionalQuantity_selection_lt_sqrt {h : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {t c₀ : ℝ} (ht : t < 0) {R zc : ℝ} (hR : 0 ≤ R)
    (hp : zoomPoint (Real.sqrt (-t)) h zc ((R, 0), (-1 : ℝ)) ∈ unitCylinder)
    (hineq : c₀ < (-t) *
        (|CKN.spatialPartial (fun w => u w 0) 0 (meridional (Real.sqrt (-t) * R) zc, t)|
        + |radialQuotient u (meridional (Real.sqrt (-t) * R) zc, t)|
        + |CKN.spatialPartial (fun w => u w 2) 2 (meridional (Real.sqrt (-t) * R) zc, t)|)) :
    c₀ < 2 * |dr (zoomV (Real.sqrt (-t)) h zc u) ((R, 0), (-1 : ℝ))|
        + |zoomV (Real.sqrt (-t)) h zc u ((R, 0), (-1 : ℝ)) / R|
        + |dz (zoomW (Real.sqrt (-t)) h zc u) ((R, 0), (-1 : ℝ))| := by
  exact lt_of_lt_of_le hineq
    (neg_t_mul_meridionalQuantity_selection_le_sqrt hu ht hR hp)

end CIV
