/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyLayer

/-!
# High-contrast homogenization: Provider.Transport.WhitneyCells

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Nesting of the aligned cells of one grid

The maximal filling of `l.two.grid.whitney` is run in the
coordinates of the grid it selects from, where the adapted cells of a rounded
geometry become the standard aligned triadic cubes: in their half-open
realizations these tile `ℝ^d` exactly, and any two of them, of any two scales,
are nested or disjoint.

This file records that tiling for the open realizations the formalization uses.
The aligned parent of the scale-`a` index `w` is the scale-`a+1` index
`⌊(w+1)/3⌋`, coordinatewise; a cell is contained in its parent, hence in each of
its iterated ancestors; two cells of any two scales that share a point are
nested, because the finer one lies in an ancestor of its own scale and distinct
cells of one scale are disjoint; and every point off the countable family of
grid faces lies in a cell of each scale, the face family being the null set the
covering statements discard.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-! ## The aligned parent -/

/-- **The aligned parent index.**  The scale-`a` cell of index `w` sits inside the
scale-`a+1` cell of index `gridParent w`, coordinatewise `⌊(w+1)/3⌋`; this is the
"aligned `u`-parent of scale `a+1`" of the selection rule of
`l.two.grid.whitney`(i). -/
@[expose]
def gridParent (w : Fin d → ℤ) : Fin d → ℤ :=
  fun i => (w i + 1) / 3

/-- **A standard aligned cube lies in its aligned parent.**  The parent index is
`⌊(w+1)/3⌋` coordinatewise, the unique scale-`a+1` index whose cube contains the
scale-`a` cube of index `w`. -/
theorem standardCell_subset_parent (a : ℤ) (w : Fin d → ℤ) :
    standardCell d a w ⊆ standardCell d (a + 1) (gridParent w) := by
  intro x hx
  rw [Recurrence.mem_standardCell_iff] at hx ⊢
  intro i
  show ((gridParent w i : ℝ) - 1 / 2) * (3 : ℝ) ^ (a + 1) < x i ∧
    x i < ((gridParent w i : ℝ) + 1 / 2) * (3 : ℝ) ^ (a + 1)
  rw [show gridParent w i = (w i + 1) / 3 from rfl]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have hpow : (3 : ℝ) ^ (a + 1) = 3 * (3 : ℝ) ^ a := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring
  obtain ⟨h1, h2⟩ := hx i
  have hloZ : 3 * ((w i + 1) / 3) ≤ w i + 1 := by omega
  have hhiZ : w i - 1 ≤ 3 * ((w i + 1) / 3) := by omega
  have hlo : (3 : ℝ) * (((w i + 1) / 3 : ℤ) : ℝ) ≤ (w i : ℝ) + 1 := by exact_mod_cast hloZ
  have hhi : (w i : ℝ) - 1 ≤ 3 * (((w i + 1) / 3 : ℤ) : ℝ) := by exact_mod_cast hhiZ
  have hL : (3 * (((w i + 1) / 3 : ℤ) : ℝ) - 3 / 2) * (3 : ℝ) ^ a ≤
      ((w i : ℝ) - 1 / 2) * (3 : ℝ) ^ a :=
    mul_le_mul_of_nonneg_right (by linarith only [hlo]) h3.le
  have hR : ((w i : ℝ) + 1 / 2) * (3 : ℝ) ^ a ≤
      (3 * (((w i + 1) / 3 : ℤ) : ℝ) + 3 / 2) * (3 : ℝ) ^ a :=
    mul_le_mul_of_nonneg_right (by linarith only [hhi]) h3.le
  rw [hpow]
  constructor
  · linarith only [h1, hL]
  · linarith only [h2, hR]

/-- **An aligned adapted cell lies in its aligned parent.** -/
theorem adaptedCellAt_subset_parent (q : Mat d) (a : ℤ) (w : Fin d → ℤ) :
    adaptedCellAt q a w ⊆ adaptedCellAt q (a + 1) (gridParent w) := by
  rw [Recurrence.adaptedCellAt_eq_image, Recurrence.adaptedCellAt_eq_image]
  exact Set.image_mono (standardCell_subset_parent a w)

/-- **An aligned adapted cell lies in each of its iterated ancestors.** -/
theorem adaptedCellAt_subset_ancestor (q : Mat d) (a : ℤ) (w : Fin d → ℤ) (k : ℕ) :
    adaptedCellAt q a w ⊆ adaptedCellAt q (a + (k : ℤ)) (gridParent^[k] w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := adaptedCellAt_subset_parent q (a + (k : ℤ)) (gridParent^[k] w)
    have hscale : a + ((k : ℤ) + 1) = a + (k : ℤ) + 1 := by ring
    rw [Function.iterate_succ_apply']
    push_cast
    rw [hscale]
    exact ih.trans hstep

/-! ## Two cells of any two scales are nested or disjoint -/

/-- **Cells of two scales that share a point are nested.**  The finer cell lies in
its own ancestor at the coarser scale, and distinct cells of one scale are
disjoint, so that ancestor is the coarser cell. -/
theorem adaptedCellAt_subset_of_mem_of_mem {q : Mat d} (hq : q.PosDef) {a b : ℤ}
    (hab : a ≤ b) {w v : Fin d → ℤ} {x : Vec d} (hxw : x ∈ adaptedCellAt q a w)
    (hxv : x ∈ adaptedCellAt q b v) : adaptedCellAt q a w ⊆ adaptedCellAt q b v := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b = a + (k : ℤ) := ⟨(b - a).toNat, by omega⟩
  subst hk
  have hanc := adaptedCellAt_subset_ancestor q a w k
  by_cases heq : gridParent^[k] w = v
  · rw [← heq]
    exact hanc
  · exact absurd (Recurrence.disjoint_adaptedCellAt hq (a + (k : ℤ)) heq)
      (Set.not_disjoint_iff.mpr ⟨x, hanc hxw, hxv⟩)

/-! ## Every point off the grid faces lies in a cell -/

/-- **The standard aligned cubes of one scale cover their complement of the grid
faces.**  Rounding each coordinate to the nearest multiple of `3^a` produces the
cube containing the point, unless the coordinate sits exactly on a face. -/
theorem exists_mem_standardCell {a : ℤ} {x : Vec d}
    (hx : ∀ (i : Fin d) (k : ℤ), x i ≠ ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ a) :
    ∃ w : Fin d → ℤ, x ∈ standardCell d a w := by
  have hc : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  refine ⟨fun i => ⌊x i / (3 : ℝ) ^ a + 1 / 2⌋, ?_⟩
  rw [Recurrence.mem_standardCell_iff]
  intro i
  set m : ℤ := ⌊x i / (3 : ℝ) ^ a + 1 / 2⌋ with hm
  have hcancel : x i / (3 : ℝ) ^ a * (3 : ℝ) ^ a = x i := div_mul_cancel₀ (x i) hc.ne'
  have hfloorle : ((m : ℝ)) ≤ x i / (3 : ℝ) ^ a + 1 / 2 := Int.floor_le _
  have hupper : x i / (3 : ℝ) ^ a < (m : ℝ) + 1 / 2 := by
    have := Int.lt_floor_add_one (x i / (3 : ℝ) ^ a + 1 / 2)
    rw [← hm] at this
    linarith only [this]
  have hlower : ((m : ℝ)) - 1 / 2 < x i / (3 : ℝ) ^ a := by
    rcases lt_or_eq_of_le hfloorle with h | h
    · linarith only [h]
    · exfalso
      refine hx i (m - 1) ?_
      have hstep : ((m : ℝ)) - 1 / 2 = x i / (3 : ℝ) ^ a := by rw [h]; ring
      have hxi : x i = (((m : ℝ)) - 1 / 2) * (3 : ℝ) ^ a := by rw [hstep, hcancel]
      rw [hxi]
      push_cast
      ring
  constructor
  · have := mul_lt_mul_of_pos_right hlower hc
    rwa [hcancel] at this
  · have := mul_lt_mul_of_pos_right hupper hc
    rwa [hcancel] at this

/-- The grid faces of one scale, carried to the grid of `q`, form a null set. -/
theorem volume_image_gridFaces (q : Mat d) (a : ℤ) :
    volume (matVecMul q '' ⋃ (i : Fin d) (k : ℤ),
      {z : Vec d | z i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ a}) = 0 :=
  Recurrence.volume_image_matVecMul_eq_zero q (Recurrence.volume_gridFaces a)

/-- **The aligned cells of one scale cover the complement of the grid faces.** -/
theorem exists_mem_adaptedCellAt {q : Mat d} (hq : q.PosDef) (a : ℤ) {x : Vec d}
    (hx : x ∉ matVecMul q '' ⋃ (i : Fin d) (k : ℤ),
      {z : Vec d | z i = ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ a}) :
    ∃ w : Fin d → ℤ, x ∈ adaptedCellAt q a w := by
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have hsurj : matVecMul q (matVecMul q⁻¹ x) = x := by
    show q *ᵥ q⁻¹ *ᵥ x = x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  set x' : Vec d := matVecMul q⁻¹ x with hx'
  have hface : ∀ (i : Fin d) (k : ℤ), x' i ≠ ((k : ℝ) + 1 / 2) * (3 : ℝ) ^ a := by
    intro i k hik
    exact hx ⟨x', Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨k, hik⟩⟩, hsurj⟩
  obtain ⟨w, hw⟩ := exists_mem_standardCell (a := a) hface
  exact ⟨w, by rw [Recurrence.adaptedCellAt_eq_image]; exact ⟨x', hw, hsurj⟩⟩

end

end Transport
end HighContrast
end HCPolySupport
