/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
import LeanPool.GraphMinor.GM16.IntervalTiling
import Mathlib.Tactic.Linarith

/-!
# Coordinate bounds for the enclosed wall disc

All rows lie in the full outer rectangle and contain the same
central rectangle. Inside an open unit-height strip, a point of
the enclosed disc belongs to that strip's unique row. These
coordinate facts locate the portions of a brick boundary that
can meet the outside face in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set

/-- Global coordinate bounds for the enclosed row stack. -/
theorem wallEnclosedSet_bounds {θ : ℕ} {p : ℝ × ℝ} (hp : p ∈ wallEnclosedSet θ) :
    0 ≤ p.1 ∧ p.1 ≤ 2*(θ : ℝ) ∧ 0 ≤ p.2 ∧ p.2 ≤ ((θ-1 : ℕ) : ℝ) := by
  have hTop := rectangleStack_vertical_le hp
  obtain ⟨j,_,hpRow⟩ := mem_iUnion₂.mp hp
  have hLeft := wallRowLeft_bounds j
  have hxRight : wallRowRight θ j ≤ 2*(θ : ℝ) := by
    dsimp only [wallRowRight]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    linarith [hLeft.1]
  exact ⟨hLeft.1.trans hpRow.1.1,hpRow.1.2.trans hxRight,
    (Nat.cast_nonneg j).trans hpRow.2.1,hTop⟩

/-- Every row contains the common central horizontal interval. -/
theorem central_rectangle_subset_wallEnclosedSet {θ : ℕ} (hθ : 2 ≤ θ) :
    Icc (1 : ℝ) (2*(θ : ℝ)-1) ×ˢ Icc (0 : ℝ) ((θ-1 : ℕ) : ℝ) ⊆ wallEnclosedSet θ := by
  rintro p ⟨hx,hy⟩
  have hTile := interval_eq_union_unit (by omega : 1 ≤ θ-1)
  obtain ⟨j,hj,hyRow⟩ := mem_iUnion₂.mp (hTile ▸ hy)
  apply mem_iUnion₂.mpr
  refine ⟨j,hj,?_,hyRow⟩
  have hLeft := wallRowLeft_bounds j
  have hRight : 2*(θ : ℝ)-1 ≤ wallRowRight θ j := by
    dsimp only [wallRowRight]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    linarith [hLeft.2]
  exact ⟨hLeft.2.trans hx.1,hx.2.trans hRight⟩

/-- Within an open unit-height strip, only its own row of rectangles
can contain a point of the enclosed disc. -/
theorem wallEnclosedSet_mem_open_strip {θ j : ℕ} {p : ℝ × ℝ}
    (hp : p ∈ wallEnclosedSet θ) (hy : p.2 ∈ Ioo (j : ℝ) ((j : ℝ) + 1)) :
    j < θ-1 ∧ p.1 ∈ Icc (wallRowLeft j) (wallRowRight θ j) := by
  obtain ⟨k,hk,hRow⟩ := mem_iUnion₂.mp hp
  have hk₁ : k < j+1 := by exact_mod_cast (lt_of_le_of_lt hRow.2.1 hy.2)
  have hk₂ : j < k+1 := by exact_mod_cast (lt_of_lt_of_le hy.1 hRow.2.2)
  have hkj : k = j := by omega
  subst k
  exact ⟨hk,hRow.1⟩

/-- The common central open rectangle is inside the interior of the
enclosed wall disc. -/
theorem central_open_rectangle_subset_interior_wallEnclosedSet {θ : ℕ} (hθ : 2 ≤ θ) :
    Ioo (1 : ℝ) (2*(θ : ℝ)-1) ×ˢ Ioo (0 : ℝ) ((θ-1 : ℕ) : ℝ) ⊆
      interior (wallEnclosedSet θ) := by
  apply interior_maximal _ (isOpen_Ioo.prod isOpen_Ioo)
  intro p hp
  exact central_rectangle_subset_wallEnclosedSet hθ
    ⟨Ioo_subset_Icc_self hp.1,Ioo_subset_Icc_self hp.2⟩

end GraphMinor.GM16
