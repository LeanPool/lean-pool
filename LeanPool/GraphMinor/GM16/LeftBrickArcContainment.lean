/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.LeftRectangleArc
import Mathlib.Tactic.Linarith

/-!
# The part of a left brick boundary outside the central rectangle

A left brick has width two. A boundary point outside the common
central open rectangle either lies at horizontal coordinate at
most one, or on the global top or bottom. The first points lie
on the three short sides. At a top or bottom corner the corresponding
horizontal side extends to width two. This is the boundary arc
shared with the outside face in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- The boundary points of a left brick outside the central rectangle
lie on its three-sided outer arc. -/
theorem left_brick_boundary_outside_central_subset_arc {M H y : ℝ}
    (hM : 3 < M) (hy : 0 ≤ y) (hyH : y + 1 ≤ H) {p : ℝ × ℝ}
    (hpFr : p ∈ frontier (Icc (0 : ℝ) 2 ×ˢ Icc y (y + 1)))
    (hpOut : p ∉ Ioo (1 : ℝ) (M - 1) ×ˢ Ioo (0 : ℝ) H) :
    p ∈ leftRectangleBoundaryArc 0 (if y=0 then 2 else 1)
      (if y+1=H then 2 else 1) y (y+1) := by
  have hpB := (isClosed_Icc.prod isClosed_Icc).frontier_subset hpFr
  have hEdges : p.2=y ∨ p.2=y+1 ∨ p.1=0 ∨ p.1=2 := by
    rw [frontier_prod_eq,isClosed_Icc.closure_eq,isClosed_Icc.closure_eq,
      frontier_Icc (by norm_num : (0 : ℝ)≤2),frontier_Icc (by linarith : y≤y+1)] at hpFr
    rcases hpFr with ⟨_,hpY⟩ | ⟨hpX,_⟩
    · rcases hpY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hpX with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have hb₁ : (1 : ℝ) ≤ (if y=0 then 2 else 1) := by split_ifs <;> norm_num
  have ht₁ : (1 : ℝ) ≤ (if y+1=H then 2 else 1) := by split_ifs <;> norm_num
  change p ∈ ((Icc 0 (if y=0 then 2 else 1) ×ˢ {y}) ∪ ({0} ×ˢ Icc y (y+1))) ∪
    (Icc 0 (if y+1=H then 2 else 1) ×ˢ {y+1})
  by_cases hLow : p.1 ≤ 1
  · rcases hEdges with h | h | h | h
    · exact Or.inl (Or.inl ⟨⟨hpB.1.1,hLow.trans hb₁⟩,h⟩)
    · exact Or.inr ⟨⟨hpB.1.1,hLow.trans ht₁⟩,h⟩
    · exact Or.inl (Or.inr ⟨h,hpB.2⟩)
    · exact (by linarith : False).elim
  · have hHigh : 1 < p.1 := lt_of_not_ge hLow
    have hOutsideY : p.2 ≤ 0 ∨ H ≤ p.2 := by
      by_cases hY : 0 < p.2
      · right
        by_contra hn
        exact hpOut ⟨⟨hHigh,by linarith [hpB.1.2]⟩,hY,lt_of_not_ge hn⟩
      · exact Or.inl (le_of_not_gt hY)
    rcases hOutsideY with hBot | hTop
    · have hy0 : y=0 := by linarith [hpB.2.1]
      have hpY : p.2=y := by linarith [hpB.2.1]
      rw [ite_eq_left hy0]
      exact Or.inl (Or.inl ⟨hpB.1,hpY⟩)
    · have hyTop : y+1=H := by linarith [hpB.2.2]
      have hpY : p.2=y+1 := by linarith [hpB.2.2]
      rw [ite_eq_left hyTop]
      exact Or.inr ⟨hpB.1,hpY⟩

end GraphMinor.GM16
