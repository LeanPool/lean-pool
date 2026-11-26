/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM16.RectangularLines
import LeanPool.GraphMinor.Surface.ArcTools

/-!
# A line around the left side of a rectangle

Join a bottom horizontal side, the left vertical side, and a top
horizontal side. Consecutive sides meet only in their common end,
so their union is a line. Different horizontal lengths allow the
corner bricks at the top or bottom of the wall as well as its
intermediate bricks in XVI (4.2).
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Surface

/-- The three sides of a left boundary arc, with independently chosen
bottom and top horizontal lengths. -/
def leftRectangleBoundaryArc (x bottom top y z : ℝ) : Set (ℝ × ℝ) :=
  ((Icc x bottom ×ˢ {y}) ∪ ({x} ×ˢ Icc y z)) ∪ (Icc x top ×ˢ {z})

/-- The three sides form a line from the bottom right end to the top right end. -/
theorem leftRectangleBoundaryArc_isLine {x bottom top y z : ℝ}
    (hBottom : x < bottom) (hTop : x < top) (hyz : y < z) :
    IsLineWithEnds (leftRectangleBoundaryArc x bottom top y z) (bottom,y) (top,z) := by
  have hB := (horizontal_interval_isLine hBottom y).symm
  have hV := vertical_interval_isLine x hyz
  have hT := horizontal_interval_isLine hTop z
  have hMeet₁ : (Icc x bottom ×ˢ {y}) ∩ ({x} ×ˢ Icc y z) = {(x,y)} := by
    ext p
    constructor
    · rintro ⟨hpB,hpV⟩
      exact mem_singleton_iff.mpr (Prod.ext hpV.1 hpB.2)
    · intro hp
      rw [mem_singleton_iff] at hp
      subst p
      exact ⟨⟨⟨le_rfl,hBottom.le⟩,rfl⟩,⟨rfl,le_rfl,hyz.le⟩⟩
  have hMeet₂ : ((Icc x bottom ×ˢ {y}) ∪ ({x} ×ˢ Icc y z)) ∩
      (Icc x top ×ˢ {z}) = {(x,z)} := by
    ext p
    constructor
    · rintro ⟨hp,hpT⟩
      rcases hp with hpB | hpV
      · exact (hyz.ne (hpB.2.symm.trans hpT.2)).elim
      · exact mem_singleton_iff.mpr (Prod.ext hpV.1 hpT.2)
    · intro hp
      rw [mem_singleton_iff] at hp
      subst p
      exact ⟨Or.inr ⟨rfl,hyz.le,le_rfl⟩,⟨le_rfl,hTop.le⟩,rfl⟩
  exact (hB.union hV hMeet₁).union hT hMeet₂

end GraphMinor.GM16
