/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.RectangularGridLines
import LeanPool.GraphMinor.GM16.LatticeLineIntersections

/-!
# Grid edges meet only at grid vertices

Classify each edge as a horizontal or vertical unit line. Distinct
parallel edges have distinct starting lattice points, so they meet
only at an end. A horizontal and a vertical edge meet at the point
with the vertical edge's first coordinate and the horizontal edge's
second coordinate. That point is still a vertex of the finite grid.
These are the intersection checks for XVI (4.2)'s planar wall.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph

/-- Lines assigned to different rectangular grid edges meet only at
vertex points of that same finite grid. -/
theorem rectangularGridLine_intersection {m n : ℕ}
    {e f : Sym2 (Fin m × Fin n)}
    (he : e ∈ (pathGraph m □ pathGraph n).edgeSet)
    (hf : f ∈ (pathGraph m □ pathGraph n).edgeSet) (hne : e ≠ f)
    {x : ℝ × ℝ} (hx : x ∈ rectangularGridLine e ∩ rectangularGridLine f) :
    ∃ z : Fin m × Fin n, rectangularGridPoint z = x := by
  rcases rectangularGridLine_spec he with ⟨i,j,h,heq,hL⟩ | ⟨i,j,h,heq,hL⟩ <;>
    rcases rectangularGridLine_spec hf with ⟨k,l,h',hfq,hL'⟩ | ⟨k,l,h',hfq,hL'⟩
  · rw [hL,hL'] at hx
    have hStart : (i.val,j.val) ≠ (k.val,l.val) := by
      intro hEq
      have hik : i = k := Fin.ext (congrArg Prod.fst hEq)
      have hjl : j = l := Fin.ext (congrArg Prod.snd hEq)
      subst k
      subst l
      exact hne (heq.trans hfq.symm)
    rcases horizontalLatticeLine_inter hStart hx with hPoint | hPoint
    · exact ⟨(i,j),hPoint.symm⟩
    · exact ⟨(⟨i.val+1,h⟩,j),hPoint.symm⟩
  · rw [hL,hL'] at hx
    exact ⟨(k,j),(horizontal_vertical_LatticeLine_inter hx).symm⟩
  · rw [hL,hL'] at hx
    exact ⟨(i,l),(horizontal_vertical_LatticeLine_inter ⟨hx.2,hx.1⟩).symm⟩
  · rw [hL,hL'] at hx
    have hStart : (i.val,j.val) ≠ (k.val,l.val) := by
      intro hEq
      have hik : i = k := Fin.ext (congrArg Prod.fst hEq)
      have hjl : j = l := Fin.ext (congrArg Prod.snd hEq)
      subst k
      subst l
      exact hne (heq.trans hfq.symm)
    rcases verticalLatticeLine_inter hStart hx with hPoint | hPoint
    · exact ⟨(i,j),hPoint.symm⟩
    · exact ⟨(i,⟨j.val+1,h⟩),hPoint.symm⟩

end GraphMinor.GM16
