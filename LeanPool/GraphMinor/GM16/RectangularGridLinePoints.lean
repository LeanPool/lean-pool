/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.RectangularGridLines
import LeanPool.GraphMinor.Surface.ArcTools

/-!
# Ends and vertices of the grid lines

The coordinate map is injective. Each actual grid edge is drawn as a
line joining its two vertex points, and no other grid vertex lies on
that line. These are the incidence checks for the drawing of the wall
in XVI (4.2), page 53.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph GraphMinor.Surface

/-- Distinct finite grid vertices have distinct lattice points. -/
theorem rectangularGridPoint_injective (m n : ℕ) :
    Function.Injective (@rectangularGridPoint m n) := by
  intro x y heq
  have hi : (x.1.val : ℝ) = (y.1.val : ℝ) := congrArg Prod.fst heq
  have hj : (x.2.val : ℝ) = (y.2.val : ℝ) := congrArg Prod.snd heq
  exact Prod.ext (Fin.ext (Nat.cast_injective hi)) (Fin.ext (Nat.cast_injective hj))

/-- The line assigned to a grid edge joins its two prescribed ends. -/
theorem rectangularGridLine_isLine {m n : ℕ} {x y : Fin m × Fin n}
    (hAdj : (pathGraph m □ pathGraph n).Adj x y) :
    IsLineWithEnds (rectangularGridLine s(x,y)) (rectangularGridPoint x) (rectangularGridPoint y)
      := by
  rcases rectangularGridLine_spec (e := s(x,y)) hAdj with ⟨i,j,h,hEq,hLine⟩ | ⟨i,j,h,hEq,hLine⟩
  · rw [hLine]
    rcases Sym2.eq_iff.mp hEq with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · rw [hx,hy]
      exact horizontalLatticeLine_isLine i.val j.val
    · rw [hx,hy]
      exact (horizontalLatticeLine_isLine i.val j.val).symm
  · rw [hLine]
    rcases Sym2.eq_iff.mp hEq with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · rw [hx,hy]
      exact verticalLatticeLine_isLine i.val j.val
    · rw [hx,hy]
      exact (verticalLatticeLine_isLine i.val j.val).symm

/-- A grid vertex on the line of an actual grid edge is one of that
edge's ends. -/
theorem rectangularGridLine_vertex {m n : ℕ} {e : Sym2 (Fin m × Fin n)}
    (he : e ∈ (pathGraph m □ pathGraph n).edgeSet) {z : Fin m × Fin n}
    (hz : rectangularGridPoint z ∈ rectangularGridLine e) : z ∈ e := by
  rcases rectangularGridLine_spec he with ⟨i,j,h,hEq,hLine⟩ | ⟨i,j,h,hEq,hLine⟩
  · rw [hLine] at hz
    rcases latticePoint_mem_horizontal hz with hz | hz
    · rw [hEq,Sym2.mem_iff]
      exact Or.inl (Prod.ext (Fin.ext (congrArg Prod.fst hz)) (Fin.ext (congrArg Prod.snd hz)))
    · rw [hEq,Sym2.mem_iff]
      exact Or.inr (Prod.ext (Fin.ext (congrArg Prod.fst hz)) (Fin.ext (congrArg Prod.snd hz)))
  · rw [hLine] at hz
    rcases latticePoint_mem_vertical hz with hz | hz
    · rw [hEq,Sym2.mem_iff]
      exact Or.inl (Prod.ext (Fin.ext (congrArg Prod.fst hz)) (Fin.ext (congrArg Prod.snd hz)))
    · rw [hEq,Sym2.mem_iff]
      exact Or.inr (Prod.ext (Fin.ext (congrArg Prod.fst hz)) (Fin.ext (congrArg Prod.snd hz)))

end GraphMinor.GM16
