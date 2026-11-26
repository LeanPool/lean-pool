/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM01.Defs
public import LeanPool.GraphMinor.GM16.LatticeLines

/-!
# Coordinates and lines of a rectangular grid

A grid vertex `(i,j)` is placed at its lattice point. Each horizontal
edge uses the unit line beginning at its lower first coordinate, and
each vertical edge uses the unit line beginning at its lower second
coordinate. The rule is symmetric in the ends, so it defines a line
for an unordered edge name. This is the planar drawing underlying
the wall in XVI (4.2), page 53.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph

/-- The point assigned to a vertex of a finite rectangular grid. -/
def rectangularGridPoint {m n : ℕ} (x : Fin m × Fin n) : ℝ × ℝ :=
  latticePoint (x.1.val,x.2.val)

/-- The unit line rule on a pair of grid vertices. Values on pairs
that are not grid edges are unused. -/
def rectangularGridLinePair {m n : ℕ} (x y : Fin m × Fin n) : Set (ℝ × ℝ) :=
  if x.2 = y.2 then horizontalLatticeLine (min x.1.val y.1.val) (min x.2.val y.2.val)
  else verticalLatticeLine (min x.1.val y.1.val) (min x.2.val y.2.val)

/-- Reversing the ends leaves the line unchanged. -/
theorem rectangularGridLinePair_symm {m n : ℕ} (x y : Fin m × Fin n) :
    rectangularGridLinePair x y = rectangularGridLinePair y x := by
  simp only [rectangularGridLinePair,eq_comm,min_comm]

/-- The unit line assigned to an unordered grid edge. -/
def rectangularGridLine {m n : ℕ} : Sym2 (Fin m × Fin n) → Set (ℝ × ℝ) :=
  Sym2.lift ⟨rectangularGridLinePair,rectangularGridLinePair_symm⟩

/-- Evaluation of the grid line map. -/
theorem rectangularGridLine_mk {m n : ℕ} (x y : Fin m × Fin n) :
    rectangularGridLine s(x,y) = rectangularGridLinePair x y := by rfl

/-- Every grid edge is a positive horizontal or vertical unit edge,
with the assigned line in those same coordinates. -/
theorem rectangularGridLine_spec {m n : ℕ} {e : Sym2 (Fin m × Fin n)}
    (he : e ∈ (pathGraph m □ pathGraph n).edgeSet) :
    (∃ (i : Fin m) (j : Fin n) (h : i.val + 1 < m),
      e = s((i,j),(⟨i.val+1,h⟩,j)) ∧ rectangularGridLine e = horizontalLatticeLine i.val j.val) ∨
    (∃ (i : Fin m) (j : Fin n) (h : j.val + 1 < n),
      e = s((i,j),(i,⟨j.val+1,h⟩)) ∧ rectangularGridLine e = verticalLatticeLine i.val j.val) := by
  induction e with
  | h x y =>
    have hAdj : (pathGraph m □ pathGraph n).Adj x y := he
    rcases boxProd_adj.mp hAdj with ⟨hStep,hj⟩ | ⟨hStep,hi⟩
    · change (pathGraph m).Adj x.1 y.1 at hStep
      change x.2 = y.2 at hj
      have hjVal := congrArg Fin.val hj
      rcases pathGraph_adj.mp hStep with hs | hs
      · have hb : x.1.val + 1 < m := by omega
        have hY : (⟨x.1.val+1,hb⟩,x.2) = y := Prod.ext (Fin.ext hs) hj
        left
        refine ⟨x.1,x.2,hb,congrArg (fun t => s(x,t)) hY.symm,?_⟩
        rw [rectangularGridLine_mk,rectangularGridLinePair,ite_eq_left hj,
          min_eq_left (show x.1.val ≤ y.1.val by omega),min_eq_left (le_of_eq hjVal)]
      · have hb : y.1.val + 1 < m := by omega
        have hX : (⟨y.1.val+1,hb⟩,y.2) = x := Prod.ext (Fin.ext hs) hj.symm
        left
        refine ⟨y.1,y.2,hb,Sym2.eq_swap.trans (congrArg (fun t => s(y,t)) hX.symm),?_⟩
        rw [rectangularGridLine_mk,rectangularGridLinePair,ite_eq_left hj,
          min_eq_right (show y.1.val ≤ x.1.val by omega),min_eq_right (le_of_eq hjVal.symm)]
    · change (pathGraph n).Adj x.2 y.2 at hStep
      change x.1 = y.1 at hi
      have hiVal := congrArg Fin.val hi
      have hjNe : x.2 ≠ y.2 := hStep.ne
      rcases pathGraph_adj.mp hStep with hs | hs
      · have hb : x.2.val + 1 < n := by omega
        have hY : (x.1,⟨x.2.val+1,hb⟩) = y := Prod.ext hi (Fin.ext hs)
        right
        refine ⟨x.1,x.2,hb,congrArg (fun t => s(x,t)) hY.symm,?_⟩
        rw [rectangularGridLine_mk,rectangularGridLinePair,ite_eq_right hjNe,
          min_eq_left (le_of_eq hiVal),min_eq_left (show x.2.val ≤ y.2.val by omega)]
      · have hb : y.2.val + 1 < n := by omega
        have hX : (y.1,⟨y.2.val+1,hb⟩) = x := Prod.ext hi.symm (Fin.ext hs)
        right
        refine ⟨y.1,y.2,hb,Sym2.eq_swap.trans (congrArg (fun t => s(y,t)) hX.symm),?_⟩
        rw [rectangularGridLine_mk,rectangularGridLinePair,ite_eq_right hjNe,
          min_eq_right (le_of_eq hiVal.symm),min_eq_right (show y.2.val ≤ x.2.val by omega)]

end GraphMinor.GM16
