/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM16.DrawingPointConnectivity
import LeanPool.GraphMinor.GM16.LineConnectedSubset
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM09.Basic

/-!
# A drawing supported on a line is a path

Join the two ends by a simple graph walk. Its drawing is a subdrawing
supported on a subline with the same ends. The interval property forces
that subline to be the whole line. A subdrawing with the same support
has all vertices and hence is the original drawing. This justifies the
path condition in the rigidity argument of XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface GM11

/-- A subdrawing with the same point set is the whole drawing. -/
theorem drawing_eq_of_subdrawing_of_U_eq {S : Type*} [TopologicalSpace S]
    {P D : Drawing S} (hPD : P.IsSubdrawing D) (hU : P.U = D.U) : P = D := by
  have hV : P.V = D.V := by
    apply subset_antisymm hPD.1
    intro x hx
    by_contra hn
    obtain ⟨e, he, hxe⟩ := P.exists_edge_of_mem (hU.symm ▸ D.V_subset_U hx) hn
    exact edge_notMem_V (hPD.2 he) hxe hx
  cases P
  cases D
  simp only at hU hV
  subst hU hV
  rfl

/-- A drawing whose point set is a line between two of its vertices is a path. -/
theorem drawing_isPathBetween_of_isLine_U {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Drawing S} {a b : S} (hL : IsLineWithEnds D.U a b)
    (hab : a ≠ b) (ha : a ∈ D.V) (hb : b ∈ D.V) : D.IsPathBetween a b := by
  have hU := isPreconnected_of_isLineWithEnds hL
  obtain ⟨W⟩ := drawing_walk_of_isPreconnected_U hU ha hb
  obtain ⟨W, hW, _, _⟩ := GraphMinor.GM09.exists_isSimple_subwalk W
  let P := walkDrawing D W
  have hP : P.IsPathBetween a b := walkDrawing_isPathBetween D hW
  have hPD : P.IsSubdrawing D := walkDrawing_isSubdrawing D W
  have hPL := isLine_of_isPathBetween hP hab
  have hPU := isPreconnected_of_isLineWithEnds hPL
  have heq := eq_line_of_preconnected_subset hL hPD.U_subset hPU
    hPL.left_mem hPL.right_mem
  exact drawing_eq_of_subdrawing_of_U_eq hPD heq ▸ hP

end GraphMinor.GM16
