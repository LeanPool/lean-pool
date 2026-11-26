/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.Fan
import LeanPool.GraphMinor.GM11.Section7
import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.GM14.DiscSlope

/-!
# Which side of a boundary contains a path

A line with only one point on a boundary stays on the side containing
its other end. Remove the boundary end, use connectedness, and add
that end back. This justifies trimming the battlefield paths into the
annulus in XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe u
variable {S : Type u} [TopologicalSpace S]

/-- A line starting inside a closed set and meeting its frontier only
at its last end stays in the closed set. -/
theorem line_subset_closed_of_boundary_end {L D : Set S} {a b : S}
    (hD : IsClosed D) (hL : IsLineWithEnds L a b)
    (ha : a ∈ D) (hab : a ≠ b) (hb : b ∈ D)
    (hbd : L ∩ frontier D ⊆ {b}) : L ⊆ D := by
  have hconn : IsPreconnected (L \ {b}) := GraphMinor.GM11.IsLineWithEnds.isPreconnected_sdiff
    (Surface.IsLineWithEnds.symm hL)
  have hdis : Disjoint (L \ {b}) (frontier D) := by
    apply disjoint_left.mpr
    intro x hx hxf
    exact hx.2 (hbd ⟨hx.1, hxf⟩)
  have hsub : L \ {b} ⊆ D :=
    (GraphMinor.GM14.subset_or_disjoint_of_frontier hD hconn hdis).resolve_right
      (fun hd => hd.notMem_of_mem_left ⟨hL.left_mem, hab⟩ ha)
  intro x hx
  by_cases hxb : x = b
  · exact hxb ▸ hb
  · exact hsub ⟨hx, hxb⟩

/-- A line ending outside a closed set and meeting its frontier only
at its first end avoids the interior of the closed set. -/
theorem line_avoids_interior_of_boundary_start {L D : Set S} {a b : S}
    (hD : IsClosed D) (hL : IsLineWithEnds L a b)
    (ha : a ∈ frontier D) (hb : b ∉ D)
    (hbd : L ∩ frontier D ⊆ {a}) : Disjoint L (interior D) := by
  have hconn : IsPreconnected (L \ {a}) := GraphMinor.GM11.IsLineWithEnds.isPreconnected_sdiff hL
  have hdis : Disjoint (L \ {a}) (frontier D) := by
    apply disjoint_left.mpr
    intro x hx hxf
    exact hx.2 (hbd ⟨hx.1, hxf⟩)
  have hba : b ≠ a := fun heq => hb (heq.symm ▸ hD.frontier_subset ha)
  have hout : Disjoint (L \ {a}) D :=
    (GraphMinor.GM14.subset_or_disjoint_of_frontier hD hconn hdis).resolve_left
      (fun hs => hb (hs ⟨hL.right_mem, hba⟩))
  apply disjoint_left.mpr
  intro x hx hxi
  by_cases hxa : x = a
  · exact ha.2 (hxa ▸ hxi)
  · exact hout.notMem_of_mem_left ⟨hx, hxa⟩ (interior_subset hxi)

end GraphMinor.GM16
