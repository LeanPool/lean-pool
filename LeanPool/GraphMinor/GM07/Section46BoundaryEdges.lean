/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46SeamPartsDefs
import LeanPool.GraphMinor.GM07.Section2MinVal
import LeanPool.GraphMinor.GM07.Section46RefinedEdges
import LeanPool.GraphMinor.GM07.PullForest

/-!
# Cuff edges and properness of `L`

The seam graph has only cuff edges and edges off the cuffs. Adding
vertices preserves this dichotomy. Thus deleting the cuff edges from
`J⁺` gives a proper drawing `L`, as required on page 226 of VII (4.6).
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- Every edge of the seam graph is either contained in the boundary or
disjoint from it, as used in VII (4.6), pages 225–226. -/
theorem Net.seam_edge_boundary_dichotomy {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {J : Drawing S} (hJ : N.IsSeamGraphFor J)
    {e : Set S} (he : e ∈ J.E) : e ⊆ bd S ∨ Disjoint e (bd S) := by
  have : T2Space S := hS.2.1
  rw [(N.seamGraph_edges_eq hS hJ).1] at he
  rcases he with ⟨i, rfl⟩ | hb
  · exact .inr (N.disjoint_e_int_bd hS i)
  · exact .inl (hb.2.1.trans sdiff_subset)

/-- Refining the seam by adding vertices preserves the cuff-edge
dichotomy in VII (4.6), page 226. -/
theorem Net.refined_edge_boundary_dichotomy {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {J J' : Drawing S}
    (hJ : N.IsSeamGraphFor J) {W : Set S} (hU : J'.U = J.U) (hV : J'.V = J.V ∪ W)
    {f : Set S} (hf : f ∈ J'.E) : f ⊆ bd S ∨ Disjoint f (bd S) := by
  obtain ⟨e, he, hfe⟩ := refined_edge_subset_old_edge hU hV hf
  rcases N.seam_edge_boundary_dichotomy hS hJ he with hbd | hoff
  · exact .inl (hfe.trans hbd)
  · exact .inr (hoff.mono_left hfe)

/-- The graph `L` obtained by deleting central and cuff edges is proper,
in VII (4.6), page 226. -/
theorem isProper_L {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {J J' L : Drawing S}
    (hJ : N.IsSeamGraphFor J) {W : Set S} (hU : J'.U = J.U) (hV : J'.V = J.V ∪ W)
    {central : Set (Set S)} (hLE : L.E = forestSeamEdges J' central) : L.IsProper := by
  intro x hx
  by_contra hxV
  obtain ⟨e, he, hxe⟩ := exists_edge_of_mem hx.2 hxV
  rw [hLE] at he
  have hoff := (N.refined_edge_boundary_dichotomy hS hJ hU hV he.1).resolve_left he.2.2
  exact disjoint_left.mp hoff hxe hx.1

end GraphMinor.GM07
