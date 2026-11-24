/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.PullForest

/-!
# Edges after adding the cut vertices

For `J⁺` in VII (4.6), page 225, every new edge stays in an old edge.
An old edge containing no new vertex remains an edge. A drawing on one
closed old edge with exactly its marked vertices supplies actual edges
of `J⁺`. These facts identify the short, linking, and central edges.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

private theorem refined_off_vertices_subset {J J' : Drawing S} {W : Set S}
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ W) : J'.U \ J'.V ⊆ J.U \ J.V := by
  rw [hU, hV]
  exact sdiff_subset_sdiff_right subset_union_left

/-- A refined edge is contained in an old edge, in the construction of
`J⁺` in VII (4.6), page 225. -/
theorem refined_edge_subset_old_edge {J J' : Drawing S} {W : Set S}
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ W) {f : Set S} (hf : f ∈ J'.E) :
    ∃ e ∈ J.E, f ⊆ e := by
  have hsub := refined_off_vertices_subset hU hV
  obtain ⟨x, hxf⟩ := hf.1
  have hx := hsub (hf.2.1 hxf)
  obtain ⟨e, he, hxe⟩ := exists_edge_of_mem hx.1 hx.2
  have hconn := he.2.2.1.union hf.2.2.1 ⟨x, hxe, hxf⟩
  have heq := he.2.2.2 (e ∪ f) (union_subset he.2.1 (hf.2.1.trans hsub))
    hconn subset_union_left
  exact ⟨e, he, fun y hy => heq ▸ (Or.inr hy : y ∈ e ∪ f)⟩

/-- An edge disjoint from the new vertex set is unchanged, as for short
edges in VII (4.6), page 225. -/
theorem edge_mem_refinement_of_disjoint {J J' : Drawing S} {W : Set S}
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ W) {e : Set S} (he : e ∈ J.E)
    (hoff : Disjoint e W) : e ∈ J'.E := by
  refine ⟨he.1, ?_, he.2.2.1, ?_⟩
  · intro x hx
    have hxold := he.2.1 hx
    rw [hU, hV]
    exact ⟨hxold.1, fun h => h.elim hxold.2 (disjoint_left.mp hoff hx)⟩
  · intro D hD hc heD
    exact he.2.2.2 D (hD.trans (refined_off_vertices_subset hU hV)) hc heD

/-- Drawings on the marked closed old edges give actual edges of `J⁺`,
as used for the three pieces of a long edge in VII (4.6), page 225. -/
theorem local_marked_edge_mem_refinement {J J' P : Drawing S} {W : Set S}
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ W) {e : Set S} (he : e ∈ J.E)
    (hPU : P.U = closure e) (hPV : P.V = (J.V ∪ W) ∩ closure e)
    {f : Set S} (hf : f ∈ P.E) : f ∈ J'.E := by
  have hfe : f ⊆ e := by
    intro x hx
    have hxP := hf.2.1 hx
    rw [hPU, hPV] at hxP
    have hxV : x ∉ J.V := fun h => hxP.2 ⟨.inl h, hxP.1⟩
    exact J.closure_diff_V he ▸ (⟨hxP.1, hxV⟩ : x ∈ closure e \ J.V)
  have hfsub : f ⊆ J'.U \ J'.V := by
    intro x hx
    have hxP := hf.2.1 hx
    rw [hPU, hPV] at hxP
    rw [hU, hV]
    exact ⟨J.closure_subset_U he hxP.1, fun h => hxP.2 ⟨h, hxP.1⟩⟩
  refine ⟨hf.1, hfsub, hf.2.2.1, ?_⟩
  intro D hD hc hfD
  obtain ⟨x, hxf⟩ := hf.1
  have hsubold := refined_off_vertices_subset hU hV
  have hconn := he.2.2.1.union hc ⟨x, hfe hxf, hfD hxf⟩
  have heq := he.2.2.2 (e ∪ D) (union_subset he.2.1 (hD.trans hsubold))
    hconn subset_union_left
  have hDe : D ⊆ e := fun y hy => heq ▸ (Or.inr hy : y ∈ e ∪ D)
  apply hf.2.2.2 D _ hc hfD
  intro y hy
  have hynew := hD hy
  rw [hU, hV] at hynew
  rw [hPU, hPV]
  exact ⟨subset_closure (hDe hy), fun h => hynew.2 h.1⟩

end GraphMinor.GM07
