/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import Mathlib.Combinatorics.Graph.Simple
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section3c

/-!
# Edge disjointness in a subdivision path system

For XVI (4.2), page 54, distinct replacing paths meet only at branch
centres. If they shared an edge, both ends of that edge would be
centres. A path has no loop, so the two centres would be different.
They would be the two ends of both source edges, forcing those source
edges to be equal because the source graph is simple.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph Function GraphMinor.GM09
universe u v w

/-- The replacing paths for two different simple-graph edges are edge
disjoint once their vertex intersections are confined to centres. -/
theorem subdivision_paths_edge_disjoint
    {α : Type u} {β : Type v} {ν : Type w} {H : SimpleGraph ν} {G : Graph α β}
    (c : ν → α) (hc : Injective c) (P : H.edgeSet → Graph α β)
    (hPaths : ∀ e : H.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds G (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : H.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c) :
    ∀ e f : H.edgeSet, e ≠ f → Disjoint E(P e) E(P f) := by
  intro e f hne
  refine disjoint_left.mpr ?_
  intro g hge hgf
  obtain ⟨a, b, heq, hPe, hVe⟩ := hPaths e
  obtain ⟨d, z, hfq, hPf, hVf⟩ := hPaths f
  obtain ⟨x, y, hlink⟩ := (P e).exists_isLink_of_mem_edgeSet hge
  have hlG := hPe.le.isLink_mono hlink
  have hlF := (hPf.le.isLink_iff hgf).mpr hlG
  have hxy : x ≠ y := by
    intro hEq
    have hLoop : G.IsLoopAt g y := hEq ▸ hlG
    exact hPe.not_isLoopAt hge y hLoop
  have hxRange := hInter e f hne ⟨hlink.left_mem, hlF.left_mem⟩
  have hyRange := hInter e f hne ⟨hlink.right_mem, hlF.right_mem⟩
  have hxe : x ∈ Sym2.map c e.val := by
    have hx : x ∈ ({c a,c b} : Set α) := hVe ▸ ⟨hlink.left_mem, hxRange⟩
    simpa only [heq, Sym2.map_mk, Sym2.mem_iff, mem_insert_iff, mem_singleton_iff] using hx
  have hye : y ∈ Sym2.map c e.val := by
    have hy : y ∈ ({c a,c b} : Set α) := hVe ▸ ⟨hlink.right_mem, hyRange⟩
    simpa only [heq, Sym2.map_mk, Sym2.mem_iff, mem_insert_iff, mem_singleton_iff] using hy
  have hxf : x ∈ Sym2.map c f.val := by
    have hx : x ∈ ({c d,c z} : Set α) := hVf ▸ ⟨hlF.left_mem, hxRange⟩
    simpa only [hfq, Sym2.map_mk, Sym2.mem_iff, mem_insert_iff, mem_singleton_iff] using hx
  have hyf : y ∈ Sym2.map c f.val := by
    have hy : y ∈ ({c d,c z} : Set α) := hVf ▸ ⟨hlF.right_mem, hyRange⟩
    simpa only [hfq, Sym2.map_mk, Sym2.mem_iff, mem_insert_iff, mem_singleton_iff] using hy
  have heEnds := (Sym2.mem_and_mem_iff hxy).mp ⟨hxe,hye⟩
  have hfEnds := (Sym2.mem_and_mem_iff hxy).mp ⟨hxf,hyf⟩
  exact hne (Subtype.ext (Sym2.map.injective hc (heEnds.trans hfEnds.symm)))

end GraphMinor.GM16
