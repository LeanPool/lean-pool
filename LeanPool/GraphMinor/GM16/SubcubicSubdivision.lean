/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.SubcubicEdgePaths
public import LeanPool.GraphMinor.GM16.GraphPathSystemUnion
import LeanPool.GraphMinor.GM16.SubdivisionPathDisjoint
import LeanPool.GraphMinor.GM09.Basic

/-!
# The subdivision subgraph of a subcubic minor

This supplies the graph assertion in the last paragraph of XVI
(4.2), page 54. Use the constructed centres and replacing paths,
which are pairwise edge disjoint and meet only at their common branch
centres. Their union, with isolated centres retained, is the required
subgraph. The explicit centre map and edge paths describe the
isomorphism with a subdivision of the original simple graph.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph Function GraphMinor.GM09
universe u v w

/-- The subdivision assertion used in XVI (4.2), page 54, with its
isomorphism specified by the centre map and the replacing edge paths. -/
theorem exists_subcubic_subdivision_with_minor {α : Type u} {β : Type v} {ν : Type w} [Finite ν]
    {H : SimpleGraph ν} {G : Graph α β} {ηv : ν → Set α} {ηe : Sym2 ν → β}
    (h : IsMinorModel (Graph.ofSimpleGraph H) G ηv ηe)
    (hDeg : ∀ v, (H.neighborSet v).ncard ≤ 3) :
    ∃ (N : Graph α β) (c : ν → α) (P : H.edgeSet → Graph α β),
      N ≤ G ∧ Injective c ∧ (∀ v, c v ∈ ηv v) ∧
      V(N) = range c ∪ ⋃ e, V(P e) ∧ E(N) = ⋃ e, E(P e) ∧
      (∀ e : H.edgeSet, ∃ a b, e.val = s(a,b) ∧ H.Adj a b ∧
        IsGraphPathWithEnds N (P e) (c a) (c b) ∧ ηe e.val ∈ E(P e) ∧
        V(P e) ∩ range c = {c a,c b}) ∧
      (∀ e f : H.edgeSet, e ≠ f → Disjoint E(P e) E(P f) ∧
        V(P e) ∩ V(P f) ⊆ range c) ∧
      ∃ ηv' : ν → Set α, IsMinorModel (Graph.ofSimpleGraph H) N ηv' ηe := by
  obtain ⟨c, P, hcInj, hc, hPaths, hInter, ηv', hModelN⟩ := exists_subcubic_edge_paths_with_minor h
    hDeg
  have hP : ∀ e, P e ≤ G := by
    intro e
    obtain ⟨_, _, _, _, hPath, _, _⟩ := hPaths e
    exact hPath.le
  have hC : range c ⊆ V(G) := by
    rintro _ ⟨v,rfl⟩
    exact h.vertex_subset v (mem_univ _) (hc v)
  have hDisj := subdivision_paths_edge_disjoint c hcInj P
    (fun e => by
      obtain ⟨a, b, he, _, hPath, _, hRange⟩ := hPaths e
      exact ⟨a, b, he, hPath, hRange⟩) hInter
  let N := pathSystemGraph G (range c) P
  refine ⟨N, c, P, pathSystemGraph_le hC hP, hcInj, hc,
    pathSystemGraph_vertexSet G (range c) P, pathSystemGraph_edgeSet hP, ?_, ?_,ηv',hModelN⟩
  · intro e
    obtain ⟨a, b, he, hAdj, hPath, hChosen, hRange⟩ := hPaths e
    exact ⟨a, b, he, hAdj, hPath.of_le (le_pathSystemGraph hP e), hChosen, hRange⟩
  · intro e f hne
    exact ⟨hDisj e f hne, hInter e f hne⟩

/-- The explicit subdivision subgraph and its replacing paths in XVI (4.2). -/
theorem exists_subcubic_subdivision {α : Type u} {β : Type v} {ν : Type w} [Finite ν]
    {H : SimpleGraph ν} {G : Graph α β} {ηv : ν → Set α} {ηe : Sym2 ν → β}
    (h : IsMinorModel (Graph.ofSimpleGraph H) G ηv ηe)
    (hDeg : ∀ v, (H.neighborSet v).ncard ≤ 3) :
    ∃ (N : Graph α β) (c : ν → α) (P : H.edgeSet → Graph α β),
      N ≤ G ∧ Injective c ∧ (∀ v, c v ∈ ηv v) ∧
      V(N) = range c ∪ ⋃ e, V(P e) ∧ E(N) = ⋃ e, E(P e) ∧
      (∀ e : H.edgeSet, ∃ a b, e.val = s(a,b) ∧ H.Adj a b ∧
        IsGraphPathWithEnds N (P e) (c a) (c b) ∧ ηe e.val ∈ E(P e) ∧
        V(P e) ∩ range c = {c a,c b}) ∧
      (∀ e f : H.edgeSet, e ≠ f → Disjoint E(P e) E(P f) ∧
        V(P e) ∩ V(P f) ⊆ range c) := by
  obtain ⟨N,c,P,hNG,hcInj,hc,hVN,hEN,hPaths,hInter,_⟩ :=
    exists_subcubic_subdivision_with_minor h hDeg
  exact ⟨N,c,P,hNG,hcInj,hc,hVN,hEN,hPaths,hInter⟩

end GraphMinor.GM16
