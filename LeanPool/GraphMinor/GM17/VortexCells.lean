/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.VortexPaint

/-!
# The cell graphs of the portrayal in XVII (13.1)

Third step of the proof of XVII (13.1), page 203. For a small society, the cell graph is the graph
of the society. For a lune it is a piece `X i` of the linear
decomposition, with the next vertex added (`gr`). We also define the map from nodes to vertices
(`nv`), and the sets `β(n)` (`bt`). The sets `β(n)` differ from those
of the paper at the first node of each cuff: we take `β` empty there, in place of `V(κ(n_k) ∩
κ(n_1))`. Since the `κ(n_i)` come from a linear decomposition,
this is enough, and it makes the axioms easier to check.

Then we prove the parts of (P1)-(P7) that are about graphs, one lemma for each.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface GM09 GM14 GM16 Graph

universe u v

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S] [T2Space S] {G : Graph α β} {Seg
  : Set (Society α β)} {D : Society α β → Set S} {ν : α → S} {ρ : ℕ}
  {V : ∀ m : Maj Seg, VortexCut m.1 (D m.1) ν ρ}

omit [T2Space S] in
theorem VortexCut.finite_V {s : Society α β} {E : Set S} (W : VortexCut s E ν ρ)
  (i : Fin W.k) : V(W.X i).Finite :=
  s.finite_V.subset (W.dec.le_G i).vertexSet_mono

omit [T2Space S] in
theorem VortexCut.finite_E {s : Society α β} {E : Set S} (W : VortexCut s E ν ρ)
  (i : Fin W.k) : E(W.X i).Finite :=
  s.finite_E.subset (W.dec.le_G i).edgeSet_mono

omit [T2Space S] in
theorem VortexCut.mem_between {s : Society α β} {E : Set S} (W : VortexCut s E ν ρ) {a b c : Fin
  W.k} (hab : a ≤ b) (hbc : b ≤ c) {v : α} (ha : v ∈ V(W.X a))
    (hc : v ∈ V(W.X c)) : v ∈ V(W.X b) := by
  have hle := (W.dec.inter_le a b c hab hbc).vertexSet_mono
  apply hle
  simp only [subgraphInter]
  exact ⟨ha, hc⟩

variable (V) in
/-- The graphs of the cells. -/
def gr : Idx V → Hypergraph α β
  | .inl a => Hypergraph.ofGraph a.1.G a.1.finite_V a.1.finite_E
  | .inr x => addVertex (Hypergraph.ofGraph ((V x.1).X x.2) ((V x.1).finite_V _)
    ((V x.1).finite_E _)) ((V x.1).t ((V x.1).nx x.2))

omit [T2Space S] in
theorem gr_inr_vertex (m : Maj Seg) (i : Fin (V m).k) : (gr V (.inr ⟨m, i⟩)).vertexSet
  = V((V m).X i) ∪ {(V m).t ((V m).nx i)} := rfl

omit [T2Space S] in
theorem gr_inr_edge (m : Maj Seg) (i : Fin (V m).k) : (gr V (.inr ⟨m, i⟩)).edgeSet = E((V m).X i)
  := rfl

omit [T2Space S] in
theorem gr_vertex_sub (i : Idx V) : (gr V i).vertexSet ⊆ V((soc V i).G) := by
  rcases i with a | ⟨m, a⟩
  · exact subset_rfl
  · rw [gr_inr_vertex]
    refine union_subset ((V m).dec.le_G a).vertexSet_mono ?_
    rintro _ rfl
    exact m.1.bar_subset (t_mem_bar m _)

omit [T2Space S] in
theorem gr_edge_sub (i : Idx V) : (gr V i).edgeSet ⊆ E((soc V i).G) := by
  rcases i with a | ⟨m, a⟩
  · exact subset_rfl
  · exact ((V m).dec.le_G a).edgeSet_mono

variable (hseg : IsGraphSegregation G Seg) (hGV : V(G).Finite) (hGE : E(G).Finite)

theorem ofGraph_le {A B : Graph α β} (h : A ≤ B) (hA : V(A).Finite) (hA' : E(A).Finite)
  (hB : V(B).Finite) (hB' : E(B).Finite) :
    Hypergraph.ofGraph A hA hA' ≤ Hypergraph.ofGraph B hB hB' := by
  refine ⟨h.vertexSet_mono, h.edgeSet_mono, fun e he => ?_⟩
  ext v
  simp only [Hypergraph.ends, Hypergraph.ofGraph, mem_ofPred_eq, Graph.Inc, h.isLink_eqOn he]

theorem exists_vertex_of_union {H : Graph α β} {P : Set (Graph α β)} (h : subgraphSUnion H P
  = H) {v : α} (hv : v ∈ V(H)) : ∃ A ∈ P, v ∈ V(A) := by
  have h1 : v ∈ V(subgraphSUnion H P) := h.symm ▸ hv
  simpa [subgraphSUnion] using h1

theorem exists_edge_of_union {H : Graph α β} {P : Set (Graph α β)} (h : subgraphSUnion H P
  = H) {e : β} (he : e ∈ E(H)) : ∃ A ∈ P, e ∈ E(A) := by
  have h1 : e ∈ E(subgraphSUnion H P) := h.symm ▸ he
  simp only [subgraphSUnion] at h1
  simpa only [mem_iUnion, exists_prop] using h1.2

include hseg

omit [T2Space S] in
theorem gr_le (i : Idx V) : gr V i ≤ Hypergraph.ofGraph G hGV hGE := by
  rcases i with a | ⟨m, a⟩
  · exact ofGraph_le (hseg.le _ a.2.1) _ _ _ _
  · have h := ofGraph_le (((V m).dec.le_G a).trans (hseg.le _ m.2.1))
      ((V m).finite_V a) ((V m).finite_E a) hGV hGE
    refine ⟨?_, ?_, fun e he => h.ends_eq e he⟩
    · exact (gr_vertex_sub (.inr ⟨m, a⟩)).trans (hseg.le _ m.2.1).vertexSet_mono
    · exact h.edgeSet_subset

omit [T2Space S] in
theorem cover_vertex {v : α} (hv : v ∈ V(G)) : ∃ i, v ∈ (gr V i).vertexSet := by
  obtain ⟨_, ⟨s, hs, rfl⟩, hvs⟩ := exists_vertex_of_union hseg.union_eq hv
  by_cases h3 : 3 < s.Ω.bar.ncard
  · let m : Maj Seg := ⟨s, hs, h3⟩
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ := exists_vertex_of_union (V m).dec.union_eq hvs
    exact ⟨.inr ⟨m, j⟩, Or.inl hj⟩
  · exact ⟨.inl ⟨s, hs, h3⟩, hvs⟩

omit [T2Space S] in
theorem cover_edge {e : β} (he : e ∈ E(G)) : ∃ i, e ∈ (gr V i).edgeSet := by
  obtain ⟨_, ⟨s, hs, rfl⟩, hes⟩ := exists_edge_of_union hseg.union_eq he
  by_cases h3 : 3 < s.Ω.bar.ncard
  · let m : Maj Seg := ⟨s, hs, h3⟩
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ := exists_edge_of_union (V m).dec.union_eq hes
    exact ⟨.inr ⟨m, j⟩, hj⟩
  · exact ⟨.inl ⟨s, hs, h3⟩, hes⟩

variable (harr : IsProperArrangement Seg D ν)
include harr

omit [T2Space S] harr in
theorem gr_edge_disjoint {i j : Idx V} (hij : i ≠ j) : Disjoint (gr V i).edgeSet (gr V j).edgeSet
  := by
  by_cases hs : soc V i = soc V j
  · rcases i with a | ⟨m, a⟩ <;> rcases j with b | ⟨m', b⟩
    · exact absurd (congrArg Sum.inl (Subtype.ext hs)) hij
    · exact absurd hs (soc_ne_of_mnr_maj a m')
    · exact absurd hs.symm (soc_ne_of_mnr_maj b m)
    · obtain rfl : m = m' := Subtype.ext hs
      have hab : a ≠ b := fun h => hij (h ▸ rfl)
      rw [gr_inr_edge, gr_inr_edge]
      rcases lt_or_gt_of_ne hab with h | h
      · exact (V m).dec.edge_disjoint _ _ h
      · exact ((V m).dec.edge_disjoint _ _ h).symm
  · exact (hseg.edge_disjoint _ (soc_mem V i) _ (soc_mem V j) hs).mono
      (gr_edge_sub i) (gr_edge_sub j)

omit [TopologicalSpace S] [T2Space S] harr in
/-- A vertex of a society that lies in a vertex of the arrangement belongs to the cyclic order of
that society. -/
theorem mem_bar_of_mem_graph {s : Society α β} (hs : s ∈ Seg) {v : α}
  (hv : v ∈ segregationVertices Seg) (hg : v ∈ V(s.G)) : v ∈ s.Ω.bar := by
  obtain ⟨s', hs', hv'⟩ : ∃ s' ∈ Seg, v ∈ s'.Ω.bar := by simpa [segregationVertices] using hv
  by_cases he : s' = s
  · exact he ▸ hv'
  · exact (hseg.vertex_inter_subset s' hs' s hs he ⟨s'.bar_subset hv', hg⟩).2

omit harr in
omit [T2Space S] in
/-- A vertex in two different societies belongs to the cyclic order of both. -/
theorem mem_bar_of_ne {i j : Idx V} (hs : soc V i ≠ soc V j) {v : α} (hi : v ∈ (gr V i).vertexSet)
  (hj : v ∈ (gr V j).vertexSet) : v ∈ (soc V i).Ω.bar :=
  (hseg.vertex_inter_subset _ (soc_mem V i) _ (soc_mem V j) hs ⟨gr_vertex_sub i hi, gr_vertex_sub j
    hj⟩).1

end GraphMinor.GM17
