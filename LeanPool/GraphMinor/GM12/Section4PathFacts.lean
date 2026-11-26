/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Section4

/-!
# Path facts for the circuit cover

In XII (4.1), page 248, circuits enclosing the edges of a nontrivial
path cover its whole point set. Their insides are closed, so they contain
the edge closures. Every vertex of a nontrivial path is an end of an edge.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 Hypergraph

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]

omit [T1Space S] in
/-- Subdrawings induce subhypergraphs, with unchanged ends on their edges. -/
theorem subdrawing_toHypergraph_le {P K : Drawing S} (hs : P.IsSubdrawing K) :
    P.toHypergraph ≤ K.toHypergraph := by
  refine ⟨hs.1, hs.2, ?_⟩
  intro e he
  ext x
  change (e ∈ K.E ∧ x ∈ K.V ∧ x ∈ closure e) ↔
    (e ∈ P.E ∧ x ∈ P.V ∧ x ∈ closure e)
  constructor
  · rintro ⟨_, hx, hxe⟩
    have hm : x ∈ closure e ∩ P.V := by
      rw [hs.closure_inter_V he]
      exact ⟨hxe, hx⟩
    exact ⟨he, hm.2, hxe⟩
  · rintro ⟨_, hx, hxe⟩
    exact ⟨hs.2 he, hs.1 hx, hxe⟩

omit [T1Space S] in
private theorem link_left_closure {P : Drawing S} {e : Set S} {a b : S}
    (h : P.toGraph.IsLink e a b) : a ∈ closure e := by
  have hm : a ∈ closure e ∩ P.V := by rw [h.2.2.2]; simp
  exact hm.1

omit [T1Space S] in
/-- Every vertex of a walk with at least one edge lies in an edge closure. -/
theorem walk_vertex_in_edge_closure {P : Drawing S} {u v : S}
    (W : GraphWalk P.toGraph u v) (hpos : 0 < W.length)
    {x : S} (hx : x ∈ W.support) : ∃ e ∈ W.edges, x ∈ closure e := by
  induction W with
  | nil h => exact (Nat.lt_irrefl 0 hpos).elim
  | @cons a b c e h r ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨e, List.mem_cons_self, link_left_closure h⟩
    · by_cases hr : 0 < r.length
      · obtain ⟨f, hf, hxf⟩ := ih hr hx
        exact ⟨f, List.mem_cons_of_mem _ hf, hxf⟩
      · have hr0 : r.length = 0 := Nat.eq_zero_of_not_pos hr
        obtain ⟨hs, _⟩ := support_of_length_zero hr0
        have hxb : x = b := List.mem_singleton.mp (hs ▸ hx)
        subst x
        exact ⟨e, List.mem_cons_self, link_left_closure h.symm⟩

omit [T1Space S] in
/-- Closed sets enclosing all edges of a nontrivial path cover the path,
including its vertices. This is the cover assertion in XII (4.1), page 248. -/
theorem path_subset_edge_cover {P : Drawing S} {u v : S}
    (hP : P.IsPathBetween u v) (hne : u ≠ v)
    (D : P.E → Set S) (hclosed : ∀ e, IsClosed (D e))
    (hcover : ∀ e : P.E, (e : Set S) ⊆ D e) : P.U ⊆ ⋃ e, D e := by
  obtain ⟨W, _, hV, hE⟩ := hP
  have hpos : 0 < W.length := by
    cases W with
    | nil h => exact (hne rfl).elim
    | cons _ _ => exact Nat.zero_lt_succ _
  have hclosure : ∀ e : P.E, closure (e : Set S) ⊆ D e := fun e =>
    (hclosed e).closure_subset_iff.mpr (hcover e)
  intro x hx
  rw [P.U_eq] at hx
  rcases hx with hx | hx
  · have hxW : x ∈ W.support := by
      change x ∈ {x | x ∈ W.support}
      rw [← hV]
      exact hx
    obtain ⟨e, he, hxe⟩ := walk_vertex_in_edge_closure W hpos hxW
    have heP : e ∈ P.E := hE ▸ he
    exact mem_iUnion.mpr ⟨⟨e, heP⟩, hclosure ⟨e, heP⟩ hxe⟩
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨⟨e, he⟩, hclosure ⟨e, he⟩ hxe⟩

end GraphMinor.GM12
