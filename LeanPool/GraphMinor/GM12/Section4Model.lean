/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.Minor.Model
import LeanPool.GraphMinor.GM10.TangleLemmas
import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Controlled models as graph minor models

The branch subgraphs in XII's definition of control give the branch sets
of a graph minor model. Joining edges do not belong to any branch: their
ends and branch disjointness force a loop at that branch, and the loop
condition excludes the edge there. Removing all joining edges therefore
leaves each branch connected. This is used for the contractions in (4.2).
-/

public section

namespace GraphMinor.GM12

open Set Graph Relation Hypergraph

private theorem link_of_inc_ne {α β : Type*} {G : Graph α β} {e : β} {x y : α}
    (hx : G.Inc e x) (hy : G.Inc e y) (hne : x ≠ y) : G.IsLink e x y := by
  obtain ⟨z, hxz⟩ := hx
  obtain ⟨w, hyw⟩ := hy
  rcases G.eq_or_eq_of_isLink_of_isLink hyw hxz.symm with rfl | rfl
  · exact hxz
  · exact (hne rfl).elim

/-- Keep the branch vertex sets of a controlled minor and regard them as
a minor model. The final two conditions retain exactly the size bound and
tangle-control condition for later composition. -/
theorem controlsMinor_has_minorModel {α β γ δ : Type*} {G : Graph α β}
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) {L : Graph γ δ}
    {θ : ℕ} {T : Set (Hypergraph α β × Hypergraph α β)}
    (hc : ControlsMinor (Hypergraph.ofGraph G hV hE) θ T L) :
    ∃ (ηv : γ → Set α) (ηe : δ → β), IsMinorModel L G ηv ηe ∧
      L.vertexSet.ncard ≤ θ ∧
      ∀ A B, (A, B) ∈ T → separationOrder A B < L.vertexSet.ncard →
        ∀ v ∈ L.vertexSet, ¬ ηv v ⊆ A.vertexSet := by
  classical
  obtain ⟨a, b, ha, hdisj, hlink, hloop, hinj, hcard, hcontrol⟩ := hc
  have heq : ∀ u ∈ L.vertexSet, ∀ v ∈ L.vertexSet, ∀ x,
      x ∈ (a u).vertexSet → x ∈ (a v).vertexSet → u = v := by
    intro u hu v hv x hxu hxv
    by_contra hne
    exact Set.disjoint_left.mp (hdisj u hu v hv hne) hxu hxv
  have hends : ∀ e u v, L.IsLink e u v →
      ∃ x ∈ (a u).vertexSet, ∃ y ∈ (a v).vertexSet, G.IsLink (b e) x y := by
    intro e u v hl
    by_cases huv : u = v
    · subst v
      obtain ⟨heG, _, hend⟩ := hloop e u hl
      obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet heG
      exact ⟨x, hend x hxy.inc_left, y, hend y hxy.inc_right, hxy⟩
    · obtain ⟨_, ⟨x, hx, hxe⟩, y, hy, hye⟩ := hlink e u v hl huv
      exact ⟨x, hx, y, hy, link_of_inc_ne hxe hye
        ((hdisj u hl.left_mem v hl.right_mem huv).ne_of_mem hx hy)⟩
  have hinc : ∀ v ∈ L.vertexSet, ∀ e ∈ L.edgeSet,
      L.Inc e v ↔ ∃ x ∈ (a v).vertexSet, G.Inc (b e) x := by
    intro v hv e he
    constructor
    · rintro ⟨w, hl⟩
      obtain ⟨x, hx, y, _, hxy⟩ := hends e v w hl
      exact ⟨x, hx, hxy.inc_left⟩
    · rintro ⟨x, hx, hxe⟩
      obtain ⟨p, q, hpq⟩ := L.exists_isLink_of_mem_edgeSet he
      obtain ⟨y, hy, z, hz, hyz⟩ := hends e p q hpq
      rcases hxe.eq_or_eq_of_isLink hyz with rfl | rfl
      · have hvp := heq v hv p hpq.left_mem x hx hy
        exact hvp.symm ▸ hpq.inc_left
      · have hvq := heq v hv q hpq.right_mem x hx hz
        exact hvq.symm ▸ hpq.inc_right
  have hloopiff : ∀ v ∈ L.vertexSet, ∀ e ∈ L.edgeSet,
      L.IsLoopAt e v ↔ ∀ x, G.Inc (b e) x → x ∈ (a v).vertexSet := by
    intro v hv e he
    constructor
    · exact fun hl => (hloop e v hl).2.2
    · intro hall
      obtain ⟨p, q, hpq⟩ := L.exists_isLink_of_mem_edgeSet he
      obtain ⟨x, hx, y, hy, hxy⟩ := hends e p q hpq
      have hpv := heq p hpq.left_mem v hv x hx (hall x hxy.inc_left)
      have hqv := heq q hpq.right_mem v hv y hy (hall y hxy.inc_right)
      subst p q
      exact hpq
  have havoid : ∀ v ∈ L.vertexSet, ∀ e ∈ L.edgeSet, b e ∉ (a v).edgeSet := by
    intro v hv e he heA
    have hall : ∀ x, G.Inc (b e) x → x ∈ (a v).vertexSet := by
      intro x hx
      exact (a v).vertex_mem_of_inc ((GM10.inc_iff_of_le (ha v hv).1 heA).mpr hx)
    exact (hloop e v ((hloopiff v hv e he).mpr hall)).2.1 heA
  refine ⟨fun v => (a v).vertexSet, b, ?_, hcard, hcontrol⟩
  refine {
    vertex_nonempty := fun v hv => (ha v hv).2.1
    vertex_subset := fun v hv => (ha v hv).1.vertexSet_subset
    edge_mem := ?_
    vertex_disjoint := hdisj
    edge_injOn := ?_
    inc_iff := hinc
    isLoopAt_iff := hloopiff
    connected := ?_ }
  · intro e he
    obtain ⟨u, v, hl⟩ := L.exists_isLink_of_mem_edgeSet he
    obtain ⟨x, _, y, _, hxy⟩ := hends e u v hl
    exact hxy.edge_mem
  · intro e he f hf hef
    by_contra hne
    exact hinj e he f hf hne hef
  · intro v hv
    let K := (G.induce (a v).vertexSet).deleteEdges (b '' L.edgeSet)
    refine ⟨K, ?_, ?_, (ha v hv).2.1, ?_⟩
    · exact ⟨(ha v hv).1.vertexSet_subset, fun _ _ _ h => ⟨h.1.1, h.2⟩⟩
    · rfl
    · intro x hx y hy
      obtain ⟨w⟩ := (ha v hv).2.2 x hx y hy
      induction w with
      | nil => exact .refl
      | @cons p q r hadj rest ih =>
        obtain ⟨hne, e, hep, heq'⟩ := hadj
        have hl : G.IsLink e p q := link_of_inc_ne
          (GM10.inc_of_le (ha v hv).1 hep) (GM10.inc_of_le (ha v hv).1 heq') hne
        have hn : e ∉ b '' L.edgeSet := by
          rintro ⟨f, hf, rfl⟩
          exact havoid v hv f hf ((a v).edge_mem_of_inc hep)
        exact Relation.ReflTransGen.head
          ⟨e, ⟨hl, (a v).vertex_mem_of_inc hep, (a v).vertex_mem_of_inc heq'⟩, hn⟩ (ih
            ((a v).vertex_mem_of_inc heq') hy)

end GraphMinor.GM12
