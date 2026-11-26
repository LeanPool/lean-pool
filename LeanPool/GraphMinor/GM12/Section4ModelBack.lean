/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.Minor.Model
import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Recovering controlled branch subgraphs from a model

A minor model supplies connected branch subgraphs avoiding all joining
edges. Choose these subgraphs and use their vertex sets for the tangle
condition. This converts the composed models in XII (4.2), page 249,
back to the paper's definition of control.
-/

public section

namespace GraphMinor.GM12

open Set Graph Relation Hypergraph

private theorem skeleton_reachable {α β : Type*} {K : Graph α β}
    (hV : K.vertexSet.Finite) (hE : K.edgeSet.Finite) {x y : α}
    (h : Relation.ReflTransGen K.Adj x y) :
    (Hypergraph.ofGraph K hV hE).skeleton.Reachable x y := by
  induction h with
  | refl => exact .refl _
  | @tail p q _ hpq ih =>
    by_cases heq : p = q
    · subst q
      exact ih
    · obtain ⟨e, hl⟩ := hpq
      have hstep : (Hypergraph.ofGraph K hV hE).skeleton.Adj p q :=
        ⟨heq, e, hl.inc_left, hl.inc_right⟩
      exact ih.trans hstep.reachable

/-- A minor model with the paper's size and small-side conditions gives
a controlled minor. The chosen branches avoid all joining edges. -/
theorem controlsMinor_of_minorModel {α β γ δ : Type*} {G : Graph α β}
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) {L : Graph γ δ}
    {ηv : γ → Set α} {ηe : δ → β} (hm : IsMinorModel L G ηv ηe)
    {θ : ℕ} {T : Set (Hypergraph α β × Hypergraph α β)}
    (hcard : L.vertexSet.ncard ≤ θ)
    (hcontrol : ∀ A B, (A, B) ∈ T → separationOrder A B < L.vertexSet.ncard →
      ∀ v ∈ L.vertexSet, ¬ ηv v ⊆ A.vertexSet) :
    ControlsMinor (Hypergraph.ofGraph G hV hE) θ T L := by
  classical
  let B : (v : γ) → v ∈ L.vertexSet → Graph α β := fun v hv => (hm.connected v hv).choose
  have hB : ∀ v hv, B v hv ≤ G.deleteEdges (ηe '' L.edgeSet) ∧
      (B v hv).vertexSet = ηv v ∧ GraphConnected (B v hv) :=
    fun v hv => (hm.connected v hv).choose_spec
  have hBG : ∀ v hv, B v hv ≤ G := fun v hv => (hB v hv).1.trans Graph.deleteEdges_le
  let a : γ → Hypergraph α β := fun v => if hv : v ∈ L.vertexSet then
    Hypergraph.ofGraph (B v hv) (hV.subset (hBG v hv).vertexSet_mono)
      (hE.subset (hBG v hv).edgeSet_mono)
    else Hypergraph.ofGraph G hV hE
  have ha : ∀ v hv, a v = Hypergraph.ofGraph (B v hv)
      (hV.subset (hBG v hv).vertexSet_mono) (hE.subset (hBG v hv).edgeSet_mono) :=
    fun v hv => dite_eq_left hv
  have haV : ∀ v (_hv : v ∈ L.vertexSet), (a v).vertexSet = ηv v := by
    intro v hv
    rw [ha v hv]
    exact (hB v hv).2.1
  refine ⟨a, ηe, ?_, ?_, ?_, ?_, ?_, hcard, ?_⟩
  · intro v hv
    rw [ha v hv]
    refine ⟨⟨(hBG v hv).vertexSet_mono, (hBG v hv).edgeSet_mono, ?_⟩,
      (hB v hv).2.2.1, ?_⟩
    · intro e he
      ext x
      exact ((hBG v hv).inc_congr he).symm
    · intro x hx y hy
      exact skeleton_reachable _ _ ((hB v hv).2.2.2 x hx y hy)
  · intro u hu v hv huv
    rw [haV u hu, haV v hv]
    exact hm.vertex_disjoint u hu v hv huv
  · intro e u v hl _
    obtain ⟨x, hx, hxe⟩ := (hm.inc_iff u hl.left_mem e hl.edge_mem).mp hl.inc_left
    obtain ⟨y, hy, hye⟩ := (hm.inc_iff v hl.right_mem e hl.edge_mem).mp hl.inc_right
    rw [haV u hl.left_mem, haV v hl.right_mem]
    exact ⟨hm.edge_mem e hl.edge_mem, ⟨x, hx, hxe⟩, y, hy, hye⟩
  · intro e v hl
    have hv := hl.left_mem
    refine ⟨hm.edge_mem e hl.edge_mem, ?_, ?_⟩
    · rw [ha v hv]
      intro he
      exact ((hB v hv).1.edgeSet_mono he).2 (mem_image_of_mem ηe hl.edge_mem)
    · rw [haV v hv]
      exact (hm.isLoopAt_iff v hv e hl.edge_mem).mp hl
  · intro e he f hf hne hef
    exact hne (hm.edge_injOn he hf hef)
  · intro A B hmT ho v hv
    rw [haV v hv]
    exact hcontrol A B hmT ho v hv

/-- Disjoint nonempty branches give an injection from the target vertices
into the host vertices, so taking a minor cannot increase their number. -/
theorem minorModel_vertex_ncard_le {α β γ δ : Type*} {H : Graph γ δ} {G : Graph α β}
    {ηv : γ → Set α} {ηe : δ → β} (hm : IsMinorModel H G ηv ηe)
    (hV : G.vertexSet.Finite) : H.vertexSet.ncard ≤ G.vertexSet.ncard := by
  classical
  let : Finite G.vertexSet := hV.to_subtype
  let f : H.vertexSet → G.vertexSet := fun v =>
    ⟨(hm.vertex_nonempty v.val v.property).choose,
      hm.vertex_subset v.val v.property (hm.vertex_nonempty v.val v.property).choose_spec⟩
  have hinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    by_contra hne
    exact Set.disjoint_left.mp (hm.vertex_disjoint u.val u.property v.val v.property hne)
      (hm.vertex_nonempty u.val u.property).choose_spec
      (show (f u).val ∈ ηv v.val from by
        rw [congrArg Subtype.val huv]
        exact (hm.vertex_nonempty v.val v.property).choose_spec)
  simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hinj

end GraphMinor.GM12
