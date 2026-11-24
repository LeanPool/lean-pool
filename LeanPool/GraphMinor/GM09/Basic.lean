/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM11.Walks
import Mathlib.Combinatorics.Graph.Lattice

/-!
# Basic lemmas for Graph Minors IX

This file develops the basic infrastructure for Graph Minors IX:
- Subgraph operations (`subgraphUnion`, `subgraphInter`, `subgraphSUnion`, `deleteVertices`) on
  `Graph α β`, their vertex sets, edge sets, and monotonicity.
- Graph walks and paths (`IsGraphPathWithEnds`, `IsGraphPath`, `pathEnds`, `pathInternalVerts`),
  subpaths of paths (`IsGraphPathWithEnds.exists_subpath`), concatenation of paths, and extraction
  of a path from a walk (`GraphWalk.exists_isGraphPathWithEnds`).
- Connected subgraphs and connected components (`IsGraphConnected`, `IsGraphComponent`,
  `graphComponents`) and `Catches`.
-/

public section

namespace GraphMinor.GM09

open Set Graph GraphMinor.Surface GraphMinor.GM06

universe u v

variable {α : Type u} {β : Type v}

/-! ## Subgraph operations (`subgraphUnion`, `subgraphInter`, `subgraphSUnion`, `deleteVertices`) -/

@[simp]
theorem vertexSet_subgraphUnion (G G₁ G₂ : Graph α β) :
    V(subgraphUnion G G₁ G₂) = V(G₁) ∪ V(G₂) := rfl

theorem edgeSet_subgraphUnion_subset (G G₁ G₂ : Graph α β) :
    E(subgraphUnion G G₁ G₂) ⊆ E(G₁) ∪ E(G₂) :=
  inter_subset_right

theorem subgraphUnion_le {G G₁ G₂ : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    subgraphUnion G G₁ G₂ ≤ G :=
  restrict_le.trans (G.induce_le (union_subset h₁.vertexSet_mono h₂.vertexSet_mono))

@[simp]
theorem edgeSet_subgraphUnion {G G₁ G₂ : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    E(subgraphUnion G G₁ G₂) = E(G₁) ∪ E(G₂) := by
  unfold subgraphUnion
  rw [edgeSet_restrict, inter_eq_right]
  rintro e (he | he)
  · obtain ⟨x, y, hxy⟩ := G₁.exists_isLink_of_mem_edgeSet he
    exact ⟨x, y, hxy.mono h₁, Or.inl hxy.left_mem, Or.inl hxy.right_mem⟩
  · obtain ⟨x, y, hxy⟩ := G₂.exists_isLink_of_mem_edgeSet he
    exact ⟨x, y, hxy.mono h₂, Or.inr hxy.left_mem, Or.inr hxy.right_mem⟩

theorem subgraphUnion_isLink {G G₁ G₂ : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) {e : β} {x y : α} :
    (subgraphUnion G G₁ G₂).IsLink e x y ↔ G₁.IsLink e x y ∨ G₂.IsLink e x y := by
  rw [(subgraphUnion_le h₁ h₂).isLink_iff', edgeSet_subgraphUnion h₁ h₂]
  constructor
  · rintro ⟨hG, he | he⟩
    · exact Or.inl ((h₁.isLink_iff he).mpr hG)
    · exact Or.inr ((h₂.isLink_iff he).mpr hG)
  · rintro (h | h)
    · exact ⟨h.mono h₁, Or.inl h.edge_mem⟩
    · exact ⟨h.mono h₂, Or.inr h.edge_mem⟩

theorem le_subgraphUnion_left {G G₁ G₂ : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    G₁ ≤ subgraphUnion G G₁ G₂ := by
  refine ⟨subset_union_left, fun e x y h => ?_⟩
  rw [subgraphUnion_isLink h₁ h₂]
  exact Or.inl h

theorem le_subgraphUnion_right {G G₁ G₂ : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    G₂ ≤ subgraphUnion G G₁ G₂ := by
  refine ⟨subset_union_right, fun e x y h => ?_⟩
  rw [subgraphUnion_isLink h₁ h₂]
  exact Or.inr h

theorem subgraphUnion_le_iff {G G₁ G₂ H : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) (hH : H ≤ G) :
    subgraphUnion G G₁ G₂ ≤ H ↔ G₁ ≤ H ∧ G₂ ≤ H := by
  refine ⟨fun h => ⟨(le_subgraphUnion_left h₁ h₂).trans h, (le_subgraphUnion_right h₁ h₂).trans h⟩,
    fun ⟨h₁H, h₂H⟩ => ?_⟩
  rw [(Compatible.of_le_le (subgraphUnion_le h₁ h₂) hH).le_iff, vertexSet_subgraphUnion,
    edgeSet_subgraphUnion h₁ h₂]
  exact ⟨union_subset h₁H.vertexSet_mono h₂H.vertexSet_mono,
    union_subset h₁H.edgeSet_mono h₂H.edgeSet_mono⟩

theorem subgraphUnion_comm {G G₁ G₂ : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    subgraphUnion G G₁ G₂ = subgraphUnion G G₂ G₁ := by
  refine (Compatible.of_le_le (subgraphUnion_le h₁ h₂) (subgraphUnion_le h₂ h₁)).ext ?_ ?_
  · simp [union_comm]
  · simp [edgeSet_subgraphUnion h₁ h₂, edgeSet_subgraphUnion h₂ h₁, union_comm]

@[simp]
theorem vertexSet_subgraphInter (G G₁ G₂ : Graph α β) :
    V(subgraphInter G G₁ G₂) = V(G₁) ∩ V(G₂) := rfl

theorem subgraphInter_le {G G₁ G₂ : Graph α β} (h₁ : G₁ ≤ G) :
    subgraphInter G G₁ G₂ ≤ G :=
  restrict_le.trans (G.induce_le (inter_subset_left.trans h₁.vertexSet_mono))

@[simp]
theorem edgeSet_subgraphInter {G G₁ G₂ : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    E(subgraphInter G G₁ G₂) = E(G₁) ∩ E(G₂) := by
  unfold subgraphInter
  rw [edgeSet_restrict, inter_eq_right]
  rintro e ⟨he₁, he₂⟩
  obtain ⟨x, y, hxy₁⟩ := G₁.exists_isLink_of_mem_edgeSet he₁
  have hxyG : G.IsLink e x y := hxy₁.mono h₁
  have hxy₂ : G₂.IsLink e x y := (h₂.isLink_iff he₂).mpr hxyG
  exact ⟨x, y, hxyG, ⟨hxy₁.left_mem, hxy₂.left_mem⟩, ⟨hxy₁.right_mem, hxy₂.right_mem⟩⟩

theorem subgraphInter_isLink {G G₁ G₂ : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) {e : β} {x y : α} :
    (subgraphInter G G₁ G₂).IsLink e x y ↔ G₁.IsLink e x y ∧ G₂.IsLink e x y := by
  rw [(subgraphInter_le h₁).isLink_iff', edgeSet_subgraphInter h₁ h₂]
  constructor
  · rintro ⟨hG, he₁, he₂⟩
    exact ⟨(h₁.isLink_iff he₁).mpr hG, (h₂.isLink_iff he₂).mpr hG⟩
  · rintro ⟨h₁e, h₂e⟩
    exact ⟨h₁e.mono h₁, h₁e.edge_mem, h₂e.edge_mem⟩

theorem subgraphInter_le_left {G G₁ G₂ : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    subgraphInter G G₁ G₂ ≤ G₁ := by
  refine ⟨inter_subset_left, fun e x y h => ?_⟩
  exact ((subgraphInter_isLink h₁ h₂).mp h).1

theorem subgraphInter_le_right {G G₁ G₂ : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    subgraphInter G G₁ G₂ ≤ G₂ := by
  refine ⟨inter_subset_right, fun e x y h => ?_⟩
  exact ((subgraphInter_isLink h₁ h₂).mp h).2

theorem le_subgraphInter {G G₁ G₂ H : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G)
    (hH₁ : H ≤ G₁) (hH₂ : H ≤ G₂) : H ≤ subgraphInter G G₁ G₂ := by
  refine ⟨subset_inter hH₁.vertexSet_mono hH₂.vertexSet_mono, fun e x y h => ?_⟩
  rw [subgraphInter_isLink h₁ h₂]
  exact ⟨h.mono hH₁, h.mono hH₂⟩

theorem subgraphInter_comm {G G₁ G₂ : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    subgraphInter G G₁ G₂ = subgraphInter G G₂ G₁ := by
  refine (Compatible.of_le_le (subgraphInter_le h₁) (subgraphInter_le h₂)).ext ?_ ?_
  · simp [inter_comm]
  · simp [edgeSet_subgraphInter h₁ h₂, edgeSet_subgraphInter h₂ h₁, inter_comm]

@[simp]
theorem vertexSet_subgraphSUnion (G : Graph α β) (P_set : Set (Graph α β)) :
    V(subgraphSUnion G P_set) = ⋃ P ∈ P_set, V(P) := rfl

theorem subgraphSUnion_le {G : Graph α β} {P_set : Set (Graph α β)} (hP : ∀ P ∈ P_set, P ≤ G) :
    subgraphSUnion G P_set ≤ G :=
  restrict_le.trans (G.induce_le (iUnion₂_subset fun P hP_mem => (hP P hP_mem).vertexSet_mono))

@[simp]
theorem edgeSet_subgraphSUnion {G : Graph α β} {P_set : Set (Graph α β)}
    (hP : ∀ P ∈ P_set, P ≤ G) :
    E(subgraphSUnion G P_set) = ⋃ P ∈ P_set, E(P) := by
  unfold subgraphSUnion
  rw [edgeSet_restrict, inter_eq_right]
  intro e he
  obtain ⟨P, hP_mem, heP⟩ := mem_iUnion₂.mp he
  obtain ⟨x, y, hxy⟩ := P.exists_isLink_of_mem_edgeSet heP
  exact ⟨x, y, hxy.mono (hP P hP_mem), mem_iUnion₂.mpr ⟨P, hP_mem, hxy.left_mem⟩,
    mem_iUnion₂.mpr ⟨P, hP_mem, hxy.right_mem⟩⟩

theorem le_subgraphSUnion {G P : Graph α β} {P_set : Set (Graph α β)}
    (hP_set : ∀ Q ∈ P_set, Q ≤ G) (hP : P ∈ P_set) :
    P ≤ subgraphSUnion G P_set := by
  have hsub := subgraphSUnion_le hP_set
  rw [(Compatible.of_le_le (hP_set P hP) hsub).le_iff, vertexSet_subgraphSUnion,
    edgeSet_subgraphSUnion hP_set]
  exact ⟨subset_iUnion₂ (s := fun Q _ => V(Q)) P hP, subset_iUnion₂ (s := fun Q _ => E(Q)) P hP⟩

theorem subgraphSUnion_mono {G : Graph α β} {P_set Q_set : Set (Graph α β)}
    (hQ : ∀ Q ∈ Q_set, Q ≤ G) (hsub : P_set ⊆ Q_set) :
    subgraphSUnion G P_set ≤ subgraphSUnion G Q_set := by
  have hP : ∀ P ∈ P_set, P ≤ G := fun P hP => hQ P (hsub hP)
  rw [(Compatible.of_le_le (subgraphSUnion_le hP) (subgraphSUnion_le hQ)).le_iff,
    vertexSet_subgraphSUnion, vertexSet_subgraphSUnion,
    edgeSet_subgraphSUnion hP, edgeSet_subgraphSUnion hQ]
  exact ⟨biUnion_subset_biUnion_left hsub, biUnion_subset_biUnion_left hsub⟩

@[simp]
theorem vertexSet_deleteVertices (G : Graph α β) (X : Set α) :
    V(deleteVertices G X) = V(G) \ X := rfl

@[simp]
theorem deleteVertices_le (G : Graph α β) (X : Set α) :
    deleteVertices G X ≤ G := G.induce_le sdiff_subset

@[simp]
theorem deleteVertices_isLink (G : Graph α β) (X : Set α) {e : β} {x y : α} :
    (deleteVertices G X).IsLink e x y ↔ G.IsLink e x y ∧ x ∉ X ∧ y ∉ X := by
  simp only [deleteVertices, induce_isLink, mem_sdiff, and_congr_right_iff]
  exact fun h => by simp [h.left_mem, h.right_mem]

/-! ##Separations of graphs -/

theorem IsGraphSeparation.symm {G G₁ G₂ : Graph α β} (h : IsGraphSeparation G G₁ G₂) :
    IsGraphSeparation G G₂ G₁ :=
  ⟨h.2.1, h.1, union_comm V(G₂) V(G₁) ▸ h.2.2.1, union_comm E(G₂) E(G₁) ▸ h.2.2.2.1,
    h.2.2.2.2.symm⟩

theorem IsGraphSeparation.subgraphUnion_eq {G G₁ G₂ : Graph α β} (h : IsGraphSeparation G G₁ G₂) :
    subgraphUnion G G₁ G₂ = G := by
  refine (Compatible.of_le_le (subgraphUnion_le h.1 h.2.1) le_rfl).ext ?_ ?_
  · rw [vertexSet_subgraphUnion, h.2.2.1]
  · rw [edgeSet_subgraphUnion h.1 h.2.1, h.2.2.2.1]

theorem IsGraphSeparation.edgeSet_subgraphInter {G G₁ G₂ : Graph α β}
    (h : IsGraphSeparation G G₁ G₂) : E(subgraphInter G G₁ G₂) = ∅ := by
  rw [GM09.edgeSet_subgraphInter h.1 h.2.1, disjoint_iff_inter_eq_empty.mp h.2.2.2.2]

/-! ## Walks and paths in `Graph α β` -/

/-- The subgraph of `G` formed by the vertices and edges of a walk `W` in `G`. -/
def walkSubgraph {G : Graph α β} {a b : α} (W : GraphWalk G a b) : Graph α β :=
  (G.induce {x | x ∈ W.support}).restrict {e | e ∈ W.edges}

theorem walkSubgraph_eq {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    walkSubgraph W = (G.induce {x | x ∈ W.support}).restrict {e | e ∈ W.edges} := by
  unfold walkSubgraph
  rfl

theorem walkSubgraph_le {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    walkSubgraph W ≤ G :=
  restrict_le.trans (G.induce_le fun _ hx => W.mem_vertexSet_of_mem_support hx)

@[simp]
theorem vertexSet_walkSubgraph {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    V(walkSubgraph W) = {x | x ∈ W.support} := by rfl

theorem walk_edges_subset_edgeSet {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    ∀ e ∈ W.edges, e ∈ E(G) := by
  induction W with
  | nil _ => simp
  | cons h _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h.edge_mem
    · exact ih e he

theorem walk_isLink_mem_support {G : Graph α β} {a b : α} (W : GraphWalk G a b)
    {e : β} (he : e ∈ W.edges) {x y : α} (hxy : G.IsLink e x y) :
    x ∈ W.support ∧ y ∈ W.support :=
  ⟨W.left_mem_support_of_mem_edges he hxy, W.left_mem_support_of_mem_edges he hxy.symm⟩

@[simp]
theorem edgeSet_walkSubgraph {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    E(walkSubgraph W) = {e | e ∈ W.edges} := by
  unfold walkSubgraph
  rw [edgeSet_restrict, inter_eq_right]
  intro e he
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet (walk_edges_subset_edgeSet W e he)
  have hm := walk_isLink_mem_support W he hxy
  exact ⟨x, y, hxy, hm.1, hm.2⟩

theorem walkSubgraph_isLink {G : Graph α β} {a b : α} (W : GraphWalk G a b)
    {e : β} {x y : α} :
    (walkSubgraph W).IsLink e x y ↔ e ∈ W.edges ∧ G.IsLink e x y := by
  rw [(walkSubgraph_le W).isLink_iff', edgeSet_walkSubgraph, mem_ofPred_eq, and_comm]

theorem isSimple_of_append {G : Graph α β} {a x b : α} {W₁ : GraphWalk G a x}
    {W₂ : GraphWalk G x b} (h : (W₁.append W₂).IsSimple) :
    W₁.IsSimple ∧ W₂.IsSimple := by
  have hs : (W₁.support ++ W₂.support.tail).Nodup := by
    have h' : (W₁.append W₂).support.Nodup := h
    rwa [GraphWalk.support_append] at h'
  have hd := List.nodup_append.mp hs
  refine ⟨hd.1, ?_⟩
  unfold GraphWalk.IsSimple
  rw [W₂.support_eq_cons]
  exact List.nodup_cons.mpr ⟨fun hx => hd.2.2 x W₁.end_mem_support x hx rfl, hd.2.1⟩

/-- Every walk `W` in `G` transfers to a walk with the same support and edges in `walkSubgraph W`.
-/
theorem exists_walk_walkSubgraph {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    ∃ W' : GraphWalk (walkSubgraph W) a b,
      W'.support = W.support ∧ W'.edges = W.edges :=
  W.exists_transfer
    (fun _ _ _ he hl => (walkSubgraph_isLink W).mpr ⟨he, hl⟩)
    (fun _ hx => hx)

/-- If `W` is a simple walk in `G` from `a` to `b`, then `walkSubgraph W` is a path in `G` with
ends `a` and `b`. -/
theorem isGraphPathWithEnds_walkSubgraph {G : Graph α β} {a b : α} {W : GraphWalk G a b}
    (hW : W.IsSimple) : IsGraphPathWithEnds G (walkSubgraph W) a b := by
  obtain ⟨W', hs, he⟩ := exists_walk_walkSubgraph W
  refine ⟨walkSubgraph_le W, W', ?_, ?_, ?_⟩
  · unfold GraphWalk.IsSimple; rw [hs]; exact hW
  · rw [vertexSet_walkSubgraph, hs]
  · rw [edgeSet_walkSubgraph, he]

/-- Every walk in `G` from `a` to `b` can be shortened to a simple walk whose support and edges
are subsets of the original walk's support and edges. -/
theorem exists_isSimple_subwalk {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    ∃ W' : GraphWalk G a b, W'.IsSimple ∧
      (∀ x ∈ W'.support, x ∈ W.support) ∧ (∀ e ∈ W'.edges, e ∈ W.edges) := by
  induction W with
  | @nil u h =>
    exact ⟨.nil h, List.nodup_singleton u, fun _ hx => hx, fun _ he => he⟩
  | @cons u v _ e h r ih =>
    obtain ⟨r', hr', hsupp, hedges⟩ := ih
    by_cases hu : u ∈ r'.support
    · obtain ⟨W₁, W₂, hsplit⟩ := r'.exists_append_of_mem hu
      have hW₂_simple : W₂.IsSimple := (isSimple_of_append (hsplit ▸ hr')).2
      refine ⟨W₂, hW₂_simple, fun x hx => ?_, fun f hf => ?_⟩
      · apply List.mem_cons_of_mem u (hsupp x ?_)
        rw [hsplit]
        exact (GraphWalk.mem_support_append W₁ W₂).mpr (Or.inr hx)
      · apply List.mem_cons_of_mem e (hedges f ?_)
        rw [hsplit, GraphWalk.edges_append]
        exact List.mem_append_right _ hf
    · refine ⟨.cons h r', List.nodup_cons.mpr ⟨hu, hr'⟩, fun x hx => ?_, fun f hf => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsupp x hx)
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hedges f hf)

/-- Every walk `W` in `G` from `a` to `b` contains a path `P ≤ G` with ends `a` and `b` whose
vertices and edges lie in `W`. -/
theorem exists_isGraphPathWithEnds_of_walk {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    ∃ P : Graph α β, IsGraphPathWithEnds G P a b ∧
      V(P) ⊆ {x | x ∈ W.support} ∧ E(P) ⊆ {e | e ∈ W.edges} := by
  obtain ⟨W', hW', hsupp, hedges⟩ := exists_isSimple_subwalk W
  refine ⟨walkSubgraph W', isGraphPathWithEnds_walkSubgraph hW', ?_, ?_⟩
  · rw [vertexSet_walkSubgraph]
    exact hsupp
  · rw [edgeSet_walkSubgraph]
    exact hedges

theorem IsGraphPathWithEnds.le {G P : Graph α β} {a b : α} (h : IsGraphPathWithEnds G P a b) :
    P ≤ G := h.1

theorem IsGraphPathWithEnds.left_mem {G P : Graph α β} {a b : α}
    (h : IsGraphPathWithEnds G P a b) : a ∈ V(P) := by
  obtain ⟨_, W, _, hV, _⟩ := h
  rw [hV]
  exact W.start_mem_support

theorem IsGraphPathWithEnds.right_mem {G P : Graph α β} {a b : α}
    (h : IsGraphPathWithEnds G P a b) : b ∈ V(P) := by
  obtain ⟨_, W, _, hV, _⟩ := h
  rw [hV]
  exact W.end_mem_support

theorem IsGraphPathWithEnds.symm {G P : Graph α β} {a b : α}
    (h : IsGraphPathWithEnds G P a b) : IsGraphPathWithEnds G P b a := by
  obtain ⟨hPG, W, hW, hV, hE⟩ := h
  refine ⟨hPG, W.reverse, hW.reverse, ?_, ?_⟩
  · rw [hV]
    ext x
    simp [GraphWalk.support_reverse]
  · rw [hE]
    ext e
    simp [GraphWalk.edges_reverse]

theorem IsGraphPathWithEnds.mono {G H P : Graph α β} {a b : α}
    (h : IsGraphPathWithEnds H P a b) (hHG : H ≤ G) : IsGraphPathWithEnds G P a b :=
  ⟨h.1.trans hHG, h.2⟩

theorem IsGraphPathWithEnds.of_le {G H P : Graph α β} {a b : α}
    (h : IsGraphPathWithEnds G P a b) (hPH : P ≤ H) : IsGraphPathWithEnds H P a b :=
  ⟨hPH, h.2⟩

/-- If `P` is a path in `G` with ends `a, b` and `x ∈ V(P)`, then `P` splits into two subpaths
`P₁` (from `a` to `x`) and `P₂` (from `x` to `b`) with `P₁ ∪ P₂ = P`, `V(P₁) ∩ V(P₂) = {x}`,
and `E(P₁) ∩ E(P₂) = ∅`. -/
theorem IsGraphPathWithEnds.exists_split_at {G P : Graph α β} {a b x : α}
    (hP : IsGraphPathWithEnds G P a b) (hx : x ∈ V(P)) :
    ∃ P₁ P₂ : Graph α β,
      P₁ ≤ P ∧ P₂ ≤ P ∧
      IsGraphPathWithEnds P P₁ a x ∧ IsGraphPathWithEnds P P₂ x b ∧
      subgraphUnion P P₁ P₂ = P ∧
      V(P₁) ∩ V(P₂) = {x} ∧ Disjoint E(P₁) E(P₂) := by
  obtain ⟨_, W, hW, hVP, hEP⟩ := hP
  have hxW : x ∈ W.support := by rwa [hVP] at hx
  obtain ⟨W₁, W₂, rfl⟩ := W.exists_append_of_mem hxW
  have hsp := isSimple_of_append hW
  let P₁ := walkSubgraph W₁
  let P₂ := walkSubgraph W₂
  have hP₁P : P₁ ≤ P := walkSubgraph_le W₁
  have hP₂P : P₂ ≤ P := walkSubgraph_le W₂
  have hP₁ : IsGraphPathWithEnds P P₁ a x := isGraphPathWithEnds_walkSubgraph hsp.1
  have hP₂ : IsGraphPathWithEnds P P₂ x b := isGraphPathWithEnds_walkSubgraph hsp.2
  have hnd_V : (W₁.support ++ W₂.support.tail).Nodup := by
    have h' : (W₁.append W₂).support.Nodup := hW
    rwa [GraphWalk.support_append] at h'
  have hd_V := List.nodup_append.mp hnd_V
  have hnd_E : (W₁.edges ++ W₂.edges).Nodup := by
    have h' : (W₁.append W₂).edges.Nodup := hW.edges_nodup
    rwa [GraphWalk.edges_append] at h'
  have hd_E := List.nodup_append.mp hnd_E
  refine ⟨P₁, P₂, hP₁P, hP₂P, hP₁, hP₂, ?_, ?_, ?_⟩
  · refine (Compatible.of_le_le (subgraphUnion_le hP₁P hP₂P) le_rfl).ext ?_ ?_
    · rw [vertexSet_subgraphUnion, vertexSet_walkSubgraph, vertexSet_walkSubgraph, hVP]
      ext z
      simp [GraphWalk.mem_support_append]
    · rw [edgeSet_subgraphUnion hP₁P hP₂P, edgeSet_walkSubgraph, edgeSet_walkSubgraph, hEP]
      ext e
      simp [GraphWalk.edges_append]
  · rw [vertexSet_walkSubgraph, vertexSet_walkSubgraph]
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hz₁, hz₂⟩
      rw [W₂.support_eq_cons] at hz₂
      rcases List.mem_cons.mp hz₂ with rfl | hz₂
      · rfl
      · exact False.elim (hd_V.2.2 z hz₁ z hz₂ rfl)
    · rintro rfl
      exact ⟨W₁.end_mem_support, W₂.start_mem_support⟩
  · rw [edgeSet_walkSubgraph, edgeSet_walkSubgraph]
    exact disjoint_left.mpr fun e he₁ he₂ => hd_E.2.2 e he₁ e he₂ rfl

/-- Between any two vertices `u, v ∈ V(P)` of a path `P` in `G`, there is a subpath `Q ≤ P` with
ends `u` and `v`. -/
theorem IsGraphPathWithEnds.exists_subpath {G P : Graph α β} {a b u v : α}
    (hP : IsGraphPathWithEnds G P a b) (hu : u ∈ V(P)) (hv : v ∈ V(P)) :
    ∃ Q : Graph α β, Q ≤ P ∧ IsGraphPathWithEnds P Q u v ∧ IsGraphPathWithEnds G Q u v := by
  obtain ⟨P₁, P₂, hP₁P, hP₂P, hP₁, hP₂, hunion, _, _⟩ := hP.exists_split_at hu
  have hv_union : v ∈ V(P₁) ∪ V(P₂) := by
    rw [← vertexSet_subgraphUnion P P₁ P₂, hunion]
    exact hv
  rcases hv_union with hv₁ | hv₂
  · obtain ⟨Q₁, Q₂, _, hQ₂P₁, _, hQ₂, _, _, _⟩ := hP₁.exists_split_at hv₁
    have hQ₂P : Q₂ ≤ P := hQ₂P₁.trans hP₁P
    have hQ₂' : IsGraphPathWithEnds P Q₂ u v := (hQ₂.mono hP₁P).symm
    exact ⟨Q₂, hQ₂P, hQ₂', hQ₂'.mono hP.le⟩
  · obtain ⟨Q₁, Q₂, hQ₁P₂, _, hQ₁, _, _, _, _⟩ := hP₂.exists_split_at hv₂
    have hQ₁P : Q₁ ≤ P := hQ₁P₂.trans hP₂P
    have hQ₁' : IsGraphPathWithEnds P Q₁ u v := hQ₁.mono hP₂P
    exact ⟨Q₁, hQ₁P, hQ₁', hQ₁'.mono hP.le⟩

/-- If `P₁` is a path in `G` from `a` to `b` and `P₂` is a path in `G` from `b` to `c` with
`V(P₁) ∩ V(P₂) = {b}`, then `P₁ ∪ P₂` is a path in `G` from `a` to `c`. -/
theorem IsGraphPathWithEnds.subgraphUnion {G P₁ P₂ : Graph α β} {a b c : α}
    (h₁ : IsGraphPathWithEnds G P₁ a b) (h₂ : IsGraphPathWithEnds G P₂ b c)
    (hV : V(P₁) ∩ V(P₂) = {b}) :
    IsGraphPathWithEnds G (subgraphUnion G P₁ P₂) a c := by
  obtain ⟨hP₁G, W₁, hW₁, hV₁, hE₁⟩ := h₁
  obtain ⟨hP₂G, W₂, hW₂, hV₂, hE₂⟩ := h₂
  have hl₁ := le_subgraphUnion_left hP₁G hP₂G
  have hl₂ := le_subgraphUnion_right hP₁G hP₂G
  obtain ⟨W₁', hs₁, he₁⟩ := W₁.exists_transfer (fun _ _ _ _ hl => hl.mono hl₁)
    (fun _ hx => hl₁.vertexSet_mono (W₁.mem_vertexSet_of_mem_support hx))
  obtain ⟨W₂', hs₂, he₂⟩ := W₂.exists_transfer (fun _ _ _ _ hl => hl.mono hl₂)
    (fun _ hx => hl₂.vertexSet_mono (W₂.mem_vertexSet_of_mem_support hx))
  refine ⟨subgraphUnion_le hP₁G hP₂G, W₁'.append W₂', ?_, ?_, ?_⟩
  · unfold GraphWalk.IsSimple
    rw [GraphWalk.support_append, hs₁, hs₂]
    refine List.nodup_append.mpr ⟨hW₁, List.Nodup.tail hW₂, fun x hx₁ y hy₂ hxy => ?_⟩
    subst hxy
    have hxP₁ : x ∈ V(P₁) := by rw [hV₁]; exact hx₁
    have hxW₂ : x ∈ W₂.support := by
      rw [W₂.support_eq_cons]
      exact List.mem_cons_of_mem _ hy₂
    have hxP₂ : x ∈ V(P₂) := by rw [hV₂]; exact hxW₂
    have hxb : x = b := by
      have : x ∈ V(P₁) ∩ V(P₂) := ⟨hxP₁, hxP₂⟩
      rwa [hV, mem_singleton_iff] at this
    subst hxb
    have hnd₂ : W₂.support.Nodup := hW₂
    rw [W₂.support_eq_cons] at hnd₂
    exact (List.nodup_cons.mp hnd₂).1 hy₂
  · rw [vertexSet_subgraphUnion, hV₁, hV₂]
    ext x
    simp [GraphWalk.mem_support_append, hs₁, hs₂]
  · rw [edgeSet_subgraphUnion hP₁G hP₂G, hE₁, hE₂]
    ext e
    simp [GraphWalk.edges_append, he₁, he₂]

/-! ## Connected subgraphs, components, and `Catches` -/

theorem exists_walk_up_of_le {G H : Graph α β} (h : H ≤ G) {u v : α} (W : GraphWalk H u v) :
    ∃ W' : GraphWalk G u v, W'.support = W.support ∧ W'.edges = W.edges :=
  W.exists_transfer (fun _ _ _ _ hl => hl.mono h)
    (fun _ hx => h.vertexSet_mono (W.mem_vertexSet_of_mem_support hx))

theorem exists_walk_down_of_le {G H : Graph α β} (h : H ≤ G) {u v : α} (W : GraphWalk G u v)
    (hV : ∀ x ∈ W.support, x ∈ V(H)) (hE : ∀ e ∈ W.edges, e ∈ E(H)) :
    ∃ W' : GraphWalk H u v, W'.support = W.support ∧ W'.edges = W.edges :=
  W.exists_transfer (fun _ _ _ he hl => (h.isLink_iff (hE _ he)).mpr hl) hV

theorem isGraphConnected_subgraphUnion {G H₁ H₂ : Graph α β} (h₁G : H₁ ≤ G) (h₂G : H₂ ≤ G)
    (h₁ : IsGraphConnected H₁) (h₂ : IsGraphConnected H₂) (hinter : (V(H₁) ∩ V(H₂)).Nonempty) :
    IsGraphConnected (subgraphUnion G H₁ H₂) := by
  obtain ⟨z, hz₁, hz₂⟩ := hinter
  have hl₁ := le_subgraphUnion_left h₁G h₂G
  have hl₂ := le_subgraphUnion_right h₁G h₂G
  refine ⟨⟨z, Or.inl hz₁⟩, fun u hu v hv => ?_⟩
  have hu_walk : Nonempty (GraphWalk (subgraphUnion G H₁ H₂) u z) := by
    rcases hu with hu₁ | hu₂
    · obtain ⟨W⟩ := h₁.2 u hu₁ z hz₁
      obtain ⟨W', _, _⟩ := exists_walk_up_of_le hl₁ W
      exact ⟨W'⟩
    · obtain ⟨W⟩ := h₂.2 u hu₂ z hz₂
      obtain ⟨W', _, _⟩ := exists_walk_up_of_le hl₂ W
      exact ⟨W'⟩
  have hv_walk : Nonempty (GraphWalk (subgraphUnion G H₁ H₂) z v) := by
    rcases hv with hv₁ | hv₂
    · obtain ⟨W⟩ := h₁.2 z hz₁ v hv₁
      obtain ⟨W', _, _⟩ := exists_walk_up_of_le hl₁ W
      exact ⟨W'⟩
    · obtain ⟨W⟩ := h₂.2 z hz₂ v hv₂
      obtain ⟨W', _, _⟩ := exists_walk_up_of_le hl₂ W
      exact ⟨W'⟩
  obtain ⟨W₁⟩ := hu_walk
  obtain ⟨W₂⟩ := hv_walk
  exact ⟨W₁.append W₂⟩

/-- The induced subgraph of `G` on the vertices reachable from `v ∈ V(G)`. -/
def reachableComponent (G : Graph α β) (v : α) : Graph α β :=
  G.induce {u ∈ V(G) | Nonempty (GraphWalk G v u)}

theorem reachableComponent_le (G : Graph α β) (v : α) :
    reachableComponent G v ≤ G :=
  G.induce_le fun _ hu => hu.1

@[simp]
theorem vertexSet_reachableComponent (G : Graph α β) (v : α) :
    V(reachableComponent G v) = {u ∈ V(G) | Nonempty (GraphWalk G v u)} := by rfl

theorem self_mem_reachableComponent {G : Graph α β} {v : α} (hv : v ∈ V(G)) :
    v ∈ V(reachableComponent G v) :=
  ⟨hv, ⟨.nil hv⟩⟩

theorem walk_support_subset_reachableComponent {G : Graph α β} {v a b : α}
    (ha : a ∈ V(reachableComponent G v)) (W : GraphWalk G a b) :
    ∀ x ∈ W.support, x ∈ V(reachableComponent G v) := by
  induction W with
  | nil _ =>
    intro x hx
    simp only [GraphWalk.support_nil, List.mem_singleton] at hx
    exact hx ▸ ha
  | @cons u w _ e h r ih =>
    have hw : w ∈ V(reachableComponent G v) := by
      obtain ⟨_, ⟨W₀⟩⟩ := ha
      exact ⟨h.right_mem, ⟨W₀.append (.cons h (.nil h.right_mem))⟩⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact ih hw x hx

theorem walk_edges_subset_reachableComponent {G : Graph α β} {v a b : α}
    (ha : a ∈ V(reachableComponent G v)) (W : GraphWalk G a b) :
    ∀ e ∈ W.edges, e ∈ E(reachableComponent G v) := by
  intro e he
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet (walk_edges_subset_edgeSet W e he)
  have hm := walk_isLink_mem_support W he hxy
  exact ⟨x, y, hxy, walk_support_subset_reachableComponent ha W x hm.1,
    walk_support_subset_reachableComponent ha W y hm.2⟩

theorem isGraphConnected_reachableComponent {G : Graph α β} {v : α} (hv : v ∈ V(G)) :
    IsGraphConnected (reachableComponent G v) := by
  refine ⟨⟨v, self_mem_reachableComponent hv⟩, fun x hx y hy => ?_⟩
  obtain ⟨hxG, ⟨Wx⟩⟩ := hx
  obtain ⟨hyG, ⟨Wy⟩⟩ := hy
  let W := Wx.reverse.append Wy
  obtain ⟨W', _, _⟩ := exists_walk_down_of_le (reachableComponent_le G v) W
    (walk_support_subset_reachableComponent ⟨hxG, ⟨Wx⟩⟩ W)
    (walk_edges_subset_reachableComponent ⟨hxG, ⟨Wx⟩⟩ W)
  exact ⟨W'⟩

theorem isGraphComponent_reachableComponent {G : Graph α β} {v : α} (hv : v ∈ V(G)) :
    IsGraphComponent (reachableComponent G v) G := by
  refine ⟨reachableComponent_le G v, isGraphConnected_reachableComponent hv,
    fun C' hle hC'G hconn => le_antisymm ?_ hle⟩
  have hvC' : v ∈ V(C') := hle.vertexSet_mono (self_mem_reachableComponent hv)
  have hsubV : V(C') ⊆ V(reachableComponent G v) := by
    intro u hu
    obtain ⟨W⟩ := hconn.2 v hvC' u hu
    obtain ⟨W', _, _⟩ := exists_walk_up_of_le hC'G W
    exact ⟨hC'G.vertexSet_mono hu, ⟨W'⟩⟩
  rw [(Compatible.of_le_le hC'G (reachableComponent_le G v)).le_iff]
  refine ⟨hsubV, fun e he => ?_⟩
  obtain ⟨x, y, hxy⟩ := C'.exists_isLink_of_mem_edgeSet he
  exact ⟨x, y, hxy.mono hC'G, hsubV hxy.left_mem, hsubV hxy.right_mem⟩

theorem exists_graphComponent_of_mem {G : Graph α β} {v : α} (hv : v ∈ V(G)) :
    ∃ C ∈ graphComponents G, v ∈ V(C) :=
  ⟨reachableComponent G v, isGraphComponent_reachableComponent hv, self_mem_reachableComponent hv⟩

theorem isGraphComponent_eq_of_mem_inter {G C₁ C₂ : Graph α β}
    (h₁ : IsGraphComponent C₁ G) (h₂ : IsGraphComponent C₂ G)
    (hinter : (V(C₁) ∩ V(C₂)).Nonempty) : C₁ = C₂ := by
  have hconn := isGraphConnected_subgraphUnion h₁.1 h₂.1 h₁.2.1 h₂.2.1 hinter
  have hunion_le : subgraphUnion G C₁ C₂ ≤ G := subgraphUnion_le h₁.1 h₂.1
  have h1 := h₁.2.2 (subgraphUnion G C₁ C₂) (le_subgraphUnion_left h₁.1 h₂.1) hunion_le hconn
  have h2 := h₂.2.2 (subgraphUnion G C₁ C₂) (le_subgraphUnion_right h₁.1 h₂.1) hunion_le hconn
  exact h1.symm.trans h2

theorem isGraphComponent_eq_reachableComponent {G C : Graph α β} (hC : IsGraphComponent C G)
    {v : α} (hv : v ∈ V(C)) : C = reachableComponent G v := by
  have hvG : v ∈ V(G) := hC.1.vertexSet_mono hv
  exact isGraphComponent_eq_of_mem_inter hC (isGraphComponent_reachableComponent hvG)
    ⟨v, hv, self_mem_reachableComponent hvG⟩

theorem isClosedSubgraph_of_isGraphComponent {G C : Graph α β} (hC : IsGraphComponent C G) :
    C ≤c G := by
  obtain ⟨v, hv⟩ := hC.2.1.1
  rw [isGraphComponent_eq_reachableComponent hC hv]
  refine IsClosedSubgraph.mk' (reachableComponent_le G v) fun e x hinc hx => ?_
  obtain ⟨y, hxy⟩ := hinc
  have hx' : x ∈ V(reachableComponent G v) := hx
  obtain ⟨_, ⟨Wx⟩⟩ := hx
  have hy : y ∈ V(reachableComponent G v) :=
    ⟨hxy.right_mem, ⟨Wx.append (.cons hxy (.nil hxy.right_mem))⟩⟩
  exact ⟨x, y, hxy, hx', hy⟩

theorem mem_graphComponent_iff_of_isLink {G C : Graph α β} (hC : IsGraphComponent C G)
    {e : β} {x y : α} (hxy : G.IsLink e x y) :
    x ∈ V(C) ↔ y ∈ V(C) :=
  (isClosedSubgraph_of_isGraphComponent hC).mem_iff_of_isLink hxy

/-! ## Cyclic permutations (`CyclicPerm`) -/

namespace CyclicPerm

variable {Ω : CyclicPerm α}

theorem toFun_mem {x : α} (hx : x ∈ Ω.bar) : Ω x ∈ Ω.bar :=
  Ω.bijOn.mapsTo hx

theorem iterate_mem (k : ℕ) {x : α} (hx : x ∈ Ω.bar) : (Ω.toFun^[k]) x ∈ Ω.bar := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact Ω.toFun_mem ih

theorem injOn_iterate (k : ℕ) : Set.InjOn (Ω.toFun^[k]) Ω.bar := by
  induction k with
  | zero => exact Set.injOn_id Ω.bar
  | succ k ih =>
    intro x hx y hy hxy
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at hxy
    exact ih hx hy (Ω.bijOn.injOn (Ω.iterate_mem k hx) (Ω.iterate_mem k hy) hxy)

theorem exists_pos_period {x : α} (hx : x ∈ Ω.bar) :
    ∃ n : ℕ, 1 ≤ n ∧ (Ω.toFun^[n]) x = x := by
  obtain ⟨k, hk⟩ := Ω.single_orbit (Ω x) (Ω.toFun_mem hx) x hx
  refine ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k), ?_⟩
  rw [Function.iterate_succ_apply]
  exact hk

theorem FirstHitIn.unique {X : Set α} {x y₁ y₂ : α}
    (h₁ : Ω.FirstHitIn X x y₁) (h₂ : Ω.FirstHitIn X x y₂) : y₁ = y₂ := by
  rcases h₁ with ⟨k₁, hk₁, rfl, hy₁, hmin₁⟩
  rcases h₂ with ⟨k₂, hk₂, rfl, hy₂, hmin₂⟩
  rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
  · exact (hmin₂ k₁ hk₁ hlt hy₁).elim
  · rfl
  · exact (hmin₁ k₂ hk₂ hgt hy₂).elim

theorem exists_firstHitIn {X : Set α} {x : α} (hx : x ∈ Ω.bar)
    (hX : (Ω.bar ∩ X).Nonempty) : ∃ y, Ω.FirstHitIn X x y := by
  classical
  rcases hX with ⟨z, hzΩ, hzX⟩
  obtain ⟨k₀, hk₀⟩ := Ω.single_orbit (Ω x) (Ω.toFun_mem hx) z hzΩ
  have hex : ∃ k : ℕ, 1 ≤ k ∧ (Ω.toFun^[k]) x ∈ X := by
    refine ⟨k₀ + 1, Nat.succ_le_succ (Nat.zero_le k₀), ?_⟩
    rw [Function.iterate_succ_apply]
    simpa [hk₀] using hzX
  let k := Nat.find hex
  have hk_spec := Nat.find_spec hex
  refine ⟨(Ω.toFun^[k]) x, k, hk_spec.1, rfl, hk_spec.2, fun j hj1 hjlt hjX => ?_⟩
  exact Nat.find_min hex hjlt ⟨hj1, hjX⟩

theorem FirstHitIn.mem_bar {X : Set α} {x y : α} (hx : x ∈ Ω.bar)
    (h : Ω.FirstHitIn X x y) : y ∈ Ω.bar := by
  rcases h with ⟨k, _, rfl, _, _⟩
  exact Ω.iterate_mem k hx

theorem FirstHitIn.mem_set {X : Set α} {x y : α} (h : Ω.FirstHitIn X x y) : y ∈ X := by
  rcases h with ⟨_, _, _, hy, _⟩
  exact hy

theorem isClockwise3_iff {v₁ v₂ v₃ : α} :
    Ω.IsClockwise3 v₁ v₂ v₃ ↔
      v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
      v₁ ∈ Ω.bar ∧ v₂ ∈ Ω.bar ∧ v₃ ∈ Ω.bar ∧
      Ω.FirstHitIn {v₁, v₂, v₃} v₁ v₂ ∧
      Ω.FirstHitIn {v₁, v₂, v₃} v₂ v₃ ∧
      Ω.FirstHitIn {v₁, v₂, v₃} v₃ v₁ := by
  unfold IsClockwise3 IsClockwiseSeq
  constructor
  · rintro ⟨hnodup, hmem, hhit⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hnodup
    have hset : {v | v ∈ ([v₁, v₂, v₃] : List α)} = {v₁, v₂, v₃} := by
      ext x; simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    have h0 : Ω.FirstHitIn {v₁, v₂, v₃} v₁ v₂ := by
      have := hhit 0 (by simp)
      rwa [hset] at this
    have h1 : Ω.FirstHitIn {v₁, v₂, v₃} v₂ v₃ := by
      have := hhit 1 (by simp)
      rwa [hset] at this
    have h2 : Ω.FirstHitIn {v₁, v₂, v₃} v₃ v₁ := by
      have := hhit 2 (by simp)
      rw [hset] at this
      simpa using this
    refine ⟨hnodup.1.1, hnodup.1.2, hnodup.2.1,
      hmem v₁ (by simp), hmem v₂ (by simp), hmem v₃ (by simp), h0, h1, h2⟩
  · rintro ⟨h12, h13, h23, hv1, hv2, hv3, hhit0, hhit1, hhit2⟩
    have hset : {v | v ∈ ([v₁, v₂, v₃] : List α)} = {v₁, v₂, v₃} := by
      ext x; simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    refine ⟨?_, ?_, ?_⟩
    · simp [h12, h13, h23]
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    · intro i hi
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hi
      rw [hset]
      rcases i with _ | _ | _ | i
      · exact hhit0
      · exact hhit1
      · simpa using hhit2
      · omega

theorem isClockwise3_rotate {v₁ v₂ v₃ : α} (h : Ω.IsClockwise3 v₁ v₂ v₃) :
    Ω.IsClockwise3 v₂ v₃ v₁ := by
  rw [isClockwise3_iff] at h ⊢
  rcases h with ⟨h12, h13, h23, hv1, hv2, hv3, hhit0, hhit1, hhit2⟩
  have hset : ({v₂, v₃, v₁} : Set α) = {v₁, v₂, v₃} := by
    ext x; simp [or_comm, or_left_comm]
  rw [hset]
  exact ⟨h23, h12.symm, h13.symm, hv2, hv3, hv1, hhit1, hhit2, hhit0⟩

theorem not_firstHitIn_self {X : Set α} {x u : α}
    (hx : x ∈ Ω.bar) (hu : u ∈ Ω.bar) (huX : u ∈ X) (hne : u ≠ x) :
    ¬ Ω.FirstHitIn X x x := by
  rintro ⟨k, hk1, hk_eq, _, hmin⟩
  obtain ⟨j, hj⟩ := Ω.single_orbit (Ω x) (Ω.toFun_mem hx) u hu
  have hj_eq : (Ω.toFun^[j + 1]) x = u := by
    rw [Function.iterate_succ_apply]; exact hj
  have hmul : ∀ d : ℕ, (Ω.toFun^[k * d]) x = x := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, hk_eq]
  have hrem : (Ω.toFun^[(j + 1) % k]) x = u := by
    rw [← hj_eq]
    conv_rhs => rw [← Nat.div_add_mod (j + 1) k, add_comm]
    rw [Function.iterate_add_apply, hmul]
  have hmod_lt : (j + 1) % k < k := Nat.mod_lt _ (Nat.zero_lt_of_lt hk1)
  rcases Nat.eq_zero_or_pos ((j + 1) % k) with h0 | hpos
  · rw [h0, Function.iterate_zero_apply] at hrem
    exact hne hrem.symm
  · exact hmin ((j + 1) % k) hpos hmod_lt (hrem ▸ huX)

theorem FirstHitIn.inj_left {X : Set α} {x₁ x₂ z : α}
    (hx₁ : x₁ ∈ Ω.bar) (hx₂ : x₂ ∈ Ω.bar) (hx₁X : x₁ ∈ X) (hx₂X : x₂ ∈ X)
    (h₁ : Ω.FirstHitIn X x₁ z) (h₂ : Ω.FirstHitIn X x₂ z) : x₁ = x₂ := by
  rcases h₁ with ⟨k₁, hk₁, rfl, _, hmin₁⟩
  rcases h₂ with ⟨k₂, hk₂, heq, _, hmin₂⟩
  rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
  · have hd_pos : 1 ≤ k₂ - k₁ := Nat.le_sub_of_add_le (by omega)
    have hd_lt : k₂ - k₁ < k₂ := Nat.sub_lt (by omega) (by omega)
    have hiter : (Ω.toFun^[k₁]) ((Ω.toFun^[k₂ - k₁]) x₂) = (Ω.toFun^[k₁]) x₁ := by
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hlt), heq]
    have hmid := Ω.injOn_iterate k₁ (Ω.iterate_mem (k₂ - k₁) hx₂) hx₁ hiter
    exact (hmin₂ (k₂ - k₁) hd_pos hd_lt (hmid ▸ hx₁X)).elim
  · exact Ω.injOn_iterate k₁ hx₁ hx₂ heq.symm
  · have hd_pos : 1 ≤ k₁ - k₂ := Nat.le_sub_of_add_le (by omega)
    have hd_lt : k₁ - k₂ < k₁ := Nat.sub_lt (by omega) (by omega)
    have hiter : (Ω.toFun^[k₂]) ((Ω.toFun^[k₁ - k₂]) x₁) = (Ω.toFun^[k₂]) x₂ := by
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt hgt), ← heq]
    have hmid := Ω.injOn_iterate k₂ (Ω.iterate_mem (k₁ - k₂) hx₁) hx₂ hiter
    exact (hmin₁ (k₁ - k₂) hd_pos hd_lt (hmid ▸ hx₂X)).elim

theorem isClockwise3_trichotomy {v₁ v₂ v₃ : α}
    (hv₁ : v₁ ∈ Ω.bar) (hv₂ : v₂ ∈ Ω.bar) (hv₃ : v₃ ∈ Ω.bar)
    (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h23 : v₂ ≠ v₃) :
    (Ω.IsClockwise3 v₁ v₂ v₃ ∧ ¬ Ω.IsClockwise3 v₁ v₃ v₂) ∨
      (Ω.IsClockwise3 v₁ v₃ v₂ ∧ ¬ Ω.IsClockwise3 v₁ v₂ v₃) := by
  have hne1 : (Ω.bar ∩ ({v₁, v₂, v₃} : Set α)).Nonempty := ⟨v₁, hv₁, by simp⟩
  obtain ⟨y₁, hy₁⟩ := Ω.exists_firstHitIn hv₁ hne1
  obtain ⟨y₂, hy₂⟩ := Ω.exists_firstHitIn hv₂ hne1
  obtain ⟨y₃, hy₃⟩ := Ω.exists_firstHitIn hv₃ hne1
  have hy₁_ne : y₁ ≠ v₁ := fun h =>
    Ω.not_firstHitIn_self hv₁ hv₂ (by simp) h12.symm (h ▸ hy₁)
  have hy₂_ne : y₂ ≠ v₂ := fun h =>
    Ω.not_firstHitIn_self hv₂ hv₃ (by simp) h23.symm (h ▸ hy₂)
  have hy₃_ne : y₃ ≠ v₃ := fun h =>
    Ω.not_firstHitIn_self hv₃ hv₁ (by simp) h13 (h ▸ hy₃)
  have hy₁_mem := hy₁.mem_set
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy₁_mem
  rcases hy₁_mem with h | h | h
  · exact (hy₁_ne h).elim
  · rw [h] at hy₁
    have hy₃_mem := hy₃.mem_set
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy₃_mem
    have hy₃_eq : y₃ = v₁ := by
      rcases hy₃_mem with h3 | h3 | h3
      · exact h3
      · rw [h3] at hy₃
        exact (h13 (hy₁.inj_left hv₁ hv₃ (by simp) (by simp) hy₃)).elim
      · exact (hy₃_ne h3).elim
    rw [hy₃_eq] at hy₃
    have hy₂_mem := hy₂.mem_set
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy₂_mem
    have hy₂_eq : y₂ = v₃ := by
      rcases hy₂_mem with h2 | h2 | h2
      · rw [h2] at hy₂
        exact (h23 (hy₂.inj_left hv₂ hv₃ (by simp) (by simp) hy₃)).elim
      · exact (hy₂_ne h2).elim
      · exact h2
    rw [hy₂_eq] at hy₂
    left
    refine ⟨isClockwise3_iff.2 ⟨h12, h13, h23, hv₁, hv₂, hv₃, hy₁, hy₂, hy₃⟩, ?_⟩
    rw [isClockwise3_iff]
    rintro ⟨_, _, _, _, _, _, hhit0', _, _⟩
    have hset : ({v₁, v₃, v₂} : Set α) = {v₁, v₂, v₃} := by
      ext x; simp [or_comm]
    rw [hset] at hhit0'
    exact h23 (hy₁.unique hhit0')
  · rw [h] at hy₁
    have hy₂_mem := hy₂.mem_set
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy₂_mem
    have hy₂_eq : y₂ = v₁ := by
      rcases hy₂_mem with h2 | h2 | h2
      · exact h2
      · exact (hy₂_ne h2).elim
      · rw [h2] at hy₂
        exact (h12 (hy₁.inj_left hv₁ hv₂ (by simp) (by simp) hy₂)).elim
    rw [hy₂_eq] at hy₂
    have hy₃_mem := hy₃.mem_set
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy₃_mem
    have hy₃_eq : y₃ = v₂ := by
      rcases hy₃_mem with h3 | h3 | h3
      · rw [h3] at hy₃
        exact (h23 (hy₂.inj_left hv₂ hv₃ (by simp) (by simp) hy₃)).elim
      · exact h3
      · exact (hy₃_ne h3).elim
    rw [hy₃_eq] at hy₃
    right
    have hset : ({v₁, v₃, v₂} : Set α) = {v₁, v₂, v₃} := by
      ext x; simp [or_comm]
    refine ⟨isClockwise3_iff.2 ⟨h13, h12, h23.symm, hv₁, hv₃, hv₂, ?_, ?_, ?_⟩, ?_⟩
    · rwa [hset]
    · rwa [hset]
    · rwa [hset]
    · rw [isClockwise3_iff]
      rintro ⟨_, _, _, _, _, _, hhit0', _, _⟩
      exact h23 (hhit0'.unique hy₁)

theorem interval_subset_bar (v₁ v₂ : α) : Ω.interval v₁ v₂ ⊆ Ω.bar :=
  fun _ hv => hv.1.1

theorem not_mem_interval_left (v₁ v₂ : α) : v₁ ∉ Ω.interval v₁ v₂ :=
  fun hv => hv.1.2 (by simp)

theorem not_mem_interval_right (v₁ v₂ : α) : v₂ ∉ Ω.interval v₁ v₂ :=
  fun hv => hv.1.2 (by simp)

theorem disjoint_interval_swap (v₁ v₂ : α) :
    Disjoint (Ω.interval v₁ v₂) (Ω.interval v₂ v₁) := by
  rw [Set.disjoint_left]
  intro v hv₁ hv₂
  have h1 := hv₁.2
  have h2 := isClockwise3_rotate (isClockwise3_rotate hv₂.2)
  have htri := isClockwise3_trichotomy
    (isClockwise3_iff.1 h1).2.2.2.1
    (isClockwise3_iff.1 h1).2.2.2.2.1
    (isClockwise3_iff.1 h1).2.2.2.2.2.1
    (isClockwise3_iff.1 h1).1
    (isClockwise3_iff.1 h1).2.1
    (isClockwise3_iff.1 h1).2.2.1
  rcases htri with ⟨_, hnot⟩ | ⟨_, hnot⟩
  · exact hnot h2
  · exact hnot h1

theorem mem_interval_or_interval_swap {v₁ v₂ v : α}
    (hv₁ : v₁ ∈ Ω.bar) (hv₂ : v₂ ∈ Ω.bar) (hv : v ∈ Ω.bar)
    (h12 : v₁ ≠ v₂) (hv1 : v ≠ v₁) (hv2 : v ≠ v₂) :
    v ∈ Ω.interval v₁ v₂ ∨ v ∈ Ω.interval v₂ v₁ := by
  rcases isClockwise3_trichotomy hv₁ hv hv₂ hv1.symm h12 hv2 with ⟨h1, _⟩ | ⟨h2, _⟩
  · left; exact ⟨⟨hv, by simp [hv1, hv2]⟩, h1⟩
  · right; exact ⟨⟨hv, by simp [hv1, hv2]⟩, isClockwise3_rotate h2⟩

theorem interval_union_interval_swap {v₁ v₂ : α}
    (hv₁ : v₁ ∈ Ω.bar) (hv₂ : v₂ ∈ Ω.bar) (h12 : v₁ ≠ v₂) :
    Ω.interval v₁ v₂ ∪ Ω.interval v₂ v₁ = Ω.bar \ {v₁, v₂} := by
  ext v
  constructor
  · rintro (hv | hv)
    · exact hv.1
    · refine ⟨hv.1.1, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact hv.1.2 (by simp)
      · exact hv.1.2 (by simp)
  · rintro ⟨hv, hne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    exact mem_interval_or_interval_swap hv₁ hv₂ hv h12 hne.1 hne.2

end CyclicPerm

/-! ## Paths, `X → Y` paths, avoiding, and catching -/

theorem IsGraphPathWithEnds.vertexSet_finite {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) : V(P).Finite := by
  classical
  rcases hP with ⟨_, W, _, hV, _⟩
  rw [hV]
  exact W.support.toFinset.finite_toSet.subset fun x hx => List.mem_toFinset.2 hx

theorem IsGraphPathWithEnds.edgeSet_finite {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) : E(P).Finite := by
  classical
  rcases hP with ⟨_, W, _, _, hE⟩
  rw [hE]
  exact W.edges.toFinset.finite_toSet.subset fun e he => List.mem_toFinset.2 he

theorem le_deleteVertices {G H : Graph α β} {Z : Set α} (hHG : H ≤ G)
    (hdisj : Disjoint V(H) Z) : H ≤ deleteVertices G Z := by
  rw [(Compatible.of_le_le hHG (deleteVertices_le G Z)).le_iff]
  refine ⟨subset_sdiff.mpr ⟨hHG.vertexSet_mono, hdisj⟩, fun e he => ?_⟩
  obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet he
  exact ⟨x, y, (deleteVertices_isLink G Z).mpr
    ⟨hxy.mono hHG, disjoint_left.mp hdisj hxy.left_mem, disjoint_left.mp hdisj hxy.right_mem⟩⟩

theorem IsGraphPathWithEnds.le_deleteVertices {G P : Graph α β} {a b : α} {Z : Set α}
    (hP : IsGraphPathWithEnds G P a b) (hav : Avoids P Z) :
    P ≤ deleteVertices G Z :=
  GraphMinor.GM09.le_deleteVertices hP.1 hav.symm

theorem IsGraphPathWithEnds.in_deleteVertices {G P : Graph α β} {a b : α} {Z : Set α}
    (hP : IsGraphPathWithEnds G P a b) (hav : Avoids P Z) :
    IsGraphPathWithEnds (deleteVertices G Z) P a b :=
  hP.of_le (hP.le_deleteVertices hav)

/-- Any path `P` in `G` from `u ∈ X` to `v ∈ Y` contains an `X → Y` subpath `Q ≤ P`. -/
theorem IsGraphPathWithEnds.exists_isFromToPathWithEnds {G P : Graph α β} {u v : α}
    (hP : IsGraphPathWithEnds G P u v) {X Y : Set α} (hu : u ∈ X) (hv : v ∈ Y) :
    ∃ x ∈ X, ∃ y ∈ Y, ∃ Q : Graph α β,
      Q ≤ P ∧ IsFromToPathWithEnds G Q X Y x y := by
  classical
  have hind : ∀ (n : ℕ) {a b : α} {P₁ : Graph α β},
      IsGraphPathWithEnds G P₁ a b → P₁ ≤ P → V(P₁).ncard = n → a ∈ X → b ∈ Y →
      ∃ x ∈ X, ∃ y ∈ Y, ∃ Q : Graph α β,
        Q ≤ P ∧ IsFromToPathWithEnds G Q X Y x y := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro a b P₁ hP₁ hP₁P hcard ha hb
      have hfin : V(P₁).Finite := hP₁.vertexSet_finite
      by_cases hhitX : ∃ z ∈ V(P₁), z ∈ X ∧ z ≠ a
      · rcases hhitX with ⟨z, hzP, hzX, hza⟩
        obtain ⟨Q₁, Q₂, hQ₁P₁, hQ₂P₁, _, hQ₂, _, hinter, _⟩ := hP₁.exists_split_at hzP
        have ha_not_Q₂ : a ∉ V(Q₂) := by
          intro haQ₂
          have ha_in : a ∈ V(Q₁) ∩ V(Q₂) := ⟨( ‹IsGraphPathWithEnds P₁ Q₁ a z› ).left_mem, haQ₂⟩
          rw [hinter, mem_singleton_iff] at ha_in
          exact hza ha_in.symm
        have hlt : V(Q₂).ncard < n := by
          rw [← hcard]
          exact Set.ncard_lt_ncard ⟨hQ₂P₁.vertexSet_mono, fun hsub => ha_not_Q₂
            (hsub hP₁.left_mem)⟩ hfin
        exact ih V(Q₂).ncard hlt (hQ₂.mono hP₁.le) (hQ₂P₁.trans hP₁P) rfl hzX hb
      · by_cases hhitY : ∃ z ∈ V(P₁), z ∈ Y ∧ z ≠ b
        · rcases hhitY with ⟨z, hzP, hzY, hzb⟩
          obtain ⟨Q₁, Q₂, hQ₁P₁, _, hQ₁, hQ₂, _, hinter, _⟩ := hP₁.exists_split_at hzP
          have hb_not_Q₁ : b ∉ V(Q₁) := by
            intro hbQ₁
            have hb_in : b ∈ V(Q₁) ∩ V(Q₂) := ⟨hbQ₁, hQ₂.right_mem⟩
            rw [hinter, mem_singleton_iff] at hb_in
            exact hzb hb_in.symm
          have hlt : V(Q₁).ncard < n := by
            rw [← hcard]
            exact Set.ncard_lt_ncard ⟨hQ₁P₁.vertexSet_mono, fun hsub => hb_not_Q₁
              (hsub hP₁.right_mem)⟩ hfin
          exact ih V(Q₁).ncard hlt (hQ₁.mono hP₁.le) (hQ₁P₁.trans hP₁P) rfl ha hzY
        · refine ⟨a, ha, b, hb, P₁, hP₁P, hP₁, ?_, ?_⟩
          · ext z
            simp only [mem_inter_iff, mem_singleton_iff]
            exact ⟨fun ⟨hzP, hzX⟩ => by_contra fun hne => hhitX ⟨z, hzP, hzX, hne⟩,
              fun h => h ▸ ⟨hP₁.left_mem, ha⟩⟩
          · ext z
            simp only [mem_inter_iff, mem_singleton_iff]
            exact ⟨fun ⟨hzP, hzY⟩ => by_contra fun hne => hhitY ⟨z, hzP, hzY, hne⟩,
              fun h => h ▸ ⟨hP₁.right_mem, hb⟩⟩
  exact hind V(P).ncard hP le_rfl rfl hu hv

/-- Every walk `W` in `G` from `u ∈ X` to `v ∈ Y` contains an `X → Y` path `Q ≤ walkSubgraph W`. -/
theorem exists_isFromToPathWithEnds_of_walk {G : Graph α β} {u v : α}
    (W : GraphWalk G u v) {X Y : Set α} (hu : u ∈ X) (hv : v ∈ Y) :
    ∃ x ∈ X, ∃ y ∈ Y, ∃ Q : Graph α β,
      Q ≤ walkSubgraph W ∧
      V(Q) ⊆ {z | z ∈ W.support} ∧
      IsFromToPathWithEnds G Q X Y x y := by
  obtain ⟨W₀, hW₀, hsupp, hedges⟩ := exists_isSimple_subwalk W
  have hle : walkSubgraph W₀ ≤ walkSubgraph W := by
    rw [(Compatible.of_le_le (walkSubgraph_le W₀) (walkSubgraph_le W)).le_iff]
    rw [vertexSet_walkSubgraph, vertexSet_walkSubgraph, edgeSet_walkSubgraph, edgeSet_walkSubgraph]
    exact ⟨hsupp, hedges⟩
  obtain ⟨x, hx, y, hy, Q, hQP₀, hQ⟩ :=
    (isGraphPathWithEnds_walkSubgraph hW₀).exists_isFromToPathWithEnds hu hv
  refine ⟨x, hx, y, hy, Q, hQP₀.trans hle, ?_, hQ⟩
  have hsub := (hQP₀.trans hle).vertexSet_mono
  rwa [vertexSet_walkSubgraph] at hsub

end GraphMinor.GM09
