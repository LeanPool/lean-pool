/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section4d
public import LeanPool.GraphMinor.GM20.Bag

/-!
# Graph Minors XX, Section 4, (4.10)

Each edge `e` of a condensation `P₁` of `P₂` stands for a piece `A_e` of `P₂`, all of whose vertices
are roots of `A_e`. As in the paper, we give `e` a label recording `Q₂|A_e`. Since `P₁` is
removable,
each piece is removable (`Pieces.emptySubgraph_mem`): the grouping with no adjacencies is feasible
in
it, and all vertices of the piece are roots, so each edge of the piece has that grouping.

Differences from the paper:
- The paper labels `e` by the patchwork `Q₂|A_e` ordered by simulation, and says that this order is
  a
  well-quasi-order by a proof like that of (8.4) of Graph Minors IV. That claim is proved in
  `Section4eOmega.lean` (`wqo_omega₁`), by (8.4) of Graph Minors IV applied to a star with one
  vertex. Here we use the `bag` of the piece instead, with the order of Higman's lemma.
- The paper derives the encoding from (5.7) of Graph Minors XVIII. That result needs `{A_e}` to be a
  set with a new edge for each member, but two edges of `P₁` can have equal pieces with no edges,
  and
  it needs an expansion of the two hearts, whose patches `gr(Q₂|A_e)` are larger than `Δ₁(e)`. All
  pieces here have only roots as vertices, so we prove the needed case directly
  (`simulated_of_pieces`): an edge `f` of `A_e` goes to the matching edge of `A_{η(e)}`, and a
  realization is assembled from realizations of the pieces that `η` misses.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v} {Ω Ω' : Type*}

theorem sameComponent_iff_connectedIn {K : (⊤ : SimpleGraph α).Subgraph} {p q : α} :
    sameComponent K p q ↔ ConnectedIn K p q := by
  rw [sameComponent_iff]
  constructor
  · rintro ⟨hp, hq, hr⟩
    exact ⟨component K ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, self_mem_componentVerts K ⟨p, hp⟩, ⟨hq, hr⟩⟩
  · rintro ⟨_, ⟨x, rfl⟩, ⟨hp, hxp⟩, ⟨hq, hxq⟩⟩
    exact ⟨hp, hq, hxp.symm.trans hxq⟩

theorem sameComponent_of_forall_adj {K H : (⊤ : SimpleGraph α).Subgraph} (hv : K.verts ⊆ H.verts)
    (h : ∀ a b, K.Adj a b → sameComponent H a b) {p q : α} (hpq : sameComponent K p q) :
    sameComponent H p q := by
  obtain ⟨hp, hq, hr⟩ := sameComponent_iff.mp hpq
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  suffices ∀ y : K.verts, Relation.ReflTransGen K.coe.Adj ⟨p, hp⟩ y → sameComponent H p y.1 from
    this ⟨q, hq⟩ hr
  intro y hy
  induction hy with
  | refl => exact sameComponent_iff.mpr ⟨hv hp, hv hp, SimpleGraph.Reachable.refl _⟩
  | tail _ hab ih => exact ih.trans (h _ _ hab)

/-- The relation that `S` is a condensation of `Q` with pieces `A` (Graph Minors XX, Section 4,
page 335), where `S` and `Q` may have labels. -/
structure Pieces (N : ℕ) (Q : Patchwork Ω α β) (S : Patchwork Ω' α β)
    (A : β → RootedHypergraph α β) : Prop where
  vertexSet_eq : S.G.vertexSet = Q.G.vertexSet
  roots_eq : S.G.roots = Q.G.roots
  dom_S : S.dom = S.G.edgeSet
  dom_Q : Q.dom = Q.G.edgeSet
  le : ∀ e ∈ S.G.edgeSet, (A e).toHypergraph ≤ Q.G.toHypergraph
  vertexSet_A : ∀ e ∈ S.G.edgeSet, (A e).vertexSet = S.G.ends e
  roots_A : ∀ e ∈ S.G.edgeSet, (A e).roots = S.μ e
  iUnion_eq : ⋃ e ∈ S.G.edgeSet, (A e).edgeSet = Q.G.edgeSet
  disjoint : ∀ e ∈ S.G.edgeSet, ∀ e' ∈ S.G.edgeSet, e ≠ e' → Disjoint (A e).edgeSet (A e').edgeSet
  feasible : ∀ e ∈ S.G.edgeSet, ∀ K ∈ S.Δ e, IsFeasibleGrouping (Q.restrict (A e)) K
  removable : S.IsRemovable
  roots_le : ∀ e ∈ S.G.edgeSet, (A e).roots.length ≤ N

namespace Pieces

variable {N : ℕ} {Q : Patchwork Ω α β} {S : Patchwork Ω' α β} {A : β → RootedHypergraph α β}

/-- Every vertex of a piece is a root of it. -/
theorem mem_roots (h : Pieces N Q S A) {e : β} (he : e ∈ S.G.edgeSet) {x : α}
    (hx : x ∈ (A e).vertexSet) : x ∈ (A e).roots := by
  have hd : e ∈ S.dom := h.dom_S ▸ he
  rw [h.vertexSet_A e he, ← S.μ_set e hd] at hx
  rw [h.roots_A e he]
  exact hx

/-- The ends of an edge of a piece are roots of that piece. -/
theorem end_mem_roots (h : Pieces N Q S A) {e f : β} (he : e ∈ S.G.edgeSet)
    (hf : f ∈ (A e).edgeSet) {x : α} (hx : Q.G.Inc f x) : x ∈ (A e).roots := by
  have hinc := (inc_iff_of_le (h.le e he) hf).mpr hx
  exact h.mem_roots he ((A e).vertex_mem_of_inc hinc)

theorem eq_of_mem (h : Pieces N Q S A) {e e' f : β} (he : e ∈ S.G.edgeSet)
    (he' : e' ∈ S.G.edgeSet) (hf : f ∈ (A e).edgeSet) (hf' : f ∈ (A e').edgeSet) : e = e' := by
  by_contra hne
  exact Set.disjoint_left.mp (h.disjoint e he e' he' hne) hf hf'

theorem exists_mem (h : Pieces N Q S A) {f : β} (hf : f ∈ Q.G.edgeSet) :
    ∃ e ∈ S.G.edgeSet, f ∈ (A e).edgeSet := by
  rw [← h.iUnion_eq] at hf
  simpa using hf

/-- Each edge of a piece has the grouping with no adjacencies. The reason is that this grouping is
feasible in the piece, because `S` is removable, and the vertices of the piece are roots. -/
theorem emptySubgraph_mem (h : Pieces N Q S A) {e f : β} (he : e ∈ S.G.edgeSet)
    (hf : f ∈ (A e).edgeSet) : emptySubgraph (Q.G.ends f) ∈ Q.Δ f := by
  obtain ⟨-, -, H, hH, hconn⟩ := h.feasible e he _ (h.removable e he)
  have hle := h.le e he
  have hverts : H.verts = (A e).vertexSet := hH.verts_eq
  obtain ⟨δ, hδ, rfl⟩ := id hH
  have hfm := hδ f hf
  rw [Patchwork.restrict_Δ hle hf] at hfm
  have hV := ((Q.Δ f).verts_eq _ hfm).trans (Q.Δ_verts f (hle.edgeSet_subset hf))
  have hadj : ∀ a b, ¬ (δ f).Adj a b := by
    intro a b hab
    have hH' : (realizationOf (Q.restrict (A e)).G.toHypergraph δ).Adj a b :=
      realizationOf_adj.mpr ⟨f, hf, hab⟩
    have ha := (realizationOf (Q.restrict (A e)).G.toHypergraph δ).edge_vert hH'
    have hb := (realizationOf (Q.restrict (A e)).G.toHypergraph δ).edge_vert hH'.symm
    rw [hverts] at ha hb
    have := (hconn a (h.mem_roots he ha) b (h.mem_roots he hb) hH'.ne).mp
      (sameComponent_iff_connectedIn.mp (sameComponent_of_adj hH'))
    exact not_emptySubgraph_adj this
  have : δ f = emptySubgraph (Q.G.ends f) := by
    apply SimpleGraph.Subgraph.ext
    · exact hV
    · funext a b
      exact propext ⟨fun h' ↦ absurd h' (hadj a b), fun h' ↦ absurd h' not_emptySubgraph_adj⟩
  rw [← this]
  exact hfm

/-- A grouping in the patch of `e` is the connection pattern of a choice of groupings on the edges
of
the piece. -/
theorem exists_choice (h : Pieces N Q S A) {e : β} (he : e ∈ S.G.edgeSet) {K} (hK : K ∈ S.Δ e) :
    ∃ d : β → (⊤ : SimpleGraph α).Subgraph, (∀ f ∈ (A e).edgeSet, d f ∈ Q.Δ f) ∧
      (∀ a b, ∀ f ∈ (A e).edgeSet, (d f).Adj a b → K.Adj a b) ∧
      ∀ a b, K.Adj a b → sameComponent (realizationOf (A e).toHypergraph d) a b := by
  obtain ⟨hgrp, hverts, H, hH, hconn⟩ := h.feasible e he K hK
  have hle := h.le e he
  have hvH : H.verts = (A e).vertexSet := hH.verts_eq
  obtain ⟨δ, hδ, rfl⟩ := id hH
  refine ⟨δ, fun f hf ↦ ?_, fun a b f hf hab ↦ ?_, fun a b hab ↦ ?_⟩
  · have := hδ f hf
    rwa [Patchwork.restrict_Δ hle hf] at this
  · have hH' : (realizationOf (Q.restrict (A e)).G.toHypergraph δ).Adj a b :=
      realizationOf_adj.mpr ⟨f, hf, hab⟩
    have ha := (realizationOf (Q.restrict (A e)).G.toHypergraph δ).edge_vert hH'
    have hb := (realizationOf (Q.restrict (A e)).G.toHypergraph δ).edge_vert hH'.symm
    rw [hvH] at ha hb
    exact (hconn a (h.mem_roots he ha) b (h.mem_roots he hb) hH'.ne).mp
      (sameComponent_iff_connectedIn.mp (sameComponent_of_adj hH'))
  · have ha : a ∈ K.verts := K.edge_vert hab
    have hb : b ∈ K.verts := K.edge_vert hab.symm
    rw [hverts] at ha hb
    exact sameComponent_iff_connectedIn.mpr ((hconn a ha b hb hab.ne).mpr hab)

end Pieces

/-- The core of (4.10): a realizable expansion of the condensation `S` of `Q` in the condensation
`S'`
of `Q'`, with edge maps between the pieces, gives a simulation of `Q` in `Q'`. -/
theorem simulated_of_pieces {Ω₁ : Type*} [Preorder Ω] [Preorder Ω₁] {N : ℕ} {Q Q' : Patchwork Ω α β}
    {S S' : Patchwork Ω₁ α β} {A A' : β → RootedHypergraph α β} (hP : Pieces N Q S A)
    (hP' : Pieces N Q' S' A') {ηv : α → Set α} {ηe : β → β} (hη : IsRealizableExpansion S S' ηv ηe)
    (hmap : ∀ e ∈ S.G.edgeSet, ∃ g : β → β, InjOn g (A e).edgeSet ∧
      MapsTo g (A e).edgeSet (A' (ηe e)).edgeSet ∧ ∀ f ∈ (A e).edgeSet, Q.φ f ≤ Q'.φ (g f) ∧
        edgeCode N (A e).roots (Q.restrict (A e)) f =
          edgeCode N (A' (ηe e)).roots (Q'.restrict (A' (ηe e))) (g f)) :
    Simulated Q Q' := by
  classical
  obtain ⟨hex, H, hH, hcomp⟩ := hη
  choose! G hinj hmaps hgood using hmap
  have hcov : ∀ f ∈ Q.G.edgeSet, ∃ e ∈ S.G.edgeSet, f ∈ (A e).edgeSet := fun f hf ↦ hP.exists_mem hf
  choose! pc hpcE hpcA using hcov
  have hcov' : ∀ f ∈ Q'.G.edgeSet, ∃ e ∈ S'.G.edgeSet, f ∈ (A' e).edgeSet :=
    fun f hf ↦ hP'.exists_mem hf
  choose! pc' hpcE' hpcA' using hcov'
  have hVS : S.G.vertexSet = Q.G.vertexSet := hP.vertexSet_eq
  have hVS' : S'.G.vertexSet = Q'.G.vertexSet := hP'.vertexSet_eq
  have hunique' : ∀ {e f}, e ∈ S'.G.edgeSet → f ∈ (A' e).edgeSet → pc' f = e := fun {e f} he hf ↦
    hP'.eq_of_mem (hpcE' f ((hP'.le _ he).edgeSet_subset hf)) he
      (hpcA' f ((hP'.le _ he).edgeSet_subset hf)) hf
  -- Facts about one edge `f` of `Q`, in the piece of `e = pc f`.
  have hpiece : ∀ f ∈ Q.G.edgeSet, ∃ e ∈ S.G.edgeSet, f ∈ (A e).edgeSet ∧ pc f = e ∧
      G e f ∈ (A' (ηe e)).edgeSet ∧ ηe e ∈ S'.G.edgeSet ∧
      (Q.μ f).Nodup ∧ (∀ x ∈ Q.μ f, x ∈ (A e).roots) ∧
      (Q'.μ (G e f)).Nodup ∧ (∀ x ∈ Q'.μ (G e f), x ∈ (A' (ηe e)).roots) ∧
      marchCode N (A e).roots (Q.μ f) = marchCode N (A' (ηe e)).roots (Q'.μ (G e f)) ∧
      patchCode N (A e).roots (Q.Δ f) = patchCode N (A' (ηe e)).roots (Q'.Δ (G e f)) := by
    intro f hf
    have he := hpcE f hf
    have hfA := hpcA f hf
    have hee := hex.edge_mem _ he
    have hg := hmaps _ he hfA
    have hg' : G (pc f) f ∈ Q'.G.edgeSet := (hP'.le _ hee).edgeSet_subset hg
    have hd : f ∈ Q.dom := hP.dom_Q ▸ hf
    have hd' : G (pc f) f ∈ Q'.dom := hP'.dom_Q ▸ hg'
    have hc := (hgood _ he f hfA).2
    simp only [edgeCode, Prod.mk.injEq] at hc
    refine ⟨pc f, he, hfA, rfl, hg, hee, Q.μ_nodup f hd, fun x hx ↦ ?_,
      Q'.μ_nodup _ hd', fun x hx ↦ ?_, hc.2.2.1, ?_⟩
    · have h₁ : x ∈ {x | x ∈ Q.μ f} := hx
      rw [Q.μ_set f hd] at h₁
      exact hP.end_mem_roots he hfA h₁
    · have h₁ : x ∈ {x | x ∈ Q'.μ (G (pc f) f)} := hx
      rw [Q'.μ_set _ hd'] at h₁
      exact hP'.end_mem_roots hee hg h₁
    · have h₂ := hc.2.2.2
      rwa [Patchwork.restrict_Δ (hP.le _ he) hfA, Patchwork.restrict_Δ (hP'.le _ hee) hg] at h₂
  have hpos : ∀ e ∈ S.G.edgeSet, ∀ (i : Fin N) (x y : α), (A e).roots[i.1]? = some x →
      (A' (ηe e)).roots[i.1]? = some y → y ∈ ηv x := by
    intro e he i x y hx hy
    have hd : e ∈ S.dom := hP.dom_S ▸ he
    have hee := hex.edge_mem e he
    rw [hP.roots_A e he] at hx
    rw [hP'.roots_A _ hee] at hy
    obtain ⟨h₁, h₂⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨h₁', h₂'⟩ := List.getElem?_eq_some_iff.mp hy
    have := hex.μ_mem e hd i.1 h₁ h₁'
    rwa [h₂, h₂'] at this
  let ηe₂ : β → β := fun f ↦ G (pc f) f
  have himg : ∀ f ∈ Q.G.edgeSet, ηe₂ f ∈ (A' (ηe (pc f))).edgeSet := by
    intro f hf
    exact hmaps _ (hpcE f hf) (hpcA f hf)
  have hexp : IsExpansion Q Q' ηv ηe₂ := by
    refine
    { vertex_nonempty := fun v hv ↦ hex.vertex_nonempty v (hVS ▸ hv)
      vertex_subset := fun v hv ↦ hVS' ▸ hex.vertex_subset v (hVS ▸ hv)
      edge_mem := fun f hf ↦ (hP'.le _ (hex.edge_mem _ (hpcE f hf))).edgeSet_subset (himg f hf)
      vertex_disjoint := fun v₁ h₁ v₂ h₂ hne ↦ hex.vertex_disjoint v₁ (hVS ▸ h₁) v₂ (hVS ▸ h₂) hne
      edge_injOn := ?_
      mem_dom_iff := fun f hf ↦ ?_
      ends_nonempty := fun f hf hd ↦ absurd (hP.dom_Q ▸ hf) hd
      μ_length := fun f hf ↦ ?_
      μ_mem := fun f hf i hi hi' ↦ ?_
      roots_length := ?_
      roots_mem := fun i hi hi' ↦ ?_
      maps_Δ := fun f hf ↦ ?_
      φ_le := fun f hf ↦ (hgood _ (hpcE f hf) f (hpcA f hf)).1 }
    · intro f₁ h₁ f₂ h₂ heq
      have he₁ := hpcE f₁ h₁
      have he₂ := hpcE f₂ h₂
      have h₃ := himg f₁ h₁
      rw [show ηe₂ f₁ = ηe₂ f₂ from heq] at h₃
      have hee : ηe (pc f₁) = ηe (pc f₂) :=
        hP'.eq_of_mem (hex.edge_mem _ he₁) (hex.edge_mem _ he₂) h₃ (himg f₂ h₂)
      have hpp : pc f₁ = pc f₂ := hex.edge_injOn he₁ he₂ hee
      have heq' : G (pc f₂) f₁ = G (pc f₂) f₂ := by
        have : G (pc f₁) f₁ = G (pc f₂) f₂ := heq
        rwa [hpp] at this
      exact hinj _ he₂ (hpp ▸ hpcA f₁ h₁) (hpcA f₂ h₂) heq'
    · have h₁ : ηe₂ f ∈ Q'.G.edgeSet :=
        (hP'.le _ (hex.edge_mem _ (hpcE f hf))).edgeSet_subset (himg f hf)
      rw [hP.dom_Q, hP'.dom_Q]
      exact iff_of_true hf h₁
    · have hf' : f ∈ Q.G.edgeSet := Q.dom_subset hf
      obtain ⟨e, he, -, rfl, -, hee, h₁, h₂, h₃, h₄, h₅, -⟩ := hpiece f hf'
      exact length_eq_of_code (hP.roots_le _ he) (hP'.roots_le _ hee) h₁ h₃ h₂ h₄ h₅
    · have hf' : f ∈ Q.G.edgeSet := Q.dom_subset hf
      obtain ⟨e, he, -, rfl, -, hee, h₁, h₂, h₃, h₄, h₅, -⟩ := hpiece f hf'
      have hx := h₂ _ (List.getElem_mem hi)
      obtain ⟨j, hj⟩ := exists_index (hP.roots_le _ he) hx
      obtain ⟨y, hy, hyj⟩ := marchCode_forward h₅
        ((length_le_of_subset h₁ h₂).trans (hP.roots_le _ he)) (List.getElem?_eq_getElem hi) hj
      have h₀ : (Q'.μ (ηe₂ f))[i] = y :=
        Option.some.inj ((List.getElem?_eq_getElem hi').symm.trans hy)
      rw [h₀]
      exact hpos _ he j _ y hj hyj
    · rw [← hP.roots_eq, ← hP'.roots_eq]
      exact hex.roots_length
    · simp only [← hP.roots_eq, ← hP'.roots_eq] at hi hi' ⊢
      exact hex.roots_mem i hi hi'
    · have hf' : f ∈ Q.G.edgeSet := Q.dom_subset hf
      obtain ⟨e, he, hfA, rfl, -, hee, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hpiece f hf'
      have hd' : ηe₂ f ∈ Q'.dom := by
        rw [hP'.dom_Q]
        exact (hP'.le _ hee).edgeSet_subset (himg f hf')
      refine mapsTo_of_code (hP.roots_le _ he) (hP'.roots_le _ hee) h₁ h₃ h₂ h₄ ?_ ?_ h₅ h₆
      · rw [Q.Δ_verts f hf', Q.μ_set f hf]
      · rw [Q'.Δ_verts _ (Q'.dom_subset hd'), Q'.μ_set _ hd']
  obtain ⟨δ, hδ, hHeq⟩ := id hH
  have hfree : ∀ e' ∈ S'.G.edgeSet, e' ∉ ηe '' S.G.edgeSet → _ := fun e' he' hne ↦
    hP'.exists_choice he' (hδ e' ⟨he', hne⟩)
  choose! D hD₁ hD₂ hD₃ using hfree
  let d₂ : β → (⊤ : SimpleGraph α).Subgraph := fun f' ↦
    if pc' f' ∈ ηe '' S.G.edgeSet then emptySubgraph (Q'.G.ends f') else D (pc' f') f'
  have hd₂in : ∀ {f'}, pc' f' ∈ ηe '' S.G.edgeSet → d₂ f' = emptySubgraph (Q'.G.ends f') :=
    fun hi ↦ ite_eq_left hi
  have hd₂out : ∀ {f'}, pc' f' ∉ ηe '' S.G.edgeSet → d₂ f' = D (pc' f') f' :=
    fun hi ↦ ite_eq_right hi
  let F : Set β := ηe₂ '' Q.G.edgeSet
  let H₂ := realizationOf (Q'.deleteEdges F).G.toHypergraph d₂
  have hH₂ : (Q'.deleteEdges F).IsRealization H₂ := by
    refine ⟨d₂, fun f' hf' ↦ ?_, rfl⟩
    have hE : f' ∈ Q'.G.edgeSet := hf'.1
    change d₂ f' ∈ Q'.Δ f'
    by_cases hi : pc' f' ∈ ηe '' S.G.edgeSet
    · rw [hd₂in hi]
      exact hP'.emptySubgraph_mem (hpcE' _ hE) (hpcA' _ hE)
    · rw [hd₂out hi]
      exact hD₁ _ (hpcE' _ hE) hi _ (hpcA' _ hE)
  have hvH : H.verts = Q'.G.vertexSet := hH.verts_eq.trans hVS'
  have hvH₂ : H₂.verts = Q'.G.vertexSet := hH₂.verts_eq
  have claimA : ∀ a b, H₂.Adj a b → sameComponent H a b := by
    intro a b hab
    obtain ⟨f', hf', hadj⟩ := realizationOf_adj.mp hab
    have hE : f' ∈ Q'.G.edgeSet := hf'.1
    by_cases hi : pc' f' ∈ ηe '' S.G.edgeSet
    · rw [hd₂in hi] at hadj
      exact absurd hadj not_emptySubgraph_adj
    · rw [hd₂out hi] at hadj
      have h₁ := hD₂ _ (hpcE' _ hE) hi a b f' (hpcA' _ hE) hadj
      apply sameComponent_of_adj
      rw [hHeq]
      exact realizationOf_adj.mpr ⟨pc' f', ⟨hpcE' _ hE, hi⟩, h₁⟩
  have claimB : ∀ a b, H.Adj a b → sameComponent H₂ a b := by
    intro a b hab
    rw [hHeq] at hab
    obtain ⟨e', he', hadj⟩ := realizationOf_adj.mp hab
    have he₁ : e' ∈ S'.G.edgeSet := he'.1
    have he₂ : e' ∉ ηe '' S.G.edgeSet := he'.2
    refine sameComponent.mono ⟨?_, ?_⟩ (hD₃ e' he₁ he₂ a b hadj)
    · rw [realizationOf_verts, hvH₂]
      · exact (hP'.le e' he₁).vertexSet_subset
      · intro f hf
        have hE := (hP'.le e' he₁).edgeSet_subset hf
        rw [(Q'.Δ f).verts_eq _ (hD₁ e' he₁ he₂ f hf), Q'.Δ_verts f hE,
          (hP'.le e' he₁).ends_eq f hf]
    · intro x y hxy
      obtain ⟨f', hf', hadj'⟩ := realizationOf_adj.mp hxy
      have hE := (hP'.le e' he₁).edgeSet_subset hf'
      have hpc : pc' f' = e' := hunique' he₁ hf'
      have hnot : f' ∉ F := by
        rintro ⟨f, hf, rfl⟩
        have hee := hP'.eq_of_mem he₁ (hex.edge_mem _ (hpcE f hf)) hf' (himg f hf)
        exact he₂ ⟨pc f, hpcE f hf, hee.symm⟩
      refine realizationOf_adj.mpr ⟨f', ⟨hE, hnot⟩, ?_⟩
      rw [hd₂out (by rwa [hpc]), hpc]
      exact hadj'
  refine ⟨ηv, ηe₂, hexp, H₂, hH₂, fun v hv ↦ ?_⟩
  have hv' : v ∈ S.G.vertexSet := hVS ▸ hv
  obtain ⟨D₀, hD₀, hDv⟩ := hcomp v hv'
  have hsub : ηv v ⊆ H₂.verts := by
    rw [hvH₂, ← hVS']
    exact hex.vertex_subset v hv'
  rw [exists_isComponent_verts_eq_iff (hex.vertex_nonempty v hv') hsub]
  refine ⟨fun a ha b hab ↦ ?_, fun a ha b hb ↦ ?_⟩
  · obtain ⟨D₁, hD₁', ha', hb'⟩ := sameComponent_iff_connectedIn.mp (claimA a b hab)
    have heq := hD₁'.eq_of_mem hD₀ ha' (hDv ▸ ha)
    rw [← hDv, ← heq]
    exact hb'
  · refine sameComponent_of_forall_adj (by rw [hvH, hvH₂]) claimB
      (sameComponent_iff_connectedIn.mpr ⟨D₀, hD₀, hDv ▸ ha, hDv ▸ hb⟩)

/-- A grouping feasible in a restriction of `P₂` is feasible in the same restriction of a completion
of `P₂`. -/
theorem feasible_transfer {Ω₂ : Type*} {P : Patchwork Ω α β} {Q : Patchwork Ω₂ α β}
    (hb : SameBase P Q) {B : RootedHypergraph α β} (hB : B.toHypergraph ≤ P.G.toHypergraph)
    {K : (⊤ : SimpleGraph α).Subgraph} (hK : IsFeasibleGrouping (P.restrict B) K) :
    IsFeasibleGrouping (Q.restrict B) K := by
  obtain ⟨h₁, h₂, H, hH, hc⟩ := hK
  refine ⟨h₁, h₂, H, hH.congr rfl rfl fun e he ↦ ?_, hc⟩
  have hB' : B.toHypergraph ≤ Q.G.toHypergraph := hb.hyper ▸ hB
  rw [Patchwork.restrict_Δ hB he, Patchwork.restrict_Δ hB' he]
  exact hb.Δ_eq (hB.edgeSet_subset he)

/-- Graph Minors XX, (4.10) (page 334): "Let $\mathcal{F}_1$ be a well-behaved set of removable
patchworks and let $\mathcal{F}_2$ be
a set of patchworks such that for each $P_2 \in \mathcal{F}_2$ some $P_1 \in \mathcal{F}_1$
is a condensation of $P_2$. Then $\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_10_proof {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁)
    (hrem : ∀ P ∈ 𝓕₁, P.IsRemovable) (h₂ : ∀ P₂ ∈ 𝓕₂, ∃ P₁ ∈ 𝓕₁, IsCondensation P₁ P₂) :
    WellBehaved 𝓕₂ := by
  obtain ⟨N, hN⟩ := theorem_4_1_proof h
  refine wellBehaved_of_encoding h fun Ω₂ _ hΩ₂ ↦ ⟨Bag Ω₂ N, inferInstance, wqo_bag hΩ₂ N,
    fun Q S ↦ ∃ A, Pieces N Q S A ∧ ∀ e ∈ S.G.edgeSet, S.φ e = bag N (Q.restrict (A e)), ?_, ?_⟩
  · rintro Q ⟨P₂, hP₂, hQ⟩
    obtain ⟨P₁, hP₁, hV, hr, hd₁, hd₂, A, hA, hU, hdis, hfeas⟩ := h₂ P₂ hP₂
    have hb := hQ.sameBase
    refine ⟨P₁.relabel fun e ↦ bag N (Q.restrict (A e)), ⟨P₁, hP₁, isCompletionOf_relabel _ _⟩, A,
      ?_, fun _ _ ↦ rfl⟩
    exact
    { vertexSet_eq := hV.trans hb.vertexSet_eq.symm
      roots_eq := hr.trans (congrArg (·.roots) hQ.G_eq).symm
      dom_S := hd₁
      dom_Q := hb.dom_eq.trans (hd₂.trans hb.edgeSet_eq.symm)
      le := fun e he ↦ hb.hyper ▸ (hA e he).1
      vertexSet_A := fun e he ↦ (hA e he).2.1
      roots_A := fun e he ↦ (hA e he).2.2
      iUnion_eq := hU.trans hb.edgeSet_eq.symm
      disjoint := hdis
      feasible := fun e he K hK ↦ feasible_transfer hb (hA e he).1 (hfeas e he K hK)
      removable := fun e he ↦ hrem P₁ hP₁ e he
      roots_le := fun e he ↦ by
        rw [(hA e he).2.2]
        exact hN P₁ hP₁ e (hd₁ ▸ he) }
  · rintro Q - Q' - S S' ⟨A, hP, hφ⟩ ⟨A', hP', hφ'⟩ ⟨ηv, ηe, hη⟩
    refine simulated_of_pieces hP hP' hη fun e he ↦ ?_
    have hle := hη.1.φ_le e he
    rw [hφ e he, hφ' _ (hη.1.edge_mem e he)] at hle
    obtain ⟨g, hi, hm, hg⟩ := exists_edgeMap hle
    exact ⟨g, hi, hm, hg⟩

end GraphMinor.GM20
