/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section4b

/-!
# Moving patchworks to a larger edge type

The paper gets (4.13) from `w` uses of (4.12) (Graph Minors XX, page 336). The patchworks in between
have some of the new edges `f` and some of the pieces `A_f`. The statement does not say that the
new edges are not edges of the pieces, so in a fixed edge type `β` a new edge `f` may have the same
name as an edge of another piece `A_{f'}`. We avoid this by moving to the edge type `ℕ × β`: the
edge
`e` becomes `(t e, e)` for a tag `t e`. The edges of `G₁` get the tag `0` and the new edges get the
tag `1`.

A patchwork and its tagged copy are each simulated in the other (`simulated_retag` and
`simulated_of_retag`), so tagging keeps sets well-behaved (`WellBehaved.retag_zero`), and a set
whose tagged copies lie in a well-behaved set is well-behaved (`wellBehaved_of_retag`). The rest of
the file shows that tagging commutes with the operations of (4.13): subhypergraphs, complements,
rooted locations, deletion of edges and restriction.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

/-! ### Tagged hypergraphs and patchworks -/

/-- The hypergraph `G` with each edge `e` renamed `(t e, e)`. -/
def retagHyper (t : β → ℕ) (G : Hypergraph α β) : Hypergraph α (ℕ × β) where
  vertexSet := G.vertexSet
  edgeSet := (fun e ↦ (t e, e)) '' G.edgeSet
  Inc p v := p.1 = t p.2 ∧ G.Inc p.2 v
  vertex_mem_of_inc _ _ h := G.vertex_mem_of_inc h.2
  edge_mem_of_inc p _ h := ⟨p.2, G.edge_mem_of_inc h.2, Prod.ext h.1.symm rfl⟩
  vertexSet_finite := G.vertexSet_finite
  edgeSet_finite := G.edgeSet_finite.image _

/-- The rooted hypergraph `G` with each edge `e` renamed `(t e, e)`. -/
def retagRooted (t : β → ℕ) (G : RootedHypergraph α β) : RootedHypergraph α (ℕ × β) where
  toHypergraph := retagHyper t G.toHypergraph
  roots := G.roots
  roots_nodup := G.roots_nodup
  roots_subset := G.roots_subset

theorem mem_retagHyper_edgeSet {t : β → ℕ} {G : Hypergraph α β} {p : ℕ × β} :
    p ∈ (retagHyper t G).edgeSet ↔ p.1 = t p.2 ∧ p.2 ∈ G.edgeSet := by
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨rfl, he⟩
  · rintro ⟨h, he⟩
    exact ⟨p.2, he, Prod.ext h.symm rfl⟩

theorem retagHyper_ends (t : β → ℕ) (G : Hypergraph α β) (e : β) :
    (retagHyper t G).ends (t e, e) = G.ends e := by
  ext v
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨rfl, h⟩⟩

/-- The patchwork `P` with each edge `e` renamed `(t e, e)`. -/
def retagPatchwork {Ω : Type*} (t : β → ℕ) (P : Patchwork Ω α β) : Patchwork Ω α (ℕ × β) where
  G := retagRooted t P.G
  dom := (fun e ↦ (t e, e)) '' P.dom
  μ p := P.μ p.2
  Δ p := P.Δ p.2
  φ p := P.φ p.2
  dom_subset := image_mono P.dom_subset
  μ_nodup := by
    rintro _ ⟨e, he, rfl⟩
    exact P.μ_nodup e he
  μ_set := by
    rintro _ ⟨e, he, rfl⟩
    rw [P.μ_set e he]
    exact (retagHyper_ends t P.G.toHypergraph e).symm
  Δ_verts := by
    rintro _ ⟨e, he, rfl⟩
    rw [P.Δ_verts e he]
    exact (retagHyper_ends t P.G.toHypergraph e).symm
  Δ_free := by
    rintro _ ⟨e, he, rfl⟩ hnd
    exact P.Δ_free e he fun hd ↦ hnd ⟨e, hd, rfl⟩

theorem IsActive.retag {Ω : Type*} {P : Patchwork Ω α β} (h : IsActive P) (t : β → ℕ) :
    IsActive (retagPatchwork t P) := by
  intro v hv
  obtain ⟨e, he, hinc⟩ := h v hv
  exact ⟨(t e, e), ⟨e, he, rfl⟩, rfl, hinc⟩

/-! ### Renaming edges keeps simulation -/

/-- If `P'` is `P` with the edges renamed by `ηe`, then `(v ↦ {v}, ηe)` is a realizable expansion of
`P` in `P'`. The proof is that of `GM04.IsRealizableExpansion.id`. -/
theorem isRealizableExpansion_of_rename {Ω : Type*} [Preorder Ω] {β' : Type*}
    {P : Patchwork Ω α β} {P' : Patchwork Ω α β'} (ηe : β → β')
    (hV : P'.G.vertexSet = P.G.vertexSet) (hroots : P'.G.roots = P.G.roots)
    (hE : ηe '' P.G.edgeSet = P'.G.edgeSet) (hinj : InjOn ηe P.G.edgeSet)
    (hinc : ∀ e ∈ P.G.edgeSet, ∀ v, P'.G.Inc (ηe e) v ↔ P.G.Inc e v)
    (hdom : ∀ e ∈ P.G.edgeSet, e ∈ P.dom ↔ ηe e ∈ P'.dom)
    (hμ : ∀ e ∈ P.dom, P'.μ (ηe e) = P.μ e) (hΔ : ∀ e ∈ P.dom, P'.Δ (ηe e) = P.Δ e)
    (hφ : ∀ e ∈ P.G.edgeSet, P'.φ (ηe e) = P.φ e) :
    IsRealizableExpansion P P' (fun v ↦ {v}) ηe := by
  have hexp : IsExpansion P P' (fun v ↦ {v}) ηe :=
    { vertex_nonempty := fun v _ ↦ Set.singleton_nonempty v
      vertex_subset := fun v hv w hw ↦ by
        obtain rfl : w = v := hw
        rw [hV]
        exact hv
      edge_mem := fun e he ↦ hE ▸ mem_image_of_mem ηe he
      vertex_disjoint := fun _ _ _ _ hne ↦ Set.disjoint_singleton.mpr hne
      edge_injOn := hinj
      mem_dom_iff := hdom
      ends_nonempty := fun e he _ v hv ↦ ⟨v, rfl, (hinc e he v).mpr hv⟩
      μ_length := fun e he ↦ by rw [hμ e he]
      μ_mem := fun e he i hi hi' ↦ List.getElem_of_eq (hμ e he) hi'
      roots_length := by rw [hroots]
      roots_mem := fun i hi hi' ↦ List.getElem_of_eq hroots hi'
      maps_Δ := fun e he δ hδ ↦ by
        have heE : e ∈ P.G.edgeSet := P.dom_subset he
        have hverts : δ.verts ⊆ {x | x ∈ P.μ e} := by
          rw [((P.Δ e).verts_eq δ hδ).trans (P.Δ_verts e heE), P.μ_set e he]
        rw [hμ e he, hΔ e he, marchMapSubgraph_id hverts]
        exact hδ
      φ_le := fun e he ↦ by rw [hφ e he] }
  have hnoE : ∀ e, e ∉ (P'.deleteEdges (ηe '' P.G.edgeSet)).G.edgeSet := by
    rintro e ⟨he, hnot⟩
    rw [← hE] at he
    exact hnot he
  refine ⟨hexp, emptySubgraph P.G.vertexSet, ?_, fun v hv ↦ ?_⟩
  · refine ⟨fun _ ↦ emptySubgraph ∅, fun e he ↦ absurd he (hnoE e), ?_⟩
    ext u w
    · simp only [emptySubgraph_verts, realizationOf, SimpleGraph.Subgraph.verts_sup,
        SimpleGraph.Subgraph.verts_iSup, mem_union, mem_iUnion, exists_prop]
      change u ∈ P.G.vertexSet ↔ u ∈ P'.G.vertexSet ∨ _
      rw [hV]
      simp
    · simp only [not_emptySubgraph_adj, realizationOf_adj, false_iff, not_exists]
      rintro e ⟨he, _⟩
      exact hnoE e he
  · let x : (emptySubgraph P.G.vertexSet).verts := ⟨v, hv⟩
    refine ⟨component (emptySubgraph P.G.vertexSet) x, ⟨x, rfl⟩, ?_⟩
    ext w
    simp only [component_verts, mem_componentVerts_iff, emptySubgraph_verts,
      Set.mem_singleton_iff]
    refine ⟨?_, fun hEq ↦ hEq ▸ ⟨hv, SimpleGraph.Reachable.refl x⟩⟩
    rintro ⟨hw, hr⟩
    suffices ∀ y : (emptySubgraph P.G.vertexSet).verts,
        (emptySubgraph P.G.vertexSet).coe.Reachable x y → y.1 = x.1 from
      this ⟨w, hw⟩ hr
    intro y hy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hy
    induction hy with
    | refl => rfl
    | @tail _ _ _ hab => exact False.elim hab

/-- A patchwork is simulated in its tagged copy. -/
theorem simulated_retag {Ω : Type*} [Preorder Ω] (t : β → ℕ) (P : Patchwork Ω α β) :
    Simulated P (retagPatchwork t P) :=
  ⟨_, _, isRealizableExpansion_of_rename (P' := retagPatchwork t P) (fun e ↦ (t e, e)) rfl rfl rfl
    (fun _ _ _ _ h ↦ congrArg Prod.snd h) (fun _ _ _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨rfl, h⟩⟩)
    (fun e _ ↦ ⟨fun h ↦ ⟨e, h, rfl⟩, fun ⟨e', h, hEq⟩ ↦ by
      obtain rfl : e' = e := congrArg Prod.snd hEq
      exact h⟩)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)⟩

/-- A patchwork `Q` whose edges are tagged `(t e, e)` is simulated in any patchwork `P` with the
same data under `e ↦ (t e, e)`. -/
theorem simulated_of_retag' {Ω : Type*} [Preorder Ω] {t : β → ℕ} {Q : Patchwork Ω α (ℕ × β)}
    {P : Patchwork Ω α β} (hG : Q.G = retagRooted t P.G)
    (hdom : Q.dom = (fun e ↦ (t e, e)) '' P.dom)
    (hμ : ∀ e ∈ P.dom, Q.μ (t e, e) = P.μ e) (hΔ : ∀ e ∈ P.dom, Q.Δ (t e, e) = P.Δ e)
    (hφ : ∀ e ∈ P.G.edgeSet, Q.φ (t e, e) = P.φ e) : Simulated Q P := by
  have hE : ∀ p ∈ Q.G.edgeSet, p = (t p.2, p.2) := fun p hp ↦ by
    rw [hG] at hp
    obtain ⟨e, -, rfl⟩ := hp
    rfl
  have hE' : ∀ p ∈ Q.G.edgeSet, p.2 ∈ P.G.edgeSet := fun p hp ↦ by
    rw [hG] at hp
    obtain ⟨e, he, rfl⟩ := hp
    exact he
  refine ⟨_, _, isRealizableExpansion_of_rename (P := Q) (P' := P) Prod.snd ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_⟩
  · rw [hG]
    rfl
  · rw [hG]
    rfl
  · rw [hG]
    ext e
    exact ⟨fun ⟨_, ⟨e', he', hEq⟩, h⟩ ↦ h ▸ hEq ▸ he', fun he ↦ ⟨(t e, e), ⟨e, he, rfl⟩, rfl⟩⟩
  · intro p hp q hq h
    rw [hE p hp, hE q hq, h]
  · intro p hp v
    have h1 : p.1 = t p.2 := congrArg Prod.fst (hE p hp)
    rw [hG]
    exact ⟨fun h ↦ ⟨h1, h⟩, fun h ↦ h.2⟩
  · intro p hp
    rw [hdom]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact he
    · intro h
      exact ⟨p.2, h, (hE p hp).symm⟩
  · intro p hp
    rw [hdom] at hp
    obtain ⟨e, he, rfl⟩ := hp
    exact (hμ e he).symm
  · intro p hp
    rw [hdom] at hp
    obtain ⟨e, he, rfl⟩ := hp
    exact (hΔ e he).symm
  · intro p hp
    rw [hE p hp]
    exact (hφ p.2 (hE' p hp)).symm

/-- The tagged copy of a patchwork is simulated in it. -/
theorem simulated_of_retag {Ω : Type*} [Preorder Ω] (t : β → ℕ) (P : Patchwork Ω α β) :
    Simulated (retagPatchwork t P) P :=
  simulated_of_retag' rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- A patchwork `Q` whose edges are tagged `(t e, e)` simulates any patchwork `P` with the same data
under `e ↦ (t e, e)`. -/
theorem simulated_retag' {Ω : Type*} [Preorder Ω] {t : β → ℕ} {Q : Patchwork Ω α (ℕ × β)}
    {P : Patchwork Ω α β} (hG : Q.G = retagRooted t P.G)
    (hdom : Q.dom = (fun e ↦ (t e, e)) '' P.dom)
    (hμ : ∀ e ∈ P.dom, Q.μ (t e, e) = P.μ e) (hΔ : ∀ e ∈ P.dom, Q.Δ (t e, e) = P.Δ e)
    (hφ : ∀ e ∈ P.G.edgeSet, Q.φ (t e, e) = P.φ e) : Simulated P Q := by
  refine ⟨_, _, isRealizableExpansion_of_rename (P := P) (P' := Q) (fun e ↦ (t e, e)) ?_ ?_ ?_
    (fun _ _ _ _ h ↦ congrArg Prod.snd h) ?_ ?_ hμ hΔ hφ⟩
  · rw [hG]
    rfl
  · rw [hG]
    rfl
  · rw [hG]
    rfl
  · intro e _ v
    rw [hG]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨rfl, h⟩⟩
  · intro e _
    rw [hdom]
    exact ⟨fun h ↦ ⟨e, h, rfl⟩, fun ⟨e', h, hEq⟩ ↦ by
      obtain rfl : e' = e := congrArg Prod.snd hEq
      exact h⟩

theorem IsCompletionOf.retag {Ω Ω' : Type*} {P : Patchwork Ω α β} {Q : Patchwork Ω' α β}
    (h : IsCompletionOf P Q) (t : β → ℕ) :
    IsCompletionOf (retagPatchwork t P) (retagPatchwork t Q) where
  G_eq := by
    change retagRooted t Q.G = retagRooted t P.G
    rw [h.G_eq]
  dom_eq := by
    change (fun e ↦ (t e, e)) '' Q.dom = (fun e ↦ (t e, e)) '' P.dom
    rw [h.dom_eq]
  μ_eq := by
    rintro _ ⟨e, he, rfl⟩
    exact h.μ_eq he
  Δ_eq := by
    rintro _ ⟨e, he, rfl⟩
    exact h.Δ_eq he

/-! ### Well-behaved sets and tags -/

/-- Tagging every edge with `0` keeps a set well-behaved. -/
theorem WellBehaved.retag_zero {𝓕 : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕) :
    WellBehaved (retagPatchwork (fun _ ↦ 0) '' 𝓕) := by
  intro Ω _ hΩ Q hQ
  choose P hP hc using hQ
  choose P₀ hP₀ hPeq using hP
  let R : ℕ → Patchwork Ω α β := fun i ↦ (P₀ i).relabel fun e ↦ (Q i).φ (0, e)
  obtain ⟨i, j, hij, hsim⟩ := h Ω hΩ R fun i ↦ ⟨P₀ i, hP₀ i, isCompletionOf_relabel _ _⟩
  have hc' : ∀ i, IsCompletionOf (retagPatchwork (fun _ ↦ 0) (P₀ i)) (Q i) := fun i ↦
    (hPeq i).symm ▸ hc i
  have h₁ : ∀ i, Simulated (Q i) (R i) := fun i ↦
    simulated_of_retag' (t := fun _ ↦ 0) (hc' i).G_eq (hc' i).dom_eq
      (fun e he ↦ (hc' i).μ_eq ⟨e, he, rfl⟩) (fun e he ↦ (hc' i).Δ_eq ⟨e,
        (P₀ i).dom_subset he, rfl⟩)
      (fun _ _ ↦ rfl)
  have h₂ : ∀ i, Simulated (R i) (Q i) := fun i ↦
    simulated_retag' (t := fun _ ↦ 0) (hc' i).G_eq (hc' i).dom_eq
      (fun e he ↦ (hc' i).μ_eq ⟨e, he, rfl⟩) (fun e he ↦ (hc' i).Δ_eq ⟨e,
        (P₀ i).dom_subset he, rfl⟩)
      (fun _ _ ↦ rfl)
  exact ⟨i, j, hij, ((h₁ i).trans hsim).trans (h₂ j)⟩

/-- If every member of `𝓕` has a tagged copy among the completions of a well-behaved set, then `𝓕`
is
well-behaved. -/
theorem wellBehaved_of_retag {𝓕 : Set (UnlabeledPatchwork α β)}
    {𝓢 : Set (UnlabeledPatchwork α (ℕ × β))} (h : WellBehaved 𝓢)
    (hF : ∀ P ∈ 𝓕, ∃ t : β → ℕ, retagPatchwork t P ∈ completions Unit 𝓢) : WellBehaved 𝓕 := by
  intro Ω _ hΩ Q hQ
  choose P hP hc using hQ
  choose t ht using fun i ↦ hF (P i) (hP i)
  obtain ⟨i, j, hij, hsim⟩ := h Ω hΩ (fun i ↦ retagPatchwork (t i) (Q i)) fun i ↦ by
    obtain ⟨S, hS, hcS⟩ := ht i
    exact ⟨S, hS, hcS.trans ((hc i).retag (t i))⟩
  exact ⟨i, j, hij, ((simulated_retag (t i) (Q i)).trans hsim).trans
    (simulated_of_retag (t j) (Q j))⟩

end GraphMinor.GM20
