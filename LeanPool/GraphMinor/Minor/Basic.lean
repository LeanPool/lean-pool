/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Minor.Model
import Mathlib.Data.Set.Basic

/-!
# Models of minors and basic properties of the minor relation

This file proves the equivalence between the definition of a minor in `GraphMinor/Statement.lean`
(`IsIsoMinor`, by contracting a set of edges of a subgraph) and the description by a model of a
minor in Graph Minors IV, Section 7, conditions (i)–(iv) (pages 242–243, `IsMinorModel` in
`GraphMinor/Minor/Model.lean`), together with the basic properties of `Iso` and `IsIsoMinor`.

## Main results

* `GraphMinor.isIsoMinor_of_isMinorModel`: `MinorModelStatement`, stating that a model of a minor
  gives a minor. We build the subgraph `G'` of `G` with vertex set `⋃ v ∈ V(H), ηv v` and edge set
  consisting of `ηe '' E(H)` together with the edges of the connected subgraphs of condition (iv),
  contract the latter edges, show that the components of the contracted edges are the sets `ηv v`,
  and construct the isomorphism with `H`.
* `GraphMinor.exists_isMinorModel_of_isIsoMinor` (and
  `GraphMinor.exists_isMinorModel_of_isIsoMinor_of_nonempty_or_isEmpty`): conversely, a minor has a
  model, provided that a function `β' → β` exists (for example when `[Nonempty β]` or `[IsEmpty
  β']`;
  without such an assumption `β' → β` is empty when `β` is empty and `β'` is nonempty).
* `GraphMinor.Iso.refl`, `GraphMinor.Iso.symm`, `GraphMinor.Iso.trans`: graph isomorphisms form an
  equivalence relation.
* `GraphMinor.IsIsoMinor.refl`, `GraphMinor.IsIsoMinor.trans`: the minor relation is a quasi-order
  (Graph Minors IV, Section 1, page 228; composition of models follows Graph Minors IV, (7.1),
  page 244).
* `GraphMinor.Iso.isIsoMinor_left`, `GraphMinor.Iso.isIsoMinor_right`,
  `GraphMinor.Iso.isIsoMinor_congr`: `IsIsoMinor` is invariant under isomorphism on both sides.
-/

namespace GraphMinor

open Graph Set Relation

variable {α β α' β' α'' β'' : Type*}

/-- The vertex set of the component of `v` used by `contract`. -/
private abbrev comp (G : Graph α β) (C : Set β) (v : α) : Set α :=
  {w | ReflTransGen (fun x y ↦ ∃ e ∈ C, G.IsLink e x y) v w}

private theorem contract_isLink (G : Graph α β) (C : Set β) (e : β) (X Y : Set α) :
    (contract G C).IsLink e X Y ↔ e ∉ C ∧ ∃ x y, G.IsLink e x y ∧ comp G C x = X ∧
      comp G C y = Y := by
  simp only [contract, deleteEdges_isLink, map_isLink, Relation.Map]
  exact and_comm

private theorem vertexSet_contract (G : Graph α β) (C : Set β) :
    V(contract G C) = comp G C '' V(G) := by
  simp [contract]

private theorem edgeSet_contract (G : Graph α β) (C : Set β) :
    E(contract G C) = E(G) \ C := by
  simp [contract]

private lemma mem_vertexSet_contract {G : Graph α β} {C : Set β} {X : Set α} :
    X ∈ V(contract G C) ↔ ∃ v ∈ V(G), comp G C v = X := by
  simp [contract]

private lemma mem_edgeSet_contract {G : Graph α β} {C : Set β} {e : β} :
    e ∈ E(contract G C) ↔ e ∈ E(G) ∧ e ∉ C := by
  simp [contract]

section ModelToMinor

variable {H : Graph α' β'} {G : Graph α β} {ηv : α' → Set α} {ηe : β' → β}

private noncomputable def chosenK (h : IsMinorModel H G ηv ηe) (v : α') (hv : v ∈ V(H)) :
    Graph α β :=
  (h.connected v hv).choose

private lemma chosenK_le (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H)) :
    chosenK h v hv ≤ G.deleteEdges (ηe '' E(H)) :=
  (h.connected v hv).choose_spec.1

private lemma chosenK_le_G (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H)) :
    chosenK h v hv ≤ G :=
  (chosenK_le h hv).trans deleteEdges_le

private lemma chosenK_vertexSet (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H)) :
    V(chosenK h v hv) = ηv v :=
  (h.connected v hv).choose_spec.2.1

private lemma chosenK_connected (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H)) :
    GraphConnected (chosenK h v hv) :=
  (h.connected v hv).choose_spec.2.2

private noncomputable def modelContractEdges (h : IsMinorModel H G ηv ηe) : Set β :=
  ⋃ (v : α') (hv : v ∈ V(H)), E(chosenK h v hv)

private noncomputable def modelSubgraph (h : IsMinorModel H G ηv ηe) : Graph α β :=
  (G.induce (⋃ v ∈ V(H), ηv v)).restrict (ηe '' E(H) ∪ modelContractEdges h)

private lemma modelSubgraph_le (h : IsMinorModel H G ηv ηe) : modelSubgraph h ≤ G :=
  restrict_le.trans (G.induce_le (iUnion₂_subset h.vertex_subset))

private lemma vertexSet_modelSubgraph (h : IsMinorModel H G ηv ηe) :
    V(modelSubgraph h) = ⋃ v ∈ V(H), ηv v := rfl

private lemma chosenK_edge_ends_mem (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H))
    {e : β} {x y : α} (hl : (chosenK h v hv).IsLink e x y) : x ∈ ηv v ∧ y ∈ ηv v := by
  rw [← chosenK_vertexSet h hv]
  exact ⟨hl.left_mem, hl.right_mem⟩

private lemma modelContractEdges_subset (h : IsMinorModel H G ηv ηe) :
    modelContractEdges h ⊆ E(modelSubgraph h) := by
  rintro e ⟨_, ⟨v, rfl⟩, _, ⟨hv, rfl⟩, he⟩
  obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨hx, hy⟩ := chosenK_edge_ends_mem h hv hl
  have hlG : G.IsLink e x y := hl.mono (chosenK_le_G h hv)
  have hxU : x ∈ ⋃ v ∈ V(H), ηv v := mem_biUnion hv hx
  have hyU : y ∈ ⋃ v ∈ V(H), ηv v := mem_biUnion hv hy
  have heI : e ∈ E(G.induce (⋃ v ∈ V(H), ηv v)) := ⟨x, y, hlG, hxU, hyU⟩
  exact ⟨heI, Or.inr (mem_iUnion₂_of_mem hv he)⟩

private lemma image_edge_subset (h : IsMinorModel H G ηv ηe) :
    ηe '' E(H) ⊆ E(modelSubgraph h) := by
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨u, w, huw⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨x, hx, hincx⟩ := (h.inc_iff u huw.left_mem e he).1 huw.inc_left
  obtain ⟨y, hy⟩ := hincx
  have hxU : x ∈ ⋃ v ∈ V(H), ηv v := mem_biUnion huw.left_mem hx
  have hyU : y ∈ ⋃ v ∈ V(H), ηv v := by
    by_cases hloop : H.IsLoopAt e u
    · have hyu := (h.isLoopAt_iff u huw.left_mem e he).1 hloop y hy.inc_right
      exact mem_biUnion huw.left_mem hyu
    · have huw_ne : u ≠ w := fun h' ↦ hloop (h' ▸ huw)
      obtain ⟨z, hz, hincz⟩ := (h.inc_iff w huw.right_mem e he).1 huw.inc_right
      have hxz : x ≠ z :=
        (h.vertex_disjoint u huw.left_mem w huw.right_mem huw_ne).ne_of_mem hx hz
      have hzy : z = y := hincz.eq_of_isLink_of_ne_left hy hxz.symm
      exact mem_biUnion huw.right_mem (hzy ▸ hz)
  exact ⟨⟨x, y, hy, hxU, hyU⟩, Or.inl (mem_image_of_mem ηe he)⟩

private lemma disjoint_image_modelContractEdges (h : IsMinorModel H G ηv ηe) :
    Disjoint (ηe '' E(H)) (modelContractEdges h) := by
  rw [disjoint_left]
  rintro _ ⟨e, he, rfl⟩ ⟨_, ⟨v, rfl⟩, _, ⟨hv, rfl⟩, heK⟩
  have heD := (chosenK_le h hv).edgeSet_mono heK
  exact heD.2 (mem_image_of_mem ηe he)

private lemma edgeSet_contract_modelSubgraph (h : IsMinorModel H G ηv ηe) :
    E(contract (modelSubgraph h) (modelContractEdges h)) = ηe '' E(H) := by
  rw [edgeSet_contract]
  apply Subset.antisymm
  · rintro e ⟨⟨_, he | he⟩, heC⟩
    · exact he
    · exact absurd he heC
  · intro e he
    exact ⟨image_edge_subset h he,
      (disjoint_image_modelContractEdges h).notMem_of_mem_left he⟩

private lemma comp_modelSubgraph_eq (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H))
    {x : α} (hx : x ∈ ηv v) :
    comp (modelSubgraph h) (modelContractEdges h) x = ηv v := by
  ext y
  simp only [mem_ofPred_eq]
  constructor
  · intro hxy
    induction hxy with
    | refl => exact hx
    | @tail a b _ hab ih =>
      obtain ⟨e, ⟨_, ⟨w, rfl⟩, _, ⟨hw, rfl⟩, heK⟩, hl⟩ := hab
      have hlG : G.IsLink e a b := hl.mono (modelSubgraph_le h)
      have hlK : (chosenK h w hw).IsLink e a b :=
        ((chosenK_le_G h hw).isLink_iff heK).2 hlG
      obtain ⟨ha_w, hb_w⟩ := chosenK_edge_ends_mem h hw hlK
      by_cases hvw : v = w
      · exact hvw ▸ hb_w
      · exact absurd ha_w ((h.vertex_disjoint v hv w hw hvw).notMem_of_mem_left ih)
  · intro hy
    have hconn := (chosenK_connected h hv).2 x (by rwa [chosenK_vertexSet h hv])
      y (by rwa [chosenK_vertexSet h hv])
    induction hconn with
    | refl => exact .refl
    | @tail a b _ hab ih =>
      obtain ⟨e, hlK⟩ := hab
      have heC : e ∈ modelContractEdges h := mem_iUnion₂_of_mem hv hlK.edge_mem
      have hlG : G.IsLink e a b := hlK.mono (chosenK_le_G h hv)
      obtain ⟨ha, hb⟩ := chosenK_edge_ends_mem h hv hlK
      have haU : a ∈ ⋃ u ∈ V(H), ηv u := mem_biUnion hv ha
      have hbU : b ∈ ⋃ u ∈ V(H), ηv u := mem_biUnion hv hb
      exact (ih ha).tail ⟨e, heC, Or.inr heC, hlG, haU, hbU⟩

private lemma vertexSet_contract_modelSubgraph (h : IsMinorModel H G ηv ηe) :
    V(contract (modelSubgraph h) (modelContractEdges h)) = ηv '' V(H) := by
  rw [vertexSet_contract, vertexSet_modelSubgraph]
  ext X
  simp only [mem_image, mem_iUnion]
  constructor
  · rintro ⟨x, ⟨v, hv, hx⟩, rfl⟩
    exact ⟨v, hv, (comp_modelSubgraph_eq h hv hx).symm⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨x, hx⟩ := h.vertex_nonempty v hv
    exact ⟨x, ⟨v, hv, hx⟩, comp_modelSubgraph_eq h hv hx⟩

private lemma ηv_injOn (h : IsMinorModel H G ηv ηe) : InjOn ηv V(H) := by
  intro v₁ hv₁ v₂ hv₂ heq
  by_contra hne
  obtain ⟨x, hx⟩ := h.vertex_nonempty v₁ hv₁
  exact (h.vertex_disjoint v₁ hv₁ v₂ hv₂ hne).notMem_of_mem_left hx (heq ▸ hx)

private lemma contract_modelSubgraph_isLink_iff (h : IsMinorModel H G ηv ηe)
    {e : β'} (he : e ∈ E(H)) {u w : α'} (hu : u ∈ V(H)) (hw : w ∈ V(H)) :
    H.IsLink e u w ↔
      (contract (modelSubgraph h) (modelContractEdges h)).IsLink (ηe e) (ηv u) (ηv w) := by
  rw [contract_isLink]
  constructor
  · intro hl
    have heC : ηe e ∉ modelContractEdges h :=
      (disjoint_image_modelContractEdges h).notMem_of_mem_left (mem_image_of_mem ηe he)
    refine ⟨heC, ?_⟩
    obtain ⟨x, hx, hincx⟩ := (h.inc_iff u hu e he).1 hl.inc_left
    obtain ⟨y, hy⟩ := hincx
    have hxU : x ∈ ⋃ v ∈ V(H), ηv v := mem_biUnion hu hx
    by_cases hloop : H.IsLoopAt e u
    · have huw : u = w := hloop.eq_of_inc hl.inc_right
      subst huw
      have hy_u : y ∈ ηv u := (h.isLoopAt_iff u hu e he).1 hloop y hy.inc_right
      have hyU : y ∈ ⋃ v ∈ V(H), ηv v := mem_biUnion hu hy_u
      have hlM : (modelSubgraph h).IsLink (ηe e) x y :=
        ⟨Or.inl (mem_image_of_mem ηe he), hy, hxU, hyU⟩
      exact ⟨x, y, hlM, comp_modelSubgraph_eq h hu hx, comp_modelSubgraph_eq h hu hy_u⟩
    · have huw_ne : u ≠ w := fun h' ↦ hloop (h' ▸ hl)
      obtain ⟨z, hz, hincz⟩ := (h.inc_iff w hw e he).1 hl.inc_right
      have hxz : x ≠ z := (h.vertex_disjoint u hu w hw huw_ne).ne_of_mem hx hz
      have hzy : z = y := hincz.eq_of_isLink_of_ne_left hy hxz.symm
      have hy_w : y ∈ ηv w := hzy ▸ hz
      have hyU : y ∈ ⋃ v ∈ V(H), ηv v := mem_biUnion hw hy_w
      have hlM : (modelSubgraph h).IsLink (ηe e) x y :=
        ⟨Or.inl (mem_image_of_mem ηe he), hy, hxU, hyU⟩
      exact ⟨x, y, hlM, comp_modelSubgraph_eq h hu hx, comp_modelSubgraph_eq h hw hy_w⟩
  · rintro ⟨_, x, y, hlM, hcx, hcy⟩
    have hlG : G.IsLink (ηe e) x y := hlM.mono (modelSubgraph_le h)
    obtain ⟨v₁, hv₁, hx₁⟩ := mem_iUnion₂.1 hlM.left_mem
    obtain ⟨v₂, hv₂, hy₂⟩ := mem_iUnion₂.1 hlM.right_mem
    have hvu : v₁ = u :=
      ηv_injOn h hv₁ hu ((comp_modelSubgraph_eq h hv₁ hx₁).symm.trans hcx)
    have hvw : v₂ = w :=
      ηv_injOn h hv₂ hw ((comp_modelSubgraph_eq h hv₂ hy₂).symm.trans hcy)
    have hx_u : x ∈ ηv u := hvu ▸ hx₁
    have hy_w : y ∈ ηv w := hvw ▸ hy₂
    have hinc_u : H.Inc e u := (h.inc_iff u hu e he).2 ⟨x, hx_u, hlG.inc_left⟩
    have hinc_w : H.Inc e w := (h.inc_iff w hw e he).2 ⟨y, hy_w, hlG.inc_right⟩
    rw [isLink_iff_inc]
    refine ⟨hinc_u, hinc_w, fun z hz ↦ ?_⟩
    obtain ⟨a, ha_z, hinc_a⟩ := (h.inc_iff z hz.vertex_mem e he).1 hz
    obtain rfl | rfl := hinc_a.eq_or_eq_of_isLink hlG
    · left
      by_contra hzu
      exact (h.vertex_disjoint z hz.vertex_mem u hu hzu).notMem_of_mem_left ha_z hx_u
    · right
      by_contra hzw
      exact (h.vertex_disjoint z hz.vertex_mem w hw hzw).notMem_of_mem_left ha_z hy_w

private theorem isIsoMinor_of_isMinorModel_uncond {H : Graph α' β'} {G : Graph α β}
    {ηv : α' → Set α} {ηe : β' → β} (h : IsMinorModel H G ηv ηe) : IsIsoMinor H G := by
  refine ⟨modelSubgraph h, modelSubgraph_le h, modelContractEdges h,
    modelContractEdges_subset h, ⟨?_⟩⟩
  refine
    { vertexEquiv :=
        (Equiv.Set.imageOfInjOn ηv V(H) (ηv_injOn h)).trans
          (Equiv.subtypeEquivRight fun _ ↦ by rw [vertexSet_contract_modelSubgraph])
      edgeEquiv :=
        (Equiv.Set.imageOfInjOn ηe E(H) h.edge_injOn).trans
          (Equiv.subtypeEquivRight fun _ ↦ by rw [edgeSet_contract_modelSubgraph])
      isLink_iff := fun ⟨e, he⟩ ⟨u, hu⟩ ⟨w, hw⟩ ↦
        contract_modelSubgraph_isLink_iff h he hu hw }

end ModelToMinor

section MinorToModel

private lemma comp_self (G : Graph α β) (C : Set β) (v : α) : v ∈ comp G C v :=
  ReflTransGen.refl

private lemma comp_subset_vertexSet (G : Graph α β) (C : Set β) {v : α} (hv : v ∈ V(G)) :
    comp G C v ⊆ V(G) := by
  intro w hw
  induction hw with
  | refl => exact hv
  | tail _ hst _ =>
    obtain ⟨_, _, hl⟩ := hst
    exact hl.right_mem

private lemma comp_eq_of_mem (G : Graph α β) (C : Set β) {v w : α} (hw : w ∈ comp G C v) :
    comp G C v = comp G C w := by
  ext z
  simp only [mem_ofPred_eq]
  have hsymm : ∀ a b, ReflTransGen (fun x y ↦ ∃ e ∈ C, G.IsLink e x y) a b →
      ReflTransGen (fun x y ↦ ∃ e ∈ C, G.IsLink e x y) b a := by
    intro a b hab
    induction hab with
    | refl => exact .refl
    | tail _ hst ih =>
      obtain ⟨e, he, hl⟩ := hst
      exact ReflTransGen.head ⟨e, he, hl.symm⟩ ih
  exact ⟨fun hvz ↦ (hsymm _ _ hw).trans hvz, fun hwz ↦ hw.trans hwz⟩

private lemma comp_connected (G' : Graph α β) (C : Set β) {X : Set α}
    (hX : X ∈ V(contract G' C)) :
    GraphConnected ((G'.restrict C).induce X) := by
  rw [vertexSet_contract] at hX
  obtain ⟨v₀, hv₀, rfl⟩ := hX
  refine ⟨⟨v₀, comp_self G' C v₀⟩, fun x hx y hy ↦ ?_⟩
  have hvx : comp G' C v₀ = comp G' C x := comp_eq_of_mem G' C hx
  have hxy : y ∈ comp G' C x := hvx ▸ hy
  induction hxy with
  | refl => exact .refl
  | @tail a b hab hst ih =>
    have ha : a ∈ comp G' C v₀ := hvx.symm ▸ hab
    have hb : b ∈ comp G' C v₀ := hvx.symm ▸ (hab.tail hst)
    obtain ⟨e, heC, hl⟩ := hst
    exact (ih ha).tail ⟨e, ⟨heC, hl⟩, ha, hb⟩

private theorem exists_isMinorModel_of_isIsoMinor_aux {H : Graph α' β'} {G : Graph α β}
    (hβ : Nonempty β ∨ IsEmpty β') (h : IsIsoMinor H G) :
    ∃ (ηv : α' → Set α) (ηe : β' → β), IsMinorModel H G ηv ηe := by
  classical
  obtain ⟨G', hle, C, _, ⟨φ⟩⟩ := h
  let ηv : α' → Set α := fun v ↦ if hv : v ∈ V(H) then (φ.vertexEquiv ⟨v, hv⟩ : Set α) else ∅
  have hηe_ex : ∃ ηe : β' → β, ∀ e (he : e ∈ E(H)), ηe e = (φ.edgeEquiv ⟨e, he⟩ : β) := by
    rcases hβ with hne | hEmpty
    · obtain ⟨b₀⟩ := hne
      exact ⟨fun e ↦ if he : e ∈ E(H) then (φ.edgeEquiv ⟨e, he⟩ : β) else b₀,
        fun e he ↦ dite_eq_left he⟩
    · exact ⟨isEmptyElim, fun e ↦ hEmpty.elim e⟩
  obtain ⟨ηe, hηe⟩ := hηe_ex
  have hηv : ∀ v (hv : v ∈ V(H)), ηv v = (φ.vertexEquiv ⟨v, hv⟩ : Set α) :=
    fun v hv ↦ dite_eq_left hv
  have hηv_comp : ∀ v (hv : v ∈ V(H)), ∃ x ∈ V(G'), comp G' C x = ηv v := by
    intro v hv
    rw [hηv v hv]
    exact mem_vertexSet_contract.1 (φ.vertexEquiv ⟨v, hv⟩).2
  have hηv_comp_of_mem : ∀ v (hv : v ∈ V(H)) {x : α}, x ∈ ηv v → comp G' C x = ηv v := by
    intro v hv x hx
    obtain ⟨a, _, hca⟩ := hηv_comp v hv
    exact (comp_eq_of_mem G' C (hca.symm ▸ hx)).symm.trans hca
  have hηe_mem : ∀ e (he : e ∈ E(H)), ηe e ∈ E(G') ∧ ηe e ∉ C := by
    intro e he
    rw [hηe e he]
    exact mem_edgeSet_contract.1 (φ.edgeEquiv ⟨e, he⟩).2
  refine ⟨ηv, ηe, ?_⟩
  refine
    { vertex_nonempty := fun v hv ↦ by
        obtain ⟨x, _, hcx⟩ := hηv_comp v hv
        exact ⟨x, hcx ▸ comp_self G' C x⟩
      vertex_subset := fun v hv ↦ by
        obtain ⟨x, hx, hcx⟩ := hηv_comp v hv
        exact hcx ▸ (comp_subset_vertexSet G' C hx).trans hle.vertexSet_mono
      edge_mem := fun e he ↦ hle.edgeSet_mono (hηe_mem e he).1
      vertex_disjoint := fun v₁ hv₁ v₂ hv₂ hne ↦ by
        rw [disjoint_left]
        intro x hx₁ hx₂
        have heq : (φ.vertexEquiv ⟨v₁, hv₁⟩ : Set α) = (φ.vertexEquiv ⟨v₂, hv₂⟩ : Set α) := by
          rw [← hηv v₁ hv₁, ← hηv v₂ hv₂, ← hηv_comp_of_mem v₁ hv₁ hx₁,
            ← hηv_comp_of_mem v₂ hv₂ hx₂]
        have := φ.vertexEquiv.injective (Subtype.ext heq)
        exact hne (Subtype.mk.inj this)
      edge_injOn := fun e₁ he₁ e₂ he₂ heq ↦ by
        rw [hηe e₁ he₁, hηe e₂ he₂] at heq
        have := φ.edgeEquiv.injective (Subtype.ext heq)
        exact Subtype.mk.inj this
      inc_iff := fun v hv e he ↦ by
        constructor
        · rintro ⟨w, hl⟩
          have hw : w ∈ V(H) := hl.right_mem
          have hlc := (φ.isLink_iff ⟨e, he⟩ ⟨v, hv⟩ ⟨w, hw⟩).1 hl
          rw [contract_isLink] at hlc
          obtain ⟨_, x, y, hlG', hcx, _⟩ := hlc
          rw [hηv v hv, hηe e he]
          exact ⟨x, hcx ▸ comp_self G' C x, (hlG'.mono hle).inc_left⟩
        · rintro ⟨x, hx, y, hlG⟩
          have heG' := hηe_mem e he
          have hlG' : G'.IsLink (ηe e) x y := (hle.isLink_iff heG'.1).2 hlG
          have hcx : comp G' C x = (φ.vertexEquiv ⟨v, hv⟩ : Set α) := by
            rw [← hηv v hv, hηv_comp_of_mem v hv hx]
          have hcy_mem : comp G' C y ∈ V(contract G' C) :=
            mem_vertexSet_contract.2 ⟨y, hlG'.right_mem, rfl⟩
          obtain ⟨⟨w, hw⟩, hcw⟩ := φ.vertexEquiv.surjective ⟨comp G' C y, hcy_mem⟩
          have hcy : comp G' C y = (φ.vertexEquiv ⟨w, hw⟩ : Set α) :=
            (congrArg Subtype.val hcw).symm
          have hlc : (contract G' C).IsLink (φ.edgeEquiv ⟨e, he⟩)
              (φ.vertexEquiv ⟨v, hv⟩) (φ.vertexEquiv ⟨w, hw⟩) := by
            rw [contract_isLink, ← hηe e he]
            exact ⟨heG'.2, x, y, hlG', hcx, hcy⟩
          exact ⟨w, (φ.isLink_iff ⟨e, he⟩ ⟨v, hv⟩ ⟨w, hw⟩).2 hlc⟩
      isLoopAt_iff := fun v hv e he ↦ by
        constructor
        · intro hloop x hinc
          have hlc := (φ.isLink_iff ⟨e, he⟩ ⟨v, hv⟩ ⟨v, hv⟩).1 hloop
          rw [contract_isLink] at hlc
          obtain ⟨_, a, b, hlG', hca, hcb⟩ := hlc
          have hlG : G.IsLink (ηe e) a b := by
            rw [hηe e he]
            exact hlG'.mono hle
          rw [hηv v hv]
          obtain rfl | rfl := hinc.eq_or_eq_of_isLink hlG
          · exact hca ▸ comp_self G' C x
          · exact hcb ▸ comp_self G' C x
        · intro hall
          have heG' := hηe_mem e he
          obtain ⟨a, b, hlG'⟩ := exists_isLink_of_mem_edgeSet heG'.1
          have hlG : G.IsLink (ηe e) a b := hlG'.mono hle
          have ha_v : a ∈ ηv v := hall a hlG.inc_left
          have hb_v : b ∈ ηv v := hall b hlG.inc_right
          have hca : comp G' C a = (φ.vertexEquiv ⟨v, hv⟩ : Set α) := by
            rw [← hηv v hv, hηv_comp_of_mem v hv ha_v]
          have hcb : comp G' C b = (φ.vertexEquiv ⟨v, hv⟩ : Set α) := by
            rw [← hηv v hv, hηv_comp_of_mem v hv hb_v]
          have hlc : (contract G' C).IsLink (φ.edgeEquiv ⟨e, he⟩)
              (φ.vertexEquiv ⟨v, hv⟩) (φ.vertexEquiv ⟨v, hv⟩) := by
            rw [contract_isLink, ← hηe e he]
            exact ⟨heG'.2, a, b, hlG', hca, hcb⟩
          exact (φ.isLink_iff ⟨e, he⟩ ⟨v, hv⟩ ⟨v, hv⟩).2 hlc
      connected := fun v hv ↦ by
        have hmem_v : ηv v ∈ V(contract G' C) := by
          rw [hηv v hv]
          exact (φ.vertexEquiv ⟨v, hv⟩).2
        refine ⟨(G'.restrict C).induce (ηv v), ?_, rfl, comp_connected G' C hmem_v⟩
        obtain ⟨x₀, hx₀, hcx₀⟩ := hηv_comp v hv
        have hsub : ηv v ⊆ V(G'.restrict C) := hcx₀ ▸ comp_subset_vertexSet G' C hx₀
        refine (induce_le hsub).trans ?_
        refine ⟨hle.vertexSet_mono, fun e x y ⟨heC, hlG'⟩ ↦ ⟨hlG'.mono hle, ?_⟩⟩
        rintro ⟨e', he', heq⟩
        exact (hηe_mem e' he').2 (heq ▸ heC) }

end MinorToModel

section BasicProperties

private theorem comp_empty (G : Graph α β) (v : α) : comp G ∅ v = {v} := by
  ext w
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ h _ => simp at h
  · rintro rfl
    exact .refl

private lemma isIsoMinor_of_edgeSet_eq_empty {H : Graph α'' β''} {G : Graph α β}
    {K : Graph α' β'} (hEK : E(K) = ∅) (hHK : IsIsoMinor H K) (hKG : IsIsoMinor K G) :
    IsIsoMinor H G := by
  obtain ⟨G₁, hle₁, C₁, hC₁_sub, ⟨φ₁⟩⟩ := hHK
  obtain ⟨G₂, hle₂, C₂, _, ⟨φ₂⟩⟩ := hKG
  have hE_G₁ : E(G₁) = ∅ := subset_empty_iff.1 (hEK ▸ hle₁.edgeSet_mono)
  have hC₁ : C₁ = ∅ := subset_empty_iff.1 (hE_G₁ ▸ hC₁_sub)
  have hE_H : E(H) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro e he
    have hmem := mem_edgeSet_contract.1 (φ₁.edgeEquiv ⟨e, he⟩).2
    rw [hE_G₁] at hmem
    exact hmem.1
  have hinj₁ : Function.Injective (comp G₁ ∅) := fun x y h ↦ by simpa [comp_empty] using h
  have eV₁ : V(H) ≃ V(G₁) :=
    φ₁.vertexEquiv.trans
      ((Equiv.subtypeEquivRight fun _ ↦ by rw [hC₁, vertexSet_contract]).trans
        (Equiv.Set.image _ _ hinj₁).symm)
  have hsub₁ : V(G₁) ⊆ V(K) := hle₁.vertexSet_mono
  let emb₁ : V(H) → V(K) := Set.inclusion hsub₁ ∘ eV₁
  have hemb₁_inj : Function.Injective emb₁ :=
    (Set.inclusion_injective hsub₁).comp eV₁.injective
  have hrep : ∀ x : V(K), ∃ w ∈ V(G₂), w ∈ (φ₂.vertexEquiv x : Set α) := by
    intro x
    obtain ⟨w, hw, hcw⟩ := mem_vertexSet_contract.1 (φ₂.vertexEquiv x).2
    exact ⟨w, hw, hcw ▸ comp_self G₂ C₂ w⟩
  choose rep hrep_mem hrep_in using hrep
  have hrep_inj : Function.Injective rep := by
    intro x y hxy
    have hx := hrep_in x
    have hy := hxy ▸ hrep_in y
    obtain ⟨a₁, _, hc₁⟩ := mem_vertexSet_contract.1 (φ₂.vertexEquiv x).2
    obtain ⟨a₂, _, hc₂⟩ := mem_vertexSet_contract.1 (φ₂.vertexEquiv y).2
    have heq₁ : (φ₂.vertexEquiv x : Set α) = comp G₂ C₂ (rep x) :=
      hc₁.symm.trans (comp_eq_of_mem G₂ C₂ (hc₁.symm ▸ hx))
    have heq₂ : (φ₂.vertexEquiv y : Set α) = comp G₂ C₂ (rep x) :=
      hc₂.symm.trans (comp_eq_of_mem G₂ C₂ (hc₂.symm ▸ hy))
    exact φ₂.vertexEquiv.injective (Subtype.ext (heq₁.trans heq₂.symm))
  let f : V(H) → α := fun u ↦ rep (emb₁ u)
  have hf_inj : Function.Injective f := hrep_inj.comp hemb₁_inj
  let G' : Graph α β := Graph.noEdge (range f) β
  have hG'_le : G' ≤ G := by
    rw [noEdge_le_iff]
    rintro _ ⟨u, rfl⟩
    exact hle₂.vertexSet_mono (hrep_mem (emb₁ u))
  refine ⟨G', hG'_le, ∅, empty_subset _, ⟨?_⟩⟩
  have hinj' : Function.Injective (comp G' ∅) := fun x y h ↦ by simpa [comp_empty] using h
  have eV' : V(H) ≃ V(contract G' ∅) :=
    (Equiv.ofInjective f hf_inj).trans
      ((Equiv.Set.image (comp G' ∅) (range f) hinj').trans
        (Equiv.subtypeEquivRight fun _ ↦ by rw [vertexSet_contract, vertexSet_noEdge]))
  have eE' : E(H) ≃ E(contract G' ∅) :=
    { toFun := fun ⟨e, he⟩ ↦ absurd he (by simp [hE_H])
      invFun := fun ⟨e, he⟩ ↦ absurd he (by simp [G', edgeSet_contract])
      left_inv := fun ⟨e, he⟩ ↦ absurd he (by simp [hE_H])
      right_inv := fun ⟨e, he⟩ ↦ absurd he (by simp [G', edgeSet_contract]) }
  refine
    { vertexEquiv := eV'
      edgeEquiv := eE'
      isLink_iff := fun ⟨e, he⟩ _ _ ↦ absurd he (by simp [hE_H]) }

private lemma isMinorModel_comp {H : Graph α'' β''} {K : Graph α' β'} {G : Graph α β}
    {ηv : α'' → Set α'} {ηe : β'' → β'} {ηv' : α' → Set α} {ηe' : β' → β}
    (h₁ : IsMinorModel H K ηv ηe) (h₂ : IsMinorModel K G ηv' ηe') :
    IsMinorModel H G (fun v ↦ ⋃ v' ∈ ηv v, ηv' v') (ηe' ∘ ηe) where
  vertex_nonempty v hv := by
    obtain ⟨v', hv'⟩ := h₁.vertex_nonempty v hv
    obtain ⟨x, hx⟩ := h₂.vertex_nonempty v' (h₁.vertex_subset v hv hv')
    exact ⟨x, mem_biUnion hv' hx⟩
  vertex_subset v hv := by
    rintro x ⟨_, ⟨v', rfl⟩, _, ⟨hv', rfl⟩, hx⟩
    exact h₂.vertex_subset v' (h₁.vertex_subset v hv hv') hx
  edge_mem e he := h₂.edge_mem (ηe e) (h₁.edge_mem e he)
  vertex_disjoint v₁ hv₁ v₂ hv₂ hne := by
    rw [disjoint_left]
    rintro x ⟨_, ⟨u₁, rfl⟩, _, ⟨hu₁, rfl⟩, hx₁⟩ ⟨_, ⟨u₂, rfl⟩, _, ⟨hu₂, rfl⟩, hx₂⟩
    have hu₁K := h₁.vertex_subset v₁ hv₁ hu₁
    have hu₂K := h₁.vertex_subset v₂ hv₂ hu₂
    have hu_eq : u₁ = u₂ := by
      by_contra hne'
      exact (h₂.vertex_disjoint u₁ hu₁K u₂ hu₂K hne').notMem_of_mem_left hx₁ hx₂
    exact (h₁.vertex_disjoint v₁ hv₁ v₂ hv₂ hne).notMem_of_mem_left hu₁ (hu_eq ▸ hu₂)
  edge_injOn := h₂.edge_injOn.comp h₁.edge_injOn (mapsTo_iff_subset_preimage.2 h₁.edge_mem)
  inc_iff v hv e he := by
    rw [h₁.inc_iff v hv e he]
    constructor
    · rintro ⟨v', hv', hinc'⟩
      have hv'K := h₁.vertex_subset v hv hv'
      obtain ⟨x, hx, hinc⟩ := (h₂.inc_iff v' hv'K (ηe e) (h₁.edge_mem e he)).1 hinc'
      exact ⟨x, mem_biUnion hv' hx, hinc⟩
    · rintro ⟨x, ⟨_, ⟨v', rfl⟩, _, ⟨hv', rfl⟩, hx⟩, hinc⟩
      have hv'K := h₁.vertex_subset v hv hv'
      exact ⟨v', hv', (h₂.inc_iff v' hv'K (ηe e) (h₁.edge_mem e he)).2 ⟨x, hx, hinc⟩⟩
  isLoopAt_iff v hv e he := by
    rw [h₁.isLoopAt_iff v hv e he]
    have heK := h₁.edge_mem e he
    constructor
    · intro hall x hinc
      obtain ⟨a, b, hlK⟩ := exists_isLink_of_mem_edgeSet heK
      have ha_v : a ∈ ηv v := hall a hlK.inc_left
      have hb_v : b ∈ ηv v := hall b hlK.inc_right
      by_cases hloop' : K.IsLoopAt (ηe e) a
      · have hx_a := (h₂.isLoopAt_iff a hlK.left_mem (ηe e) heK).1 hloop' x hinc
        exact mem_biUnion ha_v hx_a
      · have hab_ne : a ≠ b := fun h' ↦ hloop' (h' ▸ hlK)
        obtain ⟨x₁, hx₁, y₁, hlG₁⟩ := (h₂.inc_iff a hlK.left_mem (ηe e) heK).1 hlK.inc_left
        obtain ⟨x₂, hx₂, hinc₂⟩ := (h₂.inc_iff b hlK.right_mem (ηe e) heK).1 hlK.inc_right
        have hx₁x₂ : x₁ ≠ x₂ :=
          (h₂.vertex_disjoint a hlK.left_mem b hlK.right_mem hab_ne).ne_of_mem hx₁ hx₂
        have hx₂y₁ : x₂ = y₁ := hinc₂.eq_of_isLink_of_ne_left hlG₁ hx₁x₂.symm
        obtain rfl | rfl := hinc.eq_or_eq_of_isLink hlG₁
        · exact mem_biUnion ha_v hx₁
        · exact mem_biUnion hb_v (hx₂y₁ ▸ hx₂)
    · intro hall v' hinc'
      have hv'K := hinc'.vertex_mem
      obtain ⟨x, hx, hinc⟩ := (h₂.inc_iff v' hv'K (ηe e) heK).1 hinc'
      obtain ⟨_, ⟨u, rfl⟩, _, ⟨hu, rfl⟩, hxu⟩ := hall x hinc
      have huK := h₁.vertex_subset v hv hu
      have huv' : u = v' := by
        by_contra hne
        exact (h₂.vertex_disjoint u huK v' hv'K hne).notMem_of_mem_left hxu hx
      exact huv' ▸ hu
  connected v hv := by
    obtain ⟨K₁, hK₁_le, hK₁_V, hK₁_conn⟩ := h₁.connected v hv
    let F₂ : Set β := (ηe' '' E(K₁)) ∪
      ⋃ (v' : α') (hv' : v' ∈ ηv v), E(chosenK h₂ v' (h₁.vertex_subset v hv hv'))
    let K₂ : Graph α β := (G.induce (⋃ v' ∈ ηv v, ηv' v')).restrict F₂
    refine ⟨K₂, ?_, rfl, ?_⟩
    · refine ⟨?_, fun e x y ⟨heF₂, hlG, _, _⟩ ↦ ⟨hlG, ?_⟩⟩
      · rintro x ⟨_, ⟨v', rfl⟩, _, ⟨hv', rfl⟩, hx⟩
        exact h₂.vertex_subset v' (h₁.vertex_subset v hv hv') hx
      · rintro ⟨e₀, he₀, rfl⟩
        rcases heF₂ with ⟨e₁, he₁, heq⟩ | ⟨_, ⟨v', rfl⟩, _, ⟨hv', rfl⟩, heK⟩
        · have he₁_mem : e₁ ∈ E(K) := (hK₁_le.trans deleteEdges_le).edgeSet_mono he₁
          have := h₂.edge_injOn he₁_mem (h₁.edge_mem e₀ he₀) heq
          exact (hK₁_le.edgeSet_mono he₁).2 (this ▸ mem_image_of_mem ηe he₀)
        · have heD := (chosenK_le h₂ (h₁.vertex_subset v hv hv')).edgeSet_mono heK
          exact heD.2 (mem_image_of_mem ηe' (h₁.edge_mem e₀ he₀))
    · have hinner : ∀ {v' : α'} (hv' : v' ∈ ηv v) {x y : α},
          x ∈ ηv' v' → y ∈ ηv' v' → ReflTransGen K₂.Adj x y := by
        intro v' hv' x y hx hy
        have hv'K := h₁.vertex_subset v hv hv'
        have hconn := (chosenK_connected h₂ hv'K).2 x (by rwa [chosenK_vertexSet h₂ hv'K])
          y (by rwa [chosenK_vertexSet h₂ hv'K])
        induction hconn with
        | refl => exact .refl
        | @tail a b _ hab ih =>
          obtain ⟨e, hlK⟩ := hab
          have heF₂ : e ∈ F₂ := Or.inr (mem_iUnion₂_of_mem hv' hlK.edge_mem)
          have hlG : G.IsLink e a b := hlK.mono (chosenK_le_G h₂ hv'K)
          obtain ⟨ha, hb⟩ := chosenK_edge_ends_mem h₂ hv'K hlK
          have haU : a ∈ ⋃ u ∈ ηv v, ηv' u := mem_biUnion hv' ha
          have hbU : b ∈ ⋃ u ∈ ηv v, ηv' u := mem_biUnion hv' hb
          exact (ih ha).tail ⟨e, heF₂, hlG, haU, hbU⟩
      obtain ⟨v₀', hv₀'⟩ := h₁.vertex_nonempty v hv
      obtain ⟨x₀, hx₀⟩ := h₂.vertex_nonempty v₀' (h₁.vertex_subset v hv hv₀')
      refine ⟨⟨x₀, mem_biUnion hv₀' hx₀⟩, ?_⟩
      rintro x ⟨_, ⟨u, rfl⟩, _, ⟨hu, rfl⟩, hxu⟩ y ⟨_, ⟨w, rfl⟩, _, ⟨hw, rfl⟩, hyw⟩
      have hwalk := hK₁_conn.2 u (hK₁_V.symm ▸ hu) w (hK₁_V.symm ▸ hw)
      have hstep : ∀ {p q : α'}, ReflTransGen K₁.Adj p q → p ∈ ηv v → q ∈ ηv v →
          ∀ {a b : α}, a ∈ ηv' p → b ∈ ηv' q → ReflTransGen K₂.Adj a b := by
        intro p q hpq
        induction hpq with
        | refl => exact fun hp _ a b ha hb ↦ hinner hp ha hb
        | @tail c d _ hcd ih =>
          intro hp hd a b ha hb
          obtain ⟨e₁, hlK₁⟩ := hcd
          have hc : c ∈ ηv v := hK₁_V ▸ hlK₁.left_mem
          have hlK : K.IsLink e₁ c d := (hlK₁.mono hK₁_le).1
          obtain ⟨c', hc', hincc'⟩ := (h₂.inc_iff c (h₁.vertex_subset v hv hc) e₁ hlK.edge_mem).1
            hlK.inc_left
          obtain ⟨d', hlG'⟩ := hincc'
          have hd' : d' ∈ ηv' d := by
            by_cases hloop : K.IsLoopAt e₁ c
            · have hcd_eq : c = d := hloop.eq_of_inc hlK.inc_right
              exact hcd_eq ▸
                (h₂.isLoopAt_iff c (h₁.vertex_subset v hv hc) e₁ hlK.edge_mem).1 hloop d'
                  hlG'.inc_right
            · have hcd_ne : c ≠ d := fun h' ↦ hloop (h' ▸ hlK)
              obtain ⟨z, hz, hincz⟩ :=
                (h₂.inc_iff d (h₁.vertex_subset v hv hd) e₁ hlK.edge_mem).1 hlK.inc_right
              have hc'z : c' ≠ z :=
                (h₂.vertex_disjoint c (h₁.vertex_subset v hv hc) d
                  (h₁.vertex_subset v hv hd) hcd_ne).ne_of_mem hc' hz
              have hzd' : z = d' := hincz.eq_of_isLink_of_ne_left hlG' hc'z.symm
              exact hzd' ▸ hz
          have heF₂ : ηe' e₁ ∈ F₂ := Or.inl (mem_image_of_mem ηe' hlK₁.edge_mem)
          have hc'U : c' ∈ ⋃ u ∈ ηv v, ηv' u := mem_biUnion hc hc'
          have hd'U : d' ∈ ⋃ u ∈ ηv v, ηv' u := mem_biUnion hd hd'
          have hadj : K₂.Adj c' d' := ⟨ηe' e₁, heF₂, hlG', hc'U, hd'U⟩
          exact ((ih hp hc ha hc').tail hadj).trans (hinner hd hd' hb)
      exact hstep hwalk hu hw hxu hyw

end BasicProperties

public section

/-- A model of a minor gives a minor (Graph Minors IV, Section 7, pages 242–243). -/
theorem isIsoMinor_of_isMinorModel : MinorModelStatement :=
  fun _ _ _ _ _ _ _ _ h ↦ isIsoMinor_of_isMinorModel_uncond h

/-- A minor has a model when the ambient edge type of `G` is nonempty or the edge type of `H` is
empty (so that a function `β' → β` exists). -/
theorem exists_isMinorModel_of_isIsoMinor_of_nonempty_or_isEmpty {α β α' β' : Type*}
    {H : Graph α' β'} {G : Graph α β} (_hV : V(G).Finite) (_hE : E(G).Finite)
    (hβ : Nonempty β ∨ IsEmpty β') (h : IsIsoMinor H G) :
    ∃ (ηv : α' → Set α) (ηe : β' → β), IsMinorModel H G ηv ηe :=
  exists_isMinorModel_of_isIsoMinor_aux hβ h

/-- A minor has a model (Graph Minors IV, Section 7, pages 242–243). -/
theorem exists_isMinorModel_of_isIsoMinor {α β α' β' : Type*} [Nonempty β]
    {H : Graph α' β'} {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (h : IsIsoMinor H G) :
    ∃ (ηv : α' → Set α) (ηe : β' → β), IsMinorModel H G ηv ηe :=
  exists_isMinorModel_of_isIsoMinor_of_nonempty_or_isEmpty hV hE (Or.inl ‹_›) h

/-- The identity isomorphism of a graph. -/
def Iso.refl (G : Graph α β) : Iso G G where
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  isLink_iff _ _ _ := Iff.rfl

/-- The inverse of a graph isomorphism. -/
def Iso.symm {H : Graph α' β'} {G : Graph α β} (φ : Iso H G) : Iso G H where
  vertexEquiv := φ.vertexEquiv.symm
  edgeEquiv := φ.edgeEquiv.symm
  isLink_iff e x y := by
    have h := φ.isLink_iff (φ.edgeEquiv.symm e) (φ.vertexEquiv.symm x) (φ.vertexEquiv.symm y)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm

/-- The composition of two graph isomorphisms. -/
def Iso.trans {H : Graph α'' β''} {K : Graph α' β'} {G : Graph α β}
    (φ : Iso H K) (ψ : Iso K G) : Iso H G where
  vertexEquiv := φ.vertexEquiv.trans ψ.vertexEquiv
  edgeEquiv := φ.edgeEquiv.trans ψ.edgeEquiv
  isLink_iff e x y := (φ.isLink_iff e x y).trans (ψ.isLink_iff _ _ _)

/-- Every graph is isomorphic to a minor of itself (Graph Minors IV, Section 1, page 228). -/
theorem IsIsoMinor.refl (G : Graph α β) : IsIsoMinor G G := by
  refine ⟨G, le_rfl, ∅, empty_subset _, ⟨?_⟩⟩
  have hinj : Function.Injective (comp G ∅) := fun x y h ↦ by simpa [comp_empty] using h
  refine
    { vertexEquiv :=
        (Equiv.Set.image _ _ hinj).trans
          (Equiv.subtypeEquivRight fun _ ↦ by rw [vertexSet_contract])
      edgeEquiv := Equiv.subtypeEquivRight fun _ ↦ by simp [contract]
      isLink_iff := ?_ }
  rintro ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩
  simp [contract_isLink, comp_empty]

/-- The minor relation is transitive (Graph Minors IV, Section 1, page 228, and (7.1), page 244). -/
theorem IsIsoMinor.trans {H : Graph α'' β''} {K : Graph α' β'} {G : Graph α β}
    (hHK : IsIsoMinor H K) (hKG : IsIsoMinor K G) : IsIsoMinor H G := by
  by_cases hEK : E(K) = ∅
  · exact isIsoMinor_of_edgeSet_eq_empty hEK hHK hKG
  · obtain ⟨eK, heK⟩ := nonempty_iff_ne_empty.2 hEK
    have hβ' : Nonempty β' := ⟨eK⟩
    have hβ : Nonempty β := by
      obtain ⟨G₂, _, C₂, _, ⟨φ₂⟩⟩ := hKG
      exact ⟨(φ₂.edgeEquiv ⟨eK, heK⟩).1⟩
    obtain ⟨ηv, ηe, hm₁⟩ := exists_isMinorModel_of_isIsoMinor_aux (Or.inl hβ') hHK
    obtain ⟨ηv', ηe', hm₂⟩ := exists_isMinorModel_of_isIsoMinor_aux (Or.inl hβ) hKG
    exact isIsoMinor_of_isMinorModel_uncond (isMinorModel_comp hm₁ hm₂)

/-- `IsIsoMinor` is invariant under isomorphism on the left. -/
theorem Iso.isIsoMinor_left {H₁ : Graph α'' β''} {H₂ : Graph α' β'} {G : Graph α β}
    (φ : Iso H₁ H₂) (h : IsIsoMinor H₂ G) : IsIsoMinor H₁ G := by
  obtain ⟨G', hle, C, hC, ⟨ψ⟩⟩ := h
  exact ⟨G', hle, C, hC, ⟨φ.trans ψ⟩⟩

/-- `IsIsoMinor` is invariant under isomorphism on the right. -/
theorem Iso.isIsoMinor_right {H : Graph α'' β''} {G₁ : Graph α' β'} {G₂ : Graph α β}
    (h : IsIsoMinor H G₁) (φ : Iso G₁ G₂) : IsIsoMinor H G₂ :=
  h.trans (φ.isIsoMinor_left (.refl G₂))

/-- `IsIsoMinor` is invariant under isomorphism on both sides. -/
theorem Iso.isIsoMinor_congr {α₁ β₁ α₂ β₂ α₃ β₃ α₄ β₄ : Type*}
    {H₁ : Graph α₁ β₁} {H₂ : Graph α₂ β₂} {G₁ : Graph α₃ β₃} {G₂ : Graph α₄ β₄}
    (φH : Iso H₁ H₂) (φG : Iso G₁ G₂) : IsIsoMinor H₁ G₁ ↔ IsIsoMinor H₂ G₂ :=
  ⟨fun h ↦ (φH.symm.isIsoMinor_left h).trans (φG.isIsoMinor_left (.refl G₂)),
   fun h ↦ (φH.isIsoMinor_left h).trans (φG.symm.isIsoMinor_left (.refl G₁))⟩

end

end GraphMinor
