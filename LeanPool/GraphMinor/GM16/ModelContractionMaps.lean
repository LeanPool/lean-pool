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
# Realising a minor model with its given maps

The contraction in XVI (4.2), page 53, must retain the chosen edge
names, since the tangle is defined by which side contains a row.
Contract connected graphs within the branch sets. Their components
are exactly the branch sets, and the remaining edges are exactly the
chosen edge images. This gives an isomorphism whose vertex and edge
maps are the maps of the original model.
-/

namespace GraphMinor.GM16
open Graph Set Relation
variable {α β α' β' : Type*}

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

/-- Realise a minor model by contraction, retaining both of its maps.
This is the contraction used in XVI (4.2), page 53. -/
public theorem exists_contraction_realizing_model
    {H : Graph α' β'} {G : Graph α β} {ηv : α' → Set α} {ηe : β' → β}
    (h : IsMinorModel H G ηv ηe) :
    ∃ (G' : Graph α β) (_ : G' ≤ G) (C : Set β) (_ : C ⊆ E(G'))
      (φ : Iso H (contract G' C)),
      (∀ v : V(H), (φ.vertexEquiv v).val = ηv v.val) ∧
      (∀ e : E(H), (φ.edgeEquiv e).val = ηe e.val) := by
  let φ : Iso H (contract (modelSubgraph h) (modelContractEdges h)) :=
    { vertexEquiv :=
        (Equiv.Set.imageOfInjOn ηv V(H) (ηv_injOn h)).trans
          (Equiv.subtypeEquivRight fun _ ↦ by rw [vertexSet_contract_modelSubgraph])
      edgeEquiv :=
        (Equiv.Set.imageOfInjOn ηe E(H) h.edge_injOn).trans
          (Equiv.subtypeEquivRight fun _ ↦ by rw [edgeSet_contract_modelSubgraph])
      isLink_iff := fun ⟨e, he⟩ ⟨u, hu⟩ ⟨w, hw⟩ ↦
        contract_modelSubgraph_isLink_iff h he hu hw }
  exact ⟨modelSubgraph h, modelSubgraph_le h, modelContractEdges h,
    modelContractEdges_subset h, φ, fun _ => rfl, fun _ => rfl⟩

end ModelToMinor
end GraphMinor.GM16
