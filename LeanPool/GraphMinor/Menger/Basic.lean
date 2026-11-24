/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Hypergraph.Basic
import LeanPool.GraphMinor.Menger.SimpleGraph

/-!
# Menger's theorem for hypergraphs

This file proves `GraphMinor.menger` (`MengerStatement`): for a hypergraph `G`, sets
`X, Y ⊆ V(G)` and `k ≥ 0`, every separation `(G₁, G₂)` of `G` with `X ⊆ V(G₁)` and `Y ⊆ V(G₂)` has
order at least `k` if and only if the 1-skeleton of `G` has `k` mutually vertex-disjoint paths from
`X` to `Y`.

The easy direction shows that every path from `X` to `Y` in `G.skeleton` meets `V(G₁ ∩ G₂)`, so `k`
disjoint paths require at least `k` vertices in `V(G₁ ∩ G₂)`. The converse constructs a separation
`(G₁, G₂)` of `G` of order `|S|` from any vertex separator `S ⊆ V(G)` between `X` and `Y` in
`G.skeleton`, by putting into `G₁` the vertices reachable from `X` in `G.skeleton` without meeting
`S`, together with `S`, and all edges whose ends lie in `V(G₁)`, and then applies Menger's theorem
for finite simple graphs (`GraphMinor.Menger.exists_disjointPaths`) to the induced subgraph of
`G.skeleton` on `V(G)`.
-/

public section

namespace GraphMinor

open SimpleGraph

variable {α β : Type*}

private lemma exists_mem_inter_of_walk {G G₁ G₂ : Hypergraph α β}
    (hsep : G.IsSeparation G₁ G₂) {u v : α} (w : G.skeleton.Walk u v)
    (hu : u ∈ G₁.vertexSet) (hv : v ∈ G₂.vertexSet) :
    ∃ z ∈ w.support, z ∈ (G₁ ∩ G₂).vertexSet := by
  induction w with
  | nil =>
    exact ⟨_, Walk.start_mem_support _, hu, hv⟩
  | @cons u u' v hadj rest ih =>
    by_cases hu' : u' ∈ G₁.vertexSet
    · obtain ⟨z, hz, hz_mem⟩ := ih hu' hv
      exact ⟨z, List.mem_cons_of_mem _ hz, hz_mem⟩
    · obtain ⟨_, e, heu, heu'⟩ := id hadj
      have he : e ∈ (G₁ ∪ G₂).edgeSet := by
        rw [hsep.union_eq]
        exact G.edge_mem_of_inc heu
      rcases he with he₁ | he₂
      · have hends := hsep.left_le.ends_eq e he₁
        have hu'_inc : G₁.Inc e u' := by
          change u' ∈ G₁.ends e
          rw [← hends]
          exact heu'
        exact absurd (G₁.vertex_mem_of_inc hu'_inc) hu'
      · have hends := hsep.right_le.ends_eq e he₂
        have hu_inc : G₂.Inc e u := by
          change u ∈ G₂.ends e
          rw [← hends]
          exact heu
        exact ⟨u, Walk.start_mem_support _, hu, G₂.vertex_mem_of_inc hu_inc⟩

private lemma separationOrder_ge_of_hasDisjointPaths {G : Hypergraph α β} {X Y : Set α} {k : ℕ}
    (hP : HasDisjointPaths G.skeleton X Y k) {G₁ G₂ : Hypergraph α β}
    (hsep : G.IsSeparation G₁ G₂) (hX : X ⊆ G₁.vertexSet) (hY : Y ⊆ G₂.vertexSet) :
    k ≤ Hypergraph.separationOrder G₁ G₂ := by
  obtain ⟨P, hP_disj⟩ := hP
  have hex : ∀ i : Fin k, ∃ z ∈ (P i).walk.support, z ∈ (G₁ ∩ G₂).vertexSet := fun i ↦
    exists_mem_inter_of_walk hsep (P i).walk (hX (P i).first_mem) (hY (P i).last_mem)
  choose z hz_supp hz_mem using hex
  let f : Fin k → ↥(G₁ ∩ G₂).vertexSet := fun i ↦ ⟨z i, hz_mem i⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hzij : z i = z j := congrArg Subtype.val hij
    exact Set.disjoint_left.mp (hP_disj hne) (hz_supp i) (hzij ▸ hz_supp j)
  have : Finite ↥(G₁ ∩ G₂).vertexSet := (G₁ ∩ G₂).vertexSet_finite.to_subtype
  have hle := Nat.card_le_card_of_injective f hf_inj
  rw [Nat.card_fin, Nat.card_coe_set_eq] at hle
  exact hle

private lemma walk_support_subset_vertexSet {G : Hypergraph α β} {u v : α}
    (w : G.skeleton.Walk u v) (hu : u ∈ G.vertexSet) :
    ∀ z ∈ w.support, z ∈ G.vertexSet := by
  induction w with
  | nil =>
    intro z hz
    simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
    exact hz ▸ hu
  | @cons u u' v hadj rest ih =>
    obtain ⟨_, e, _, heu'⟩ := id hadj
    have hu' : u' ∈ G.vertexSet := G.vertex_mem_of_inc heu'
    intro z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · exact ih hu' z hz

/-- The vertices reachable from `X` in `G.skeleton` by walks avoiding `S`. -/
private def reachableAvoiding (G : Hypergraph α β) (X S : Set α) : Set α :=
  {v | ∃ x ∈ X, ∃ w : G.skeleton.Walk x v, ∀ z ∈ w.support, z ∉ S}

private lemma reachableAvoiding_subset {G : Hypergraph α β} {X S : Set α}
    (hX : X ⊆ G.vertexSet) : reachableAvoiding G X S ⊆ G.vertexSet \ S := by
  rintro v ⟨x, hxX, w, hw⟩
  exact ⟨walk_support_subset_vertexSet w (hX hxX) v (Walk.end_mem_support w),
    hw v (Walk.end_mem_support w)⟩

private lemma not_mem_Y_of_mem_reachableAvoiding {G : Hypergraph α β} {X Y S : Set α}
    (hS : ∀ P : PathFromTo G.skeleton X Y, ∃ x ∈ P.walk.support, x ∈ S)
    {v : α} (hv : v ∈ reachableAvoiding G X S) : v ∉ Y := by
  classical
  rintro hvY
  obtain ⟨x, hxX, w, hw⟩ := hv
  obtain ⟨z, hz, hzS⟩ := hS ⟨x, v, w.bypass, w.bypass_isPath, hxX, hvY⟩
  exact hw z (w.support_bypass_subset_support hz) hzS

private lemma adj_mem_reachableAvoiding {G : Hypergraph α β} {X S : Set α} {v u : α}
    (hv : v ∈ reachableAvoiding G X S) (hadj : G.skeleton.Adj v u) (huS : u ∉ S) :
    u ∈ reachableAvoiding G X S := by
  obtain ⟨x, hxX, w, hw⟩ := hv
  refine ⟨x, hxX, w.concat hadj, fun z hz ↦ ?_⟩
  simp only [Walk.support_concat, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with hz | rfl
  · exact hw z hz
  · exact huS

private lemma exists_separation_of_separator {G : Hypergraph α β} {X Y S : Set α}
    (hX : X ⊆ G.vertexSet) (hY : Y ⊆ G.vertexSet) (hS_sub : S ⊆ G.vertexSet)
    (hS_sep : ∀ P : PathFromTo G.skeleton X Y, ∃ x ∈ P.walk.support, x ∈ S) :
    ∃ G₁ G₂ : Hypergraph α β,
      G.IsSeparation G₁ G₂ ∧ X ⊆ G₁.vertexSet ∧ Y ⊆ G₂.vertexSet ∧
        Hypergraph.separationOrder G₁ G₂ = S.ncard := by
  let R := reachableAvoiding G X S
  have hR_sub : R ⊆ G.vertexSet \ S := reachableAvoiding_subset hX
  let V₁ : Set α := R ∪ S
  let E₁ : Set β := {e ∈ G.edgeSet | G.ends e ⊆ V₁}
  let V₂ : Set α := G.vertexSet \ R
  let E₂ : Set β := G.edgeSet \ E₁
  have hV₁_sub : V₁ ⊆ G.vertexSet :=
    Set.union_subset (hR_sub.trans Set.sdiff_subset) hS_sub
  have hV₂_sub : V₂ ⊆ G.vertexSet := Set.sdiff_subset
  have hE₂_ends : ∀ ⦃e : β⦄ ⦃v : α⦄, e ∈ E₂ → G.Inc e v → v ∈ V₂ := by
    intro e v he₂ hinc
    refine ⟨G.vertex_mem_of_inc hinc, fun hvR ↦ he₂.2 ⟨he₂.1, fun u hu ↦ ?_⟩⟩
    by_contra huV₁
    have huR : u ∉ R := fun h ↦ huV₁ (Or.inl h)
    have huS : u ∉ S := fun h ↦ huV₁ (Or.inr h)
    have hvu : v ≠ u := fun h ↦ huR (h ▸ hvR)
    have hadj : G.skeleton.Adj v u := ⟨hvu, e, hinc, hu⟩
    exact huR (adj_mem_reachableAvoiding hvR hadj huS)
  let G₁ : Hypergraph α β :=
    { vertexSet := V₁
      edgeSet := E₁
      Inc := fun e v ↦ e ∈ E₁ ∧ G.Inc e v
      vertex_mem_of_inc := fun _ _ h ↦ h.1.2 h.2
      edge_mem_of_inc := fun _ _ h ↦ h.1
      vertexSet_finite := G.vertexSet_finite.subset hV₁_sub
      edgeSet_finite := G.edgeSet_finite.subset (fun _ h ↦ h.1) }
  let G₂ : Hypergraph α β :=
    { vertexSet := V₂
      edgeSet := E₂
      Inc := fun e v ↦ e ∈ E₂ ∧ G.Inc e v
      vertex_mem_of_inc := fun _ _ h ↦ hE₂_ends h.1 h.2
      edge_mem_of_inc := fun _ _ h ↦ h.1
      vertexSet_finite := G.vertexSet_finite.subset hV₂_sub
      edgeSet_finite := G.edgeSet_finite.subset Set.sdiff_subset }
  refine ⟨G₁, G₂, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨hV₁_sub, fun _ h ↦ h.1, fun e he ↦ ?_⟩,
      ⟨hV₂_sub, Set.sdiff_subset, fun e he ↦ ?_⟩, ?_, ?_⟩
    · ext v
      simp only [Hypergraph.ends, Set.mem_ofPred_eq, G₁]
      exact ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩
    · ext v
      simp only [Hypergraph.ends, Set.mem_ofPred_eq, G₂]
      exact ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩
    · refine Hypergraph.ext ?_ ?_ ?_
      · ext v
        change v ∈ (R ∪ S) ∪ (G.vertexSet \ R) ↔ v ∈ G.vertexSet
        constructor
        · rintro ((hvR | hvS) | hv₂)
          · exact hV₁_sub (Or.inl hvR)
          · exact hS_sub hvS
          · exact hv₂.1
        · intro hv
          by_cases hvR : v ∈ R
          · exact Or.inl (Or.inl hvR)
          · exact Or.inr ⟨hv, hvR⟩
      · ext e
        change e ∈ E₁ ∪ (G.edgeSet \ E₁) ↔ e ∈ G.edgeSet
        exact ⟨fun h ↦ h.elim (fun h₁ ↦ h₁.1) (fun h₂ ↦ h₂.1),
          fun he ↦ by by_cases h₁ : e ∈ E₁ <;> [exact Or.inl h₁; exact Or.inr ⟨he, h₁⟩]⟩
      · funext e v
        apply propext
        change (e ∈ E₁ ∧ G.Inc e v) ∨ (e ∈ G.edgeSet \ E₁ ∧ G.Inc e v) ↔ G.Inc e v
        constructor
        · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
        · intro h
          by_cases h₁ : e ∈ E₁
          · exact Or.inl ⟨h₁, h⟩
          · exact Or.inr ⟨⟨G.edge_mem_of_inc h, h₁⟩, h⟩
    · ext e
      change e ∈ E₁ ∧ e ∈ G.edgeSet \ E₁ ↔ False
      exact ⟨fun ⟨h₁, _, h₂⟩ ↦ h₂ h₁, False.elim⟩
  · intro x hxX
    by_cases hxS : x ∈ S
    · exact Or.inr hxS
    · refine Or.inl ⟨x, hxX, .nil, fun z hz ↦ ?_⟩
      simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
      exact hz ▸ hxS
  · intro y hyY
    exact ⟨hY hyY, fun hyR ↦ not_mem_Y_of_mem_reachableAvoiding hS_sep hyR hyY⟩
  · have h_inter : (G₁ ∩ G₂).vertexSet = S := by
      ext v
      change v ∈ (R ∪ S) ∧ v ∈ G.vertexSet \ R ↔ v ∈ S
      constructor
      · rintro ⟨hvR | hvS, _, hvnotR⟩
        · exact False.elim (hvnotR hvR)
        · exact hvS
      · intro hvS
        exact ⟨Or.inr hvS, hS_sub hvS, fun hvR ↦ (hR_sub hvR).2 hvS⟩
    unfold Hypergraph.separationOrder
    rw [h_inter]

/-- Menger's theorem in the form of Graph Minors IV. -/
theorem menger : MengerStatement := by
  intro α β G X Y hX hY k
  refine ⟨fun hsep_ord ↦ ?_, fun hP G₁ G₂ hsep hX₁ hY₂ ↦
    separationOrder_ge_of_hasDisjointPaths hP hsep hX₁ hY₂⟩
  let K₀ := G.skeleton.induce G.vertexSet
  let X₀ : Set ↥G.vertexSet := Subtype.val ⁻¹' X
  let Y₀ : Set ↥G.vertexSet := Subtype.val ⁻¹' Y
  have hfin₀ : Finite ↥G.vertexSet := G.vertexSet_finite.to_subtype
  have h0 : HasDisjointPaths K₀ X₀ Y₀ k := by
    refine Menger.exists_disjointPaths K₀ X₀ Y₀ hfin₀ k fun S₀ hS₀ ↦ ?_
    let S : Set α := Subtype.val '' S₀
    have hS_sub : S ⊆ G.vertexSet := by
      rintro _ ⟨v, _, rfl⟩
      exact v.2
    have hS_sep : ∀ P : PathFromTo G.skeleton X Y, ∃ x ∈ P.walk.support, x ∈ S := by
      intro P
      have hw : ∀ x ∈ P.walk.support, x ∈ G.vertexSet :=
        walk_support_subset_vertexSet P.walk (hX P.first_mem)
      let w₀ := P.walk.induce G.vertexSet hw
      have hw₀_path : w₀.IsPath := by
        have hmap : (w₀.map (Embedding.induce G.vertexSet).toHom).IsPath := by
          rw [Walk.map_induce]
          exact P.isPath
        exact hmap.of_map
      let P₀ : PathFromTo K₀ X₀ Y₀ :=
        ⟨⟨P.first, hw _ (Walk.start_mem_support _)⟩,
          ⟨P.last, hw _ (Walk.end_mem_support _)⟩,
          w₀, hw₀_path, P.first_mem, P.last_mem⟩
      obtain ⟨x₀, hx₀_supp, hx₀_S₀⟩ := hS₀ P₀
      have hx₀_in_P : x₀.1 ∈ P.walk.support := by
        change x₀ ∈ w₀.support at hx₀_supp
        rw [Walk.support_induce, List.mem_attachWith] at hx₀_supp
        exact hx₀_supp
      exact ⟨x₀.1, hx₀_in_P, x₀, hx₀_S₀, rfl⟩
    obtain ⟨G₁, G₂, hsep, hX₁, hY₂, hord⟩ :=
      exists_separation_of_separator hX hY hS_sub hS_sep
    have hk_le := hsep_ord G₁ G₂ hsep hX₁ hY₂
    rw [hord, Set.ncard_image_of_injective S₀ Subtype.val_injective] at hk_le
    exact hk_le
  obtain ⟨P₀, hP₀⟩ := h0
  let emb := (Embedding.induce G.vertexSet (G := G.skeleton))
  refine ⟨fun i ↦ ⟨emb.toHom (P₀ i).first, emb.toHom (P₀ i).last,
    (P₀ i).walk.map emb.toHom, (P₀ i).isPath.map emb.injective,
    (P₀ i).first_mem, (P₀ i).last_mem⟩, fun i j hij ↦
      Set.disjoint_left.mpr fun z hzi hzj ↦ ?_⟩
  simp only [Set.mem_ofPred_eq, Walk.support_map, List.mem_map] at hzi hzj
  obtain ⟨xi, hxi, rfl⟩ := hzi
  obtain ⟨xj, hxj, hxj_eq⟩ := hzj
  have hxx : xi = xj := emb.injective hxj_eq.symm
  exact Set.disjoint_left.mp (hP₀ hij) hxi (hxx ▸ hxj)

end GraphMinor
