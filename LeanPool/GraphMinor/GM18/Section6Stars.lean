/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM18.Section6Part2
public import LeanPool.GraphMinor.GM04.NumberedDecomposition
public import LeanPool.GraphMinor.GM04.Patchwork.VerifyAxioms
import LeanPool.GraphMinor.Thomas.RootedTree

/-!
# Graph Minors XVIII, (6.6): the stars of the arborescences and Graph Minors IV, (3.3)

The last step of the proof of (6.6) (pages 105–106) packs the stars of the arborescences `Tᵢ` into a
set `𝒮` of star-decompositions, checks that `𝒮` is good in the sense of Graph Minors IV, Section 3,
and applies IV (3.3). The class `ℛ` and the simulation relation are those of IV, Section 9: the
rooted hypergraphs `G ⊆ ‖Pᵢ‖`, with `G` simulated in `G'` when `Pᵢ | G` is simulated in
`Pⱼ | G'`. As the paper says, "we may assume" that the `Pᵢ` are mutually disjoint. In the Lean the
`Pᵢ` share one edge type, so we tag the edges of `Pᵢ` with `i` (`GM04.tagEdgePatchwork`); the
arborescences `Tᵢ` live in different types, so we put them side by side in `Σ k, ι k`
(`sigmaTree`).

* `simulated_of_edgeRename`: renaming the edges of a patchwork gives a patchwork that it is
  simulated in.
* `isTreeDecomposition_sigmaTag`: a tree-decomposition stays one after the tagging.
* `patchworkSim_cross_iff`: the simulation of IV, Section 9 between tagged subtree hypergraphs is
  simulation of the restrictions of the untagged patchworks.
* `theorem_6_6_of_rootedDecomposition`: the proof of (6.6) after its first paragraph, by IV (3.3).
* `theorem_6_6_proof`: (6.6).
-/

public section

namespace GraphMinor.GM18

open SimpleGraph Hypergraph

universe u v w

variable {α : Type u} {β : Type v} {Ω : Type w}

/-! ## Renaming the edges of a patchwork -/

/-- If `P'` is `P` with its edges renamed by `f`, then `P` is simulated in `P'`: each vertex goes
to itself and each edge `e` to `f e`. The realization is the edgeless graph on `V(G)`. -/
theorem simulated_of_edgeRename [Preorder Ω] {β' : Type*} (P : GM04.Patchwork Ω α β)
    (P' : GM04.Patchwork Ω α β') (f : β → β')
    (hV : P'.G.vertexSet = P.G.vertexSet) (hroots : P'.G.roots = P.G.roots)
    (hE : f '' P.G.edgeSet = P'.G.edgeSet) (hinj : Set.InjOn f P.G.edgeSet)
    (hinc : ∀ e ∈ P.G.edgeSet, ∀ x, P'.G.Inc (f e) x ↔ P.G.Inc e x)
    (hdom : ∀ e ∈ P.G.edgeSet, e ∈ P.dom ↔ f e ∈ P'.dom)
    (hμ : ∀ e ∈ P.dom, P'.μ (f e) = P.μ e) (hΔ : ∀ e ∈ P.dom, P'.Δ (f e) = P.Δ e)
    (hφ : ∀ e ∈ P.G.edgeSet, P'.φ (f e) = P.φ e) :
    GM04.Simulated P P' := by
  classical
  have hexp : GM04.IsExpansion P P' (fun x ↦ {x}) f :=
    { vertex_nonempty := fun x _ ↦ Set.singleton_nonempty x
      vertex_subset := fun x hx y hy ↦ by
        rw [Set.mem_singleton_iff.1 hy, hV]
        exact hx
      edge_mem := fun e he ↦ hE ▸ Set.mem_image_of_mem f he
      vertex_disjoint := fun _ _ _ _ hne ↦ Set.disjoint_singleton.mpr hne
      edge_injOn := hinj
      mem_dom_iff := hdom
      ends_nonempty := fun e he _ x hx ↦ ⟨x, rfl, (hinc e he x).2 hx⟩
      μ_length := fun e he ↦ by rw [hμ e he]
      μ_mem := fun e he i hi hi' ↦ by
        simp only [Set.mem_singleton_iff]
        simp only [hμ e he]
      roots_length := by rw [hroots]
      roots_mem := fun i hi hi' ↦ by
        simp only [Set.mem_singleton_iff]
        simp only [hroots]
      maps_Δ := fun e he δ hδ ↦ by
        have heE : e ∈ P.G.edgeSet := P.dom_subset he
        have hverts : δ.verts ⊆ {x | x ∈ P.μ e} := by
          rw [((P.Δ e).verts_eq δ hδ).trans (P.Δ_verts e heE), P.μ_set e he]
        rw [hμ e he, hΔ e he, GM04.marchMapSubgraph_id hverts]
        exact hδ
      φ_le := fun e he ↦ (hφ e he).symm ▸ le_rfl }
  have hdel : (P'.deleteEdges (f '' P.G.edgeSet)).G.edgeSet = ∅ := by
    change P'.G.edgeSet \ f '' P.G.edgeSet = ∅
    rw [hE, Set.sdiff_self]
  refine ⟨fun x ↦ {x}, f, hexp, GM04.emptySubgraph P'.G.vertexSet, ?_, fun x hx ↦ ?_⟩
  · refine ⟨fun _ ↦ GM04.emptySubgraph ∅, fun e he ↦ ?_, ?_⟩
    · rw [hdel] at he
      exact he.elim
    · ext a b
      · simp only [GM04.realizationOf, Subgraph.verts_sup, Subgraph.verts_iSup,
          GM04.emptySubgraph_verts, hdel, Set.mem_empty_iff_false, Set.iUnion_of_empty,
          Set.iUnion_empty, Set.union_empty]
        rfl
      · simp only [GM04.not_emptySubgraph_adj, GM04.realizationOf_adj, false_iff, not_exists,
          hdel, Set.mem_empty_iff_false, false_and, not_false_eq_true, implies_true]
  · have hx' : x ∈ P'.G.vertexSet := hV ▸ hx
    let y : (GM04.emptySubgraph P'.G.vertexSet).verts := ⟨x, hx'⟩
    refine ⟨GM04.component (GM04.emptySubgraph P'.G.vertexSet) y, ⟨y, rfl⟩, ?_⟩
    ext w
    simp only [GM04.component_verts, GM04.mem_componentVerts_iff,
      GM04.emptySubgraph_verts, Set.mem_singleton_iff]
    refine ⟨?_, fun hEq ↦ hEq ▸ ⟨hx', Reachable.refl y⟩⟩
    rintro ⟨hw, hr⟩
    suffices ∀ z : (GM04.emptySubgraph P'.G.vertexSet).verts,
        (GM04.emptySubgraph P'.G.vertexSet).coe.Reachable y z → z.1 = y.1 from
      this ⟨w, hw⟩ hr
    intro z hz
    rw [reachable_iff_reflTransGen] at hz
    induction hz with
    | refl => rfl
    | @tail _ _ _ hab => exact False.elim hab

/-- Patchworks that agree are simulated in each other. -/
theorem simulated_of_agrees [Preorder Ω] {P₁ P₂ : GM04.Patchwork Ω α β} (h : P₁.Agrees P₂) :
    GM04.Simulated P₁ P₂ := by
  obtain ⟨ηv, ηe, hη⟩ := GM04.Simulated.refl P₁
  exact ⟨ηv, ηe, hη.congr (GM04.Patchwork.Agrees.rfl P₁) h⟩

/-! ## Tagging the edges -/

theorem tagEdgeHypergraph_le {G H : Hypergraph α β} (h : G ≤ H) (i : ℕ) :
    GM04.tagEdgeHypergraph i G ≤ GM04.tagEdgeHypergraph i H := by
  refine ⟨h.vertexSet_subset, Set.image_mono h.edgeSet_subset, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  rw [GM04.tagEdgeHypergraph_ends, GM04.tagEdgeHypergraph_ends]
  exact h.ends_eq e he

theorem tagEdgeHypergraph_biUnion {ι : Type*} (s : Finset ι) (G : ι → Hypergraph α β) (i : ℕ) :
    GM04.tagEdgeHypergraph i (Hypergraph.biUnion s G) =
      Hypergraph.biUnion s fun t ↦ GM04.tagEdgeHypergraph i (G t) := by
  ext
  · simp [GM04.tagEdgeHypergraph, Hypergraph.biUnion]
  · simp only [GM04.tagEdgeHypergraph, Hypergraph.biUnion, Set.image_iUnion₂]
  · simp only [GM04.tagEdgeHypergraph, Hypergraph.biUnion]
    exact ⟨fun ⟨h₁, t, ht, h⟩ ↦ ⟨t, ht, h₁, h⟩, fun ⟨t, ht, h₁, h⟩ ↦ ⟨h₁, t, ht, h⟩⟩

/-- `P | G` is simulated in `P' | G'`, where `P'` and `G'` are `P` and `G` with their edges tagged
`i`. -/
theorem simulated_restrict_tag [Preorder Ω] (P : GM04.Patchwork Ω α β) {G : RootedHypergraph α β}
    (hG : G.toHypergraph ≤ P.G.toHypergraph) (i : ℕ) :
    GM04.Simulated (P.restrict G)
      ((GM04.tagEdgePatchwork i P).restrict (GM04.tagEdgeRooted i G)) := by
  have hG' : (GM04.tagEdgeRooted i G).toHypergraph ≤ (GM04.tagEdgePatchwork i P).G.toHypergraph :=
    tagEdgeHypergraph_le hG i
  refine simulated_of_edgeRename _ _ (Prod.mk i) rfl rfl rfl (Prod.mk_right_injective i).injOn
    (fun e _ x ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨rfl, h⟩⟩) (fun e he ↦ ?_) (fun _ _ ↦ rfl)
    (fun e he ↦ ?_) (fun _ _ ↦ rfl)
  · rw [GM04.Patchwork.restrict_dom hG, GM04.Patchwork.restrict_dom hG']
    simp [GM04.tagEdgePatchwork, GM04.tagEdgeRooted, GM04.tagEdgeHypergraph]
  · have he' : e ∈ G.edgeSet := ((GM04.Patchwork.restrict_dom hG ▸ he) : e ∈ P.dom ∩ _).2
    rw [GM04.Patchwork.restrict_Δ hG he', GM04.Patchwork.restrict_Δ hG' ⟨e, he', rfl⟩]
    rfl

/-- `P' | G'` is simulated in `P | G`, where `P'` and `G'` are `P` and `G` with their edges tagged
`i`. -/
theorem simulated_tag_restrict [Preorder Ω] (P : GM04.Patchwork Ω α β) {G : RootedHypergraph α β}
    (hG : G.toHypergraph ≤ P.G.toHypergraph) (i : ℕ) :
    GM04.Simulated ((GM04.tagEdgePatchwork i P).restrict (GM04.tagEdgeRooted i G))
      (P.restrict G) := by
  have hG' : (GM04.tagEdgeRooted i G).toHypergraph ≤ (GM04.tagEdgePatchwork i P).G.toHypergraph :=
    tagEdgeHypergraph_le hG i
  refine simulated_of_edgeRename _ _ Prod.snd rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · change Prod.snd '' (Prod.mk i '' G.edgeSet) = G.edgeSet
    rw [Set.image_image]
    exact Set.image_id' G.edgeSet
  · rintro _ ⟨e₁, _, rfl⟩ _ ⟨e₂, _, rfl⟩ h
    exact congrArg (Prod.mk i) h
  · rintro _ ⟨e, _, rfl⟩ x
    exact ⟨fun h ↦ ⟨rfl, h⟩, fun h ↦ h.2⟩
  · rintro _ ⟨e, he, rfl⟩
    rw [GM04.Patchwork.restrict_dom hG, GM04.Patchwork.restrict_dom hG']
    simp [GM04.tagEdgePatchwork, GM04.tagEdgeRooted, GM04.tagEdgeHypergraph]
  · intro _ _
    rfl
  · intro p hp
    rw [GM04.Patchwork.restrict_dom hG'] at hp
    obtain ⟨-, ⟨e, he, rfl⟩⟩ := hp
    rw [GM04.Patchwork.restrict_Δ hG he, GM04.Patchwork.restrict_Δ hG' ⟨e, he, rfl⟩]
    rfl
  · intro _ _
    rfl

/-- The simulation of Graph Minors IV, Section 9 (`GM04.patchworkSim`) for the tagged patchworks,
between tagged subhypergraphs, is simulation of the restrictions of the untagged patchworks. -/
theorem patchworkSim_tag_iff [Preorder Ω] (P : ℕ → GM04.Patchwork Ω α β) {i j : ℕ}
    {G H : RootedHypergraph α β} (hG : G.toHypergraph ≤ (P i).G.toHypergraph)
    (hH : H.toHypergraph ≤ (P j).G.toHypergraph) :
    GM04.patchworkSim (fun k ↦ GM04.tagEdgePatchwork k (P k)) (GM04.tagEdgeRooted i G)
        (GM04.tagEdgeRooted j H) ↔
      GM04.Simulated ((P i).restrict G) ((P j).restrict H) := by
  have hd := GM04.tagEdgePatchwork_disjoint P
  have hAG := GM04.inducedPatchwork_agrees hd (i := i) (G := GM04.tagEdgeRooted i G)
    (tagEdgeHypergraph_le hG i)
  have hAH := GM04.inducedPatchwork_agrees hd (i := j) (G := GM04.tagEdgeRooted j H)
    (tagEdgeHypergraph_le hH j)
  constructor
  · intro h
    exact ((simulated_restrict_tag (P i) hG i).trans (simulated_of_agrees hAG.symm)).trans
      (h.trans ((simulated_of_agrees hAH).trans (simulated_tag_restrict (P j) hH j)))
  · intro h
    exact ((simulated_of_agrees hAG).trans (simulated_tag_restrict (P i) hG i)).trans
      (h.trans ((simulated_restrict_tag (P j) hH j).trans (simulated_of_agrees hAH.symm)))

/-- Tagging the edges of the bags keeps a tree-decomposition. -/
theorem isTreeDecomposition_tag {ι : Type*} {G : RootedHypergraph α β} {T : GM04.RootedTree ι}
    {τ : ι → RootedHypergraph α β} (htd : GM04.IsTreeDecomposition G T τ) (i : ℕ) :
    GM04.IsTreeDecomposition (GM04.tagEdgeRooted i G) T fun t ↦ GM04.tagEdgeRooted i (τ t) := by
  refine ⟨fun t ht ↦ tagEdgeHypergraph_le (htd.le t ht) i, ?_, ?_, ?_, htd.roots_root,
    htd.rootSet_edge⟩
  · change Hypergraph.biUnion T.verts (fun t ↦ GM04.tagEdgeHypergraph i (τ t).toHypergraph) =
      GM04.tagEdgeHypergraph i G.toHypergraph
    rw [← tagEdgeHypergraph_biUnion, htd.biUnion_eq]
  · intro t₁ ht₁ t₂ ht₂ hne
    rw [Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨⟨e₁, he₁, rfl⟩, ⟨e₂, he₂, hEq⟩⟩
    obtain rfl : e₁ = e₂ := congrArg Prod.snd hEq.symm
    have he_inter : e₁ ∈ ((τ t₁).toHypergraph ∩ (τ t₂).toHypergraph).edgeSet := ⟨he₁, he₂⟩
    rw [htd.edgeSet_inter_eq t₁ ht₁ t₂ ht₂ hne] at he_inter
    exact he_inter
  · intro t₁ ht₁ t₂ ht₂ t₃ ht₃ hpath
    have hle := htd.inter_le t₁ ht₁ t₂ ht₂ t₃ ht₃ hpath
    refine ⟨hle.vertexSet_subset, ?_, ?_⟩
    · rintro _ ⟨⟨e₁, he₁, rfl⟩, ⟨e₃, he₃, hEq⟩⟩
      obtain rfl : e₁ = e₃ := congrArg Prod.snd hEq.symm
      exact ⟨e₁, hle.edgeSet_subset ⟨he₁, he₃⟩, rfl⟩
    · rintro _ ⟨⟨e₁, he₁, rfl⟩, ⟨e₃, he₃, hEq⟩⟩
      obtain rfl : e₁ = e₃ := congrArg Prod.snd hEq.symm
      ext v
      have hends := congrArg (v ∈ ·) (hle.ends_eq e₁ ⟨he₁, he₃⟩)
      dsimp only [Hypergraph.ends, Inter.inter, GM04.tagEdgeRooted, GM04.tagEdgeHypergraph]
        at hends ⊢
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq] at hends ⊢
      exact ⟨fun h ↦ ⟨⟨rfl, (hends.mp h.2).1⟩, ⟨rfl, (hends.mp h.2).2⟩⟩,
        fun ⟨h₁, h₃⟩ ↦ ⟨rfl, hends.mpr ⟨h₁.2, h₃.2⟩⟩⟩

/-! ## The disjoint union of the arborescences -/

section Sigma

variable {ι : ℕ → Type*} (T : ∀ i, GM04.RootedTree (ι i))

theorem exists_eq_of_mem_sigmaTree_verts {i : ℕ} {p : Σ k, ι k}
    (hp : p ∈ (sigmaTree T i).verts) : ∃ t ∈ (T i).verts, p = ⟨i, t⟩ := by
  obtain ⟨j, t⟩ := p
  obtain ⟨rfl, ht⟩ := (mem_sigmaTree_verts T i ⟨j, t⟩).1 hp
  exact ⟨t, ht, rfl⟩

theorem subtreeAt_sigmaTree (i : ℕ) (t : ι i) :
    (sigmaTree T i).subtreeAt ⟨i, t⟩ =
      ((T i).subtreeAt t).map ⟨Sigma.mk i, sigma_mk_injective⟩ := by
  ext p
  rw [GM04.RootedTree.mem_subtreeAt, Finset.mem_map]
  constructor
  · intro hr
    obtain ⟨u, -, rfl⟩ := exists_eq_of_mem_sigmaTree_verts T hr.1
    exact ⟨u, GM04.RootedTree.mem_subtreeAt _ |>.2 ((sigmaTree_reaches_mk_iff T i t u).1 hr), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact (sigmaTree_reaches_mk_iff T i t u).2 ((GM04.RootedTree.mem_subtreeAt _).1 hu)

theorem biUnion_map_sigma {γ : Type*} (i : ℕ) (s : Finset (ι i))
    (G : (Σ k, ι k) → Hypergraph α γ) :
    Hypergraph.biUnion (s.map ⟨Sigma.mk i, sigma_mk_injective⟩) G =
      Hypergraph.biUnion s fun t ↦ G ⟨i, t⟩ := by
  ext <;> simp [Hypergraph.biUnion]

theorem onPath_sigmaTree {i : ℕ} {a b c : ι i}
    (h : (sigmaTree T i).OnPath ⟨i, a⟩ ⟨i, b⟩ ⟨i, c⟩) : (T i).OnPath a b c := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, fun x hxa hxb ↦ ?_⟩
  · rcases h₁ with h | h
    · exact Or.inl ((sigmaTree_reaches_mk_iff T i c a).1 h)
    · exact Or.inr ((sigmaTree_reaches_mk_iff T i c b).1 h)
  · exact (sigmaTree_reaches_mk_iff T i x c).1
      (h₂ ⟨i, x⟩ ((sigmaTree_reaches_mk_iff T i x a).2 hxa) ((sigmaTree_reaches_mk_iff T i x b).2
        hxb))

/-- A tree-decomposition with tree `Tᵢ` is one with tree `sigmaTree T i`, when the bag of `⟨i, t⟩`
is the bag of `t`. -/
theorem isTreeDecomposition_sigmaTree {γ : Type*} {G : RootedHypergraph α γ} {i : ℕ}
    {τ : ι i → RootedHypergraph α γ} {τ' : (Σ k, ι k) → RootedHypergraph α γ}
    (hτ : ∀ t, τ' ⟨i, t⟩ = τ t) (h : GM04.IsTreeDecomposition G (T i) τ) :
    GM04.IsTreeDecomposition G (sigmaTree T i) τ' where
  le p hp := by
    obtain ⟨t, ht, rfl⟩ := exists_eq_of_mem_sigmaTree_verts T hp
    rw [hτ]
    exact h.le t ht
  biUnion_eq := by
    rw [sigmaTree_verts, biUnion_map_sigma]
    simp only [hτ]
    exact h.biUnion_eq
  edgeSet_inter_eq p₁ hp₁ p₂ hp₂ hne := by
    obtain ⟨t₁, ht₁, rfl⟩ := exists_eq_of_mem_sigmaTree_verts T hp₁
    obtain ⟨t₂, ht₂, rfl⟩ := exists_eq_of_mem_sigmaTree_verts T hp₂
    rw [hτ, hτ]
    exact h.edgeSet_inter_eq t₁ ht₁ t₂ ht₂ fun h ↦ hne (h ▸ rfl)
  inter_le p₁ hp₁ p₂ hp₂ p₃ hp₃ hpath := by
    obtain ⟨t₁, ht₁, rfl⟩ := exists_eq_of_mem_sigmaTree_verts T hp₁
    obtain ⟨t₂, ht₂, rfl⟩ := exists_eq_of_mem_sigmaTree_verts T hp₂
    obtain ⟨t₃, ht₃, rfl⟩ := exists_eq_of_mem_sigmaTree_verts T hp₃
    rw [hτ, hτ, hτ]
    exact h.inter_le t₁ ht₁ t₂ ht₂ t₃ ht₃ (onPath_sigmaTree T hpath)
  roots_root := by
    rw [sigmaTree_root, hτ]
    exact h.roots_root
  rootSet_edge p hp := by
    obtain ⟨t, -, rfl⟩ := exists_eq_of_mem_sigmaTree_verts T ((sigmaTree T i).edges_subset_verts hp)
    rw [sigmaTree_parent_mk, hτ, hτ]
    exact h.rootSet_edge t ((mem_sigmaTree_edges_mk T i t).1 hp)

/-- The bags of the tagged decompositions: the bag of `⟨k, t⟩` is `τ k t` with its edges tagged
`k`. -/
noncomputable def tagBags (τ : ∀ i, ι i → RootedHypergraph α β) (p : Σ k, ι k) :
    RootedHypergraph α (ℕ × β) :=
  GM04.tagEdgeRooted p.1 (τ p.1 p.2)

theorem cross_tagBags (τ : ∀ i, ι i → RootedHypergraph α β) (i : ℕ) {S : Finset (ι i)} {r : ι i}
    (hr : r ∈ S) :
    GM04.cross (tagBags τ) (S.map ⟨Sigma.mk i, sigma_mk_injective⟩) ⟨i, r⟩ =
      GM04.tagEdgeRooted i (GM04.cross (τ i) S r) := by
  refine RootedHypergraph.ext ?_ rfl
  have hr' : (⟨i, r⟩ : Σ k, ι k) ∈ S.map ⟨Sigma.mk i, sigma_mk_injective⟩ :=
    Finset.mem_map_of_mem _ hr
  rw [GM04.cross_toHypergraph_of_mem _ hr', biUnion_map_sigma]
  change _ = GM04.tagEdgeHypergraph i (GM04.cross (τ i) S r).toHypergraph
  rw [GM04.cross_toHypergraph_of_mem _ hr, tagEdgeHypergraph_biUnion]
  rfl

end Sigma

/-! ## The proof of (6.6) -/

/-- The proof of **Graph Minors XVIII, (6.6)** (pages 105–106) after its first paragraph, which
gives
the rooted decompositions `(Tᵢ, τᵢ)` by (6.4). As in the paper: let `ℛ` be the class of rooted
hypergraphs `G ⊆ ‖Pᵢ‖` with the simulation of Graph Minors IV, Section 9; let `𝒮` be the set of the
stars of the `Tᵢ`, with `σ(s) = τᵢ(s)` and `σ(t) = τᵢ × Tᵢᵗ`; check that `𝒮` is good, the third
condition being Claim (2) (`lemma_6_6_claim_2`) "in different language"; and apply Graph Minors IV,
(3.3). The `Pᵢ` are made disjoint by tagging their edges, and the `Tᵢ` are put side by side in
`Σ k, ι k`. -/
theorem theorem_6_6_of_rootedDecomposition [Infinite β] [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω)
    {ι : ℕ → Type*} [∀ i, Fintype (ι i)]
    {𝒞 : Set (PartialPatchwork Ω α β)} (h𝒞 : WellBehaved 𝒞)
    (P : ℕ → GM04.Patchwork Ω α β) (hrootless : ∀ i, IsRootless (P i))
    (S : ∀ i, SimpleGraph (ι i)) (σ : ∀ i, ι i → Hypergraph α β)
    (hprop : ∀ i, IsProper (P i).G.toHypergraph (S i) (σ i))
    (hpieces : ∀ i u (Q : PartialPatchwork Ω α β),
      IsPiece (toPartialPatchwork (P i)) (S i) (σ i) u Q → Q ∈ 𝒞)
    (T : ∀ i, GM04.RootedTree (ι i)) (hT_verts : ∀ i, (T i).verts = Finset.univ)
    (hT_S : ∀ i, arborescenceUnderlying (T i) = S i)
    (τ : ∀ i, ι i → RootedHypergraph α β)
    (hdec : ∀ i, IsRootedDecomposition (P i) (T i) (τ i))
    (hσ : ∀ i u, (τ i u).toHypergraph = σ i u) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) := by
  classical
  have hmem : ∀ i (t : ι i), t ∈ (T i).verts := fun i t ↦ hT_verts i ▸ Finset.mem_univ t
  -- Every march `π(τᵢ(t))` has length at most `k`, since the pieces are in `𝒞`.
  obtain ⟨k, hk_roots⟩ := (wellBehaved_rootingClosure h𝒞).exists_roots_length_le hΩ
  have hroots_le : ∀ i t, (τ i t).roots.length ≤ k := by
    intro i t
    by_cases ht : t = (T i).root
    · subst ht
      rw [(hdec i).isTreeDecomposition.roots_root, ← RootedHypergraph.ncard_rootSet, hrootless i,
        Set.ncard_empty]
      exact Nat.zero_le k
    · obtain ⟨Q, hQ_mem, ℒ, _, ⟨_, hheart⟩, _⟩ :=
        lemma_6_6_claim_1 (hrootless i) (hprop i) (hT_verts i) (hT_S i) (hdec i) (hσ i)
          (hpieces i) t
      have hroots_eq : (GM04.cross (τ i) ((T i).subtreeAt t) t).roots = Q.G.roots :=
        hheart.roots_eq.symm
      calc (τ i t).roots.length = (GM04.cross (τ i) ((T i).subtreeAt t) t).roots.length := rfl
        _ = Q.G.roots.length := by rw [hroots_eq]
        _ ≤ k := hk_roots Q hQ_mem
  -- The tagged patchworks, the trees side by side, and the tagged bags.
  let P' : ℕ → GM04.Patchwork Ω α (ℕ × β) := fun j ↦ GM04.tagEdgePatchwork j (P j)
  let T' : ℕ → GM04.RootedTree (Σ k, ι k) := sigmaTree T
  let τ' : (Σ k, ι k) → RootedHypergraph α (ℕ × β) := tagBags τ
  have hT'dec : ∀ i, GM04.IsTreeDecomposition (P' i).G (T' i) τ' := fun i ↦
    isTreeDecomposition_sigmaTree T (fun _ ↦ rfl)
      (isTreeDecomposition_tag (hdec i).isTreeDecomposition i)
  have hcross : ∀ i t, GM04.cross τ' ((T' i).subtreeAt ⟨i, t⟩) ⟨i, t⟩ =
      GM04.tagEdgeRooted i (GM04.cross (τ i) ((T i).subtreeAt t) t) := by
    intro i t
    rw [subtreeAt_sigmaTree]
    exact cross_tagBags τ i ((T i).self_mem_subtreeAt (hmem i t))
  have hle : ∀ i t, (GM04.cross (τ i) ((T i).subtreeAt t) t).toHypergraph ≤
      (P i).G.toHypergraph := fun i t ↦
    (hdec i).isTreeDecomposition.cross_le ((T i).subtreeAt_subset_verts t)
      ((T i).self_mem_subtreeAt (hmem i t))
  -- Simulation in `ℛ` between subtree hypergraphs is simulation of the subtree patchworks.
  have hK : ∀ (i : ℕ) (t : ι i) (j : ℕ) (u : ι j),
      GM04.patchworkSim P' (GM04.cross τ' ((T' i).subtreeAt ⟨i, t⟩) ⟨i, t⟩)
          (GM04.cross τ' ((T' j).subtreeAt ⟨j, u⟩) ⟨j, u⟩) ↔
        GM04.Simulated (sigmaSubtreePatchwork P T τ ⟨i, t⟩) (sigmaSubtreePatchwork P T τ ⟨j, u⟩)
          := by
    intro i t j u
    rw [hcross, hcross, sigmaSubtreePatchwork_mk, sigmaSubtreePatchwork_mk]
    exact patchworkSim_tag_iff P (hle i t) (hle j u)
  have hord : ∀ i t, t ∈ (T i).edges →
      GM04.edgeOrder (T' i) τ' ⟨i, t⟩ = GM04.edgeOrder (T i) (τ i) t := by
    intro i t ht
    rw [(hT'dec i).edgeOrder_eq_length_roots ((mem_sigmaTree_edges_mk T i t).2 ht),
      (hdec i).isTreeDecomposition.edgeOrder_eq_length_roots ht]
    rfl
  -- The set `𝒮` of the stars of the trees.
  let 𝒮 : Set (GM04.RootedTree (Σ k, ι k) × ((Σ k, ι k) → RootedHypergraph α (ℕ × β))) :=
    {x | ∃ (i : ℕ) (t : ι i), x = ((T' i).starAt ⟨i, t⟩, GM04.branching (T' i) τ' ⟨i, t⟩)}
  have hgood : GM04.IsGood (GM04.patchworkClass P') (GM04.patchworkSim P') 𝒮 := by
    refine ⟨?_, ?_, ⟨k, ?_⟩, ?_⟩
    · rintro _ ⟨i, t, rfl⟩
      exact (hT'dec i).isStarDecomposition_branching ((mem_sigmaTree_verts_mk T i t).2 (hmem i t))
    · rintro _ ⟨i, t, rfl⟩
      have hs := (mem_sigmaTree_verts_mk T i t).2 (hmem i t)
      refine ⟨i, ?_⟩
      change (GM04.cross (GM04.branching (T' i) τ' ⟨i, t⟩) ((T' i).starAt ⟨i, t⟩).verts
        ((T' i).starAt ⟨i, t⟩).root).toHypergraph ≤ _
      rw [GM04.cross_branching_eq _ _ hs]
      exact (hT'dec i).cross_le ((T' i).subtreeAt_subset_verts _) ((T' i).self_mem_subtreeAt hs)
    · rintro _ ⟨i, t, rfl⟩
      refine Finset.sup_le fun p hp ↦ ?_
      dsimp only at hp ⊢
      rcases (T' i).mem_starAt_verts.mp hp with rfl | hpc
      · rw [GM04.branching_self]
        exact hroots_le i t
      · rw [GM04.branching_of_mem_children _ _ hpc]
        obtain ⟨u, -, rfl⟩ :=
          exists_eq_of_mem_sigmaTree_verts T ((T' i).children_subset_verts _ hpc)
        exact hroots_le i u
    · intro x hx hwell
      choose i t hxeq using hx
      let X : Set (Σ k, ι k) := Set.range fun n ↦ (⟨i n, t n⟩ : Σ k, ι k)
      -- The tips of the stars are well-simulated, so `B(N(X))` is well-quasi-ordered.
      have hY_wqo : ∀ y : ℕ → GM04.Patchwork Ω α β,
          (∀ m, y m ∈ sigmaSubtreePatchwork P T τ '' sigmaOutNeighbours T X) →
          ∃ a b, a < b ∧ GM04.Simulated (y a) (y b) := by
        intro y hy
        choose q hq hqy using hy
        have hq' : ∀ m, ∃ n u, q m = ⟨i n, u⟩ ∧ u ∈ (T (i n)).children (t n) := by
          intro m
          obtain ⟨j, hqe, n, hn⟩ := (mem_sigmaOutNeighbours T X (q m)).1 (hq m)
          obtain ⟨u, -, hu⟩ :=
            exists_eq_of_mem_sigmaTree_verts T ((sigmaTree T j).edges_subset_verts hqe)
          rw [hu, sigmaTree_parent_mk] at hn
          obtain ⟨rfl, hpar⟩ := Sigma.mk.inj_iff.1 hn
          refine ⟨n, u, hu, (T (i n)).mem_children_iff.2
            ⟨(mem_sigmaTree_edges_mk T (i n) u).1 (hu ▸ hqe), eq_of_heq hpar.symm⟩⟩
        choose n u hqu hu using hq'
        obtain ⟨a, b, hab, hsim⟩ := hwell
          (fun m ↦ GM04.cross τ' ((T' (i (n m))).subtreeAt ⟨i (n m), u m⟩) ⟨i (n m), u m⟩)
          (fun m ↦ by
            refine Set.mem_iUnion.2 ⟨n m, ⟨⟨i (n m), u m⟩, ?_, ?_⟩⟩ <;> rw [hxeq (n m)]
            · rw [GM04.RootedTree.starAt_edges]
              exact (T' (i (n m))).mem_children_iff.2
                ⟨(mem_sigmaTree_edges_mk T _ _).2 ((T (i (n m))).mem_children_iff.1 (hu m)).1,
                  by rw [sigmaTree_parent_mk, ((T (i (n m))).mem_children_iff.1 (hu m)).2]⟩
            · refine (GM04.branching_of_ne _ _ ?_).symm
              intro hEq
              have hut : u m = t (n m) := eq_of_heq (Sigma.mk.inj_iff.1 hEq).2
              exact (T (i (n m))).self_notMem_children (t (n m)) (hut ▸ hu m))
        refine ⟨a, b, hab, ?_⟩
        rw [← hqy a, ← hqy b, hqu a, hqu b]
        exact (hK _ _ _ _).1 hsim
      obtain ⟨a, b, hab, hsim⟩ :=
        lemma_6_6_claim_2 hΩ h𝒞 hrootless hprop hT_verts hT_S hdec hσ hpieces hY_wqo
          (fun m ↦ sigmaSubtreePatchwork P T τ ⟨i m, t m⟩) (fun m ↦ ⟨_, ⟨m, rfl⟩, rfl⟩)
      refine ⟨a, b, hab, ?_⟩
      rw [hxeq a, hxeq b]
      dsimp only
      rw [GM04.cross_branching_eq _ _ ((mem_sigmaTree_verts_mk T _ _).2 (hmem _ _)),
        GM04.cross_branching_eq _ _ ((mem_sigmaTree_verts_mk T _ _).2 (hmem _ _))]
      exact (hK _ _ _ _).2 hsim
  -- `E(Tᵢ)` is linked, since `(Tᵢ, τᵢ)` is a rooted decomposition.
  have hlinked : ∀ i, GM04.IsLinked (GM04.patchworkSim P') (T' i) τ' ((T' i).edges : Set _) := by
    intro i f₁ hf₁ f₂ hf₂ hreach hordeq hmin
    obtain ⟨a, -, rfl⟩ := exists_eq_of_mem_sigmaTree_verts T ((T' i).edges_subset_verts hf₁)
    obtain ⟨b, -, rfl⟩ := exists_eq_of_mem_sigmaTree_verts T ((T' i).edges_subset_verts hf₂)
    have ha : a ∈ (T i).edges := (mem_sigmaTree_edges_mk T i a).1 hf₁
    have hb : b ∈ (T i).edges := (mem_sigmaTree_edges_mk T i b).1 hf₂
    rw [hord i a ha, hord i b hb] at hordeq
    refine (hK i a i b).2 ?_
    rw [sigmaSubtreePatchwork_mk, sigmaSubtreePatchwork_mk]
    refine (hdec i).isLinked a ha b hb ((sigmaTree_reaches_mk_iff T i b a).1 hreach) hordeq ?_
    rintro g ⟨⟨hbg, hga⟩, hg⟩
    have hge : g ∈ (T i).edges := hg
    have h := hmin ⟨i, g⟩ ⟨⟨(sigmaTree_reaches_mk_iff T i b g).2 hbg,
      (sigmaTree_reaches_mk_iff T i g a).2 hga⟩, (mem_sigmaTree_edges_mk T i g).2 hge⟩
    rwa [hord i a ha, hord i g hge] at h
  -- Apply Graph Minors IV, (3.3).
  obtain ⟨a, b, hab, hsim⟩ := GM04.theorem_3_3_proved (GM04.axiom1_patchwork P')
    (GM04.axiom2_patchwork P') 𝒮 hgood T' (fun _ ↦ τ')
    (fun i ↦ by rw [(hT'dec i).cross_verts_eq]; exact hT'dec i) hlinked
    (fun i s hs ↦ by
      obtain ⟨t, -, rfl⟩ := exists_eq_of_mem_sigmaTree_verts T hs
      exact ⟨i, t, rfl⟩)
  refine ⟨a, b, hab, ?_⟩
  rw [← GM04.cross_subtreeAt_root, ← GM04.cross_subtreeAt_root] at hsim
  simp only [T', sigmaTree_root] at hsim
  have h := (hK a (T a).root b (T b).root).1 hsim
  rw [sigmaSubtreePatchwork_mk, sigmaSubtreePatchwork_mk, GM04.cross_subtreeAt_root,
    GM04.cross_subtreeAt_root, (hdec a).isTreeDecomposition.cross_verts_eq,
    (hdec b).isTreeDecomposition.cross_verts_eq] at h
  exact ((simulated_of_agrees (GM04.Patchwork.agrees_restrict_self (P a)).symm).trans h).trans
    (simulated_of_agrees (GM04.Patchwork.agrees_restrict_self (P b)))

private noncomputable def treeRootOfIsTree {ι : Type*} {K : SimpleGraph ι}
    (hK : K.IsTree) : ι :=
  hK.connected.nonempty.some

private noncomputable def parentOfIsTree {ι : Type*} [DecidableEq ι] {K : SimpleGraph ι}
    (hK : K.IsTree) (u : ι) : ι :=
  if u = treeRootOfIsTree hK then treeRootOfIsTree hK
  else (Thomas.treePath hK u (treeRootOfIsTree hK)).getVert 1

private theorem treePath_eq_cons_parentOfIsTree {ι : Type*} [DecidableEq ι] {K : SimpleGraph ι}
    (hK : K.IsTree) {u : ι} (hu : u ≠ treeRootOfIsTree hK) :
    ∃ (hadj : K.Adj u (parentOfIsTree hK u)),
      Thomas.treePath hK u (treeRootOfIsTree hK) =
        Walk.cons hadj (Thomas.treePath hK (parentOfIsTree hK u) (treeRootOfIsTree hK)) := by
  generalize hp : Thomas.treePath hK u (treeRootOfIsTree hK) = p
  cases p with
  | nil => exact (hu rfl).elim
  | @cons _ v _ hadj q =>
    have hpar : parentOfIsTree hK u = v := by
      unfold parentOfIsTree
      rw [ite_eq_right hu, hp, Walk.getVert_cons_succ, Walk.getVert_zero]
    subst hpar
    refine ⟨hadj, ?_⟩
    have hpath : (Walk.cons hadj q).IsPath :=
      hp ▸ Thomas.treePath_isPath hK u (treeRootOfIsTree hK)
    have hq_path : q.IsPath := hpath.of_cons
    rw [Thomas.eq_treePath hK q hq_path]

private theorem treeDist_parentOfIsTree {ι : Type*} [DecidableEq ι] {K : SimpleGraph ι}
    (hK : K.IsTree) {u : ι} (hu : u ≠ treeRootOfIsTree hK) :
    Thomas.treeDist hK (parentOfIsTree hK u) (treeRootOfIsTree hK) + 1 =
      Thomas.treeDist hK u (treeRootOfIsTree hK) := by
  obtain ⟨hadj, heq⟩ := treePath_eq_cons_parentOfIsTree hK hu
  unfold Thomas.treeDist
  rw [heq, Walk.length_cons]

private theorem iterate_parentOfIsTree_treeDist {ι : Type*} [DecidableEq ι] {K : SimpleGraph ι}
    (hK : K.IsTree) (u : ι) :
    (parentOfIsTree hK)^[Thomas.treeDist hK u (treeRootOfIsTree hK)] u =
      treeRootOfIsTree hK := by
  generalize hd : Thomas.treeDist hK u (treeRootOfIsTree hK) = d
  induction d generalizing u with
  | zero =>
    by_contra hne
    exact absurd hd (ne_of_gt (Thomas.treeDist_pos_of_ne hK hne))
  | succ d ih =>
    have hu : u ≠ treeRootOfIsTree hK := by
      rintro rfl
      rw [Thomas.treeDist_self] at hd
      exact Nat.noConfusion hd
    have hpar_d : Thomas.treeDist hK (parentOfIsTree hK u) (treeRootOfIsTree hK) = d := by
      have := treeDist_parentOfIsTree hK hu
      omega
    rw [Function.iterate_succ_apply]
    exact ih (parentOfIsTree hK u) hpar_d

private theorem parentOfIsTree_eq_of_not_onTreePath {ι : Type*} [DecidableEq ι] {K : SimpleGraph ι}
    (hK : K.IsTree) {u v : ι}
    (hadj : K.Adj u v) (hnot : ¬ Thomas.OnTreePath K v (treeRootOfIsTree hK) u) :
    u ≠ treeRootOfIsTree hK ∧ parentOfIsTree hK u = v := by
  have hu_not_supp : u ∉ (Thomas.treePath hK v (treeRootOfIsTree hK)).support := by
    rwa [← Thomas.onTreePath_iff_mem_treePath hK]
  have hpath : (Walk.cons hadj (Thomas.treePath hK v (treeRootOfIsTree hK))).IsPath := by
    rw [Walk.cons_isPath_iff]
    exact ⟨Thomas.treePath_isPath hK v (treeRootOfIsTree hK), hu_not_supp⟩
  have heq := Thomas.eq_treePath hK _ hpath
  have hu_ne : u ≠ treeRootOfIsTree hK := by
    rintro rfl
    exact hnot (Thomas.onTreePath_right K v (treeRootOfIsTree hK))
  refine ⟨hu_ne, ?_⟩
  unfold parentOfIsTree
  rw [ite_eq_right hu_ne, ← heq, Walk.getVert_cons_succ, Walk.getVert_zero]

private theorem adj_iff_parentOfIsTree {ι : Type*} [DecidableEq ι] {K : SimpleGraph ι}
    (hK : K.IsTree) (u v : ι) :
    K.Adj u v ↔
      (u ≠ treeRootOfIsTree hK ∧ parentOfIsTree hK u = v) ∨
      (v ≠ treeRootOfIsTree hK ∧ parentOfIsTree hK v = u) := by
  constructor
  · intro hadj
    by_cases hnot : ¬ Thomas.OnTreePath K v (treeRootOfIsTree hK) u
    · exact Or.inl (parentOfIsTree_eq_of_not_onTreePath hK hadj hnot)
    · push Not at hnot
      have hnot' : ¬ Thomas.OnTreePath K u (treeRootOfIsTree hK) v := by
        intro hv
        exact hadj.ne (Thomas.onTreePath_antisymm hK
          (Thomas.onTreePath_symm hnot) (Thomas.onTreePath_symm hv))
      exact Or.inr (parentOfIsTree_eq_of_not_onTreePath hK hadj.symm hnot')
  · rintro (⟨hu, rfl⟩ | ⟨hv, rfl⟩)
    · obtain ⟨hadj, _⟩ := treePath_eq_cons_parentOfIsTree hK hu
      exact hadj
    · obtain ⟨hadj, _⟩ := treePath_eq_cons_parentOfIsTree hK hv
      exact hadj.symm

private noncomputable def rootedTreeOfIsTreeFintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : SimpleGraph ι} (hK : K.IsTree) : GM04.RootedTree ι where
  verts := Finset.univ
  root := treeRootOfIsTree hK
  parent := parentOfIsTree hK
  root_mem := Finset.mem_univ _
  parent_mem _ _ := Finset.mem_univ _
  parent_root := by
    change (if treeRootOfIsTree hK = treeRootOfIsTree hK then _ else _) = _
    rw [ite_eq_left rfl]
  exists_iterate_eq_root u _ :=
    ⟨Thomas.treeDist hK u (treeRootOfIsTree hK), iterate_parentOfIsTree_treeDist hK u⟩

private theorem arborescenceUnderlying_rootedTreeOfIsTreeFintype
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : SimpleGraph ι} (hK : K.IsTree) :
    arborescenceUnderlying (rootedTreeOfIsTreeFintype hK) = K := by
  ext u v
  rw [adj_iff_parentOfIsTree hK]
  simp [arborescenceUnderlying, rootedTreeOfIsTreeFintype]

/-- **Graph Minors XVIII, (6.6)** (page 104):
"**6.6.** *Let $\Omega$ be a well-quasi-order, and let $\mathcal{C}$ be a well-behaved class of
rootless partial $\Omega$-patchworks. Let $\mathcal{C}'$ be the class of all rootless, robust
$\Omega$-patchworks $P$ such that there is a rotund, proper tree-decomposition of $\|P\|$ under
which all pieces of $P$ belong to $\mathcal{C}$. Then $\mathcal{C}'$ is well-quasi-ordered by
simulation.*"

Lean uses an infinite ambient edge type to provide fresh edge labels. -/
theorem theorem_6_6_proof [Infinite β] [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω)
    {ι : ℕ → Type*} [∀ i, Fintype (ι i)]
    {𝒞 : Set (PartialPatchwork Ω α β)} (h𝒞 : WellBehaved 𝒞)
    (P : ℕ → GM04.Patchwork Ω α β) (hrootless : ∀ i, IsRootless (P i))
    (hrob : ∀ i, (P i).IsRobust)
    (S : ∀ i, SimpleGraph (ι i)) (σ : ∀ i, ι i → Hypergraph α β)
    (htd : ∀ i, GM10.IsTreeDecomposition (P i).G.toHypergraph (S i) (σ i))
    (hrot : ∀ i, IsRotund (P i).G.toHypergraph (S i) (σ i))
    (hprop : ∀ i, IsProper (P i).G.toHypergraph (S i) (σ i))
    (hpieces : ∀ i u (Q : PartialPatchwork Ω α β),
      IsPiece (toPartialPatchwork (P i)) (S i) (σ i) u Q → Q ∈ 𝒞) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) := by
  classical
  let T : ∀ i, GM04.RootedTree (ι i) := fun i ↦ rootedTreeOfIsTreeFintype (htd i).isTree
  have hT_verts : ∀ i, (T i).verts = Finset.univ := fun _ ↦ rfl
  have hT_S : ∀ i, arborescenceUnderlying (T i) = S i :=
    fun i ↦ arborescenceUnderlying_rootedTreeOfIsTreeFintype (htd i).isTree
  have hex_rooted : ∀ i, ∃ τ : ι i → RootedHypergraph α β,
      IsRootedDecomposition (P i) (T i) τ ∧ ∀ u, (τ u).toHypergraph = σ i u :=
    fun i ↦ theorem_6_4_proof (hrootless i) (hrob i) (htd i) (hrot i) (T i) (hT_verts i) (hT_S i)
  choose τ hdec hσ using hex_rooted
  exact theorem_6_6_of_rootedDecomposition hΩ h𝒞 P hrootless S σ hprop hpieces
    T hT_verts hT_S τ hdec hσ

end GraphMinor.GM18
