/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM10.GraphSubhypergraph
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM10.Section11
import Mathlib.Data.Set.Card

/-!
# Graph Minors XVI, Section 2: Structure Relative to a Tangle

This file formalizes Section 2 ("Structure relative to a tangle", pages 47–48) of N. Robertson and
P. D. Seymour, *Graph Minors. XVI. Excluding a non-planar graph*, J. Combin. Theory Ser. B 89
(2003) 43–76:

- Correspondence between subgraphs/separations/locations/designs/tree-decompositions of a finite
  graph `G` (`GraphMinor.GM16`) and those of `Hypergraph.ofGraph G` (`GraphMinor.GM10`).
- **Graph Minors XVI, (2.1)** (`theorem_2_1`, page 48): if a class of designs `𝒟` is `θ`-pervasive
  in a finite graph `G` (`θ ≥ 1`), then `G` has a tree-decomposition `(T, τ)` over
  `𝒟^{3θ - 2} ∪ ℛ_{4θ - 3}`, deduced from Graph Minors X, (11.1) (`GM10.theorem_11_1`).
- **Graph Minors XVI, (2.2)** (`theorem_2_2`, page 48): if `G` has a tree-decomposition `(T, τ)`
  over a class of designs `𝒟`, then `G` is a tree-structure over the class `𝒟'` of torsos of
  members of `𝒟` (`HasTreeStructureOver (torsosOfClass 𝒟) G`).
- **Graph Minors XVI, (2.3)** (`theorem_2_3`, page 48): if `𝒟` is `θ`-pervasive in a finite graph
  `G` (`θ ≥ 1`), then `G` has a tree-structure over the class of graphs `G'` that either have
  `|V(G')| ≤ 4θ - 3` or are loose `(≤ 3θ - 2)`-vertex extensions (`IsLooseVertexExtension`) of
  torsos of members of `𝒟`.
-/

@[expose] public section

namespace GraphMinor.GM16

open Set Function Graph SimpleGraph Hypergraph
open GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15

universe u v

variable {α : Type u} {β : Type v}

/-! ## Correspondence between `Graph` and `Hypergraph.ofGraph` -/

export GM10 (subgraphOfSubhypergraph vertexSet_subgraphOfSubhypergraph
  subgraphOfSubhypergraph_le edgeSet_subgraphOfSubhypergraph subgraphOfSubhypergraph_mono
  ofGraph_subgraphOfSubhypergraph subgraphOfSubhypergraph_ofGraph)

/-! ## Proof of Graph Minors XVI, (2.1) (page 48) -/

/-- **Graph Minors XVI, (2.1)** (page 48):
"For any $\theta \ge 1$, let $\mathscr{D}$ be a class of designs which is $\theta$-pervasive in a
graph $G$. Then $G$ has a tree-decomposition $(T, \tau)$ such that for each $t \in V(T)$, the
design of $t$ in $(T, \tau)$ belongs to $\mathscr{D}^{3\theta-2} \cup \mathscr{R}_{4\theta-3}$." -/
theorem theorem_2_1_proof {G : Graph α β} {θ : ℕ} {𝒟 : Set (GraphDesign α β)}
    (hV : V(G).Finite) (hE : E(G).Finite) (hθ : 1 ≤ θ)
    (hperv : IsGraphPervasive G θ 𝒟) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Graph α β),
      IsGraphTreeDecompositionOver G
        (graphEnlargementClass 𝒟 (3 * θ - 2) ∪ smallGraphDesignClass (4 * θ - 3)) T τ := by
  let G_H := Hypergraph.ofGraph G hV hE
  let 𝒮 : Set (Design α β) :=
    {d_H | d_H.1 ≤ G_H ∧ IsDesign d_H ∧ (subgraphOfSubhypergraph G d_H.1, d_H.2) ∈ 𝒟}
  have hperv_H : GM10.IsPervasive G_H θ 𝒮 := by
    intro G'_H hG'_le θ' 𝒯 hθ' h𝒯
    let G' := subgraphOfSubhypergraph G G'_H
    have hG'_le_G : G' ≤ G := subgraphOfSubhypergraph_le hG'_le
    have hV' : V(G').Finite := G'_H.vertexSet_finite
    have hE' : E(G').Finite :=
      G'_H.edgeSet_finite.subset (by rw [edgeSet_subgraphOfSubhypergraph hG'_le])
    have hof_G' : Hypergraph.ofGraph G' hV' hE' = G'_H := ofGraph_subgraphOfSubhypergraph hG'_le
    have h𝒯_graph : IsGraphTangle G' θ' 𝒯 := ⟨hV', hE', hof_G'.symm ▸ h𝒯⟩
    obtain ⟨ℒ, hloc, hℒ_mem, hdes⟩ := hperv hG'_le_G hθ' h𝒯_graph
    let ℒ_H : Set (Hypergraph α β × Hypergraph α β) :=
      {p_H ∈ 𝒯 | ∃ p ∈ ℒ, SeparationOfGraphSep G' p.1 p.2 p_H.1 p_H.2}
    have hℒ_H_sub : ℒ_H ⊆ 𝒯 := fun _ h => h.1
    have hℒ_H_loc : GM10.IsLocation G'_H ℒ_H := by
      refine ⟨fun p_H hp_H => h𝒯.isSeparation hp_H.1, ?_⟩
      rintro p₁ ⟨hp₁𝒯, p₁_G, hp₁ℒ, hsep₁⟩ p₂ ⟨hp₂𝒯, p₂_G, hp₂ℒ, hsep₂⟩ hne
      have hp₁_le : p₁.1 ≤ G'_H := (h𝒯.isSeparation hp₁𝒯).left_le
      have hp₂_le : p₂.2 ≤ G'_H := (h𝒯.isSeparation hp₂𝒯).right_le
      have hne_G : p₁_G ≠ p₂_G := by
        rintro rfl
        apply hne
        ext : 1
        · exact GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hp₁_le
            (h𝒯.isSeparation hp₂𝒯).left_le
            (hsep₁.2.1.trans hsep₂.2.1.symm) (hsep₁.2.2.1.trans hsep₂.2.2.1.symm)
        · exact GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (h𝒯.isSeparation hp₁𝒯).right_le
            hp₂_le (hsep₁.2.2.2.1.trans hsep₂.2.2.2.1.symm)
            (hsep₁.2.2.2.2.trans hsep₂.2.2.2.2.symm)
      have hle_G : p₁_G.1 ≤ p₂_G.2 := hloc.left_le_right hp₁ℒ hp₂ℒ hne_G
      rw [GM10.le_iff_of_le hp₁_le hp₂_le, hsep₁.2.1, hsep₂.2.2.2.1,
        hsep₁.2.2.1, hsep₂.2.2.2.2]
      exact ⟨hle_G.vertexSet_mono, hle_G.edgeSet_mono⟩
    have hcore_le : GM10.locationCore G'_H ℒ_H ≤ G_H :=
      (GM10.locationCore_le fun _ hp => hℒ_H_loc.isSeparation hp).trans hG'_le
    have hcore_eq : subgraphOfSubhypergraph G (GM10.locationCore G'_H ℒ_H) =
        graphLocationCore G' ℒ := by
      have h1 : subgraphOfSubhypergraph G (GM10.locationCore G'_H ℒ_H) ≤ G :=
        subgraphOfSubhypergraph_le hcore_le
      have hsub : {x ∈ V(G') | ∀ p ∈ ℒ, x ∈ V(p.2)} ⊆ V(G') := fun _ h => h.1
      have h2 : graphLocationCore G' ℒ ≤ G :=
        (restrict_le.trans (G'.induce_le hsub)).trans hG'_le_G
      refine (Compatible.of_le_le h1 h2).ext ?_ ?_
      · ext v
        simp only [vertexSet_subgraphOfSubhypergraph, GM10.locationCore, graphLocationCore,
          vertexSet_restrict, vertexSet_induce, Set.mem_ofPred_eq, G']
        refine and_congr_right fun hvG' => ⟨fun h p hp => ?_, fun h p_H hp_H => ?_⟩
        · obtain ⟨p_H, hp_H𝒯, hsep⟩ := hℒ_mem p hp
          rw [← hsep.2.2.2.1]
          exact h p_H ⟨hp_H𝒯, p, hp, hsep⟩
        · obtain ⟨_, p, hp, hsep⟩ := hp_H
          rw [hsep.2.2.2.1]
          exact h p hp
      · ext e
        rw [edgeSet_subgraphOfSubhypergraph hcore_le]
        simp only [GM10.locationCore, graphLocationCore, edgeSet_restrict, Graph.edgeSet_induce,
          Set.mem_ofPred_eq, mem_inter_iff]
        rw [edgeSet_subgraphOfSubhypergraph hG'_le]
        constructor
        · rintro ⟨heG', hall⟩
          have heG : e ∈ E(G) := hG'_le.edgeSet_subset heG'
          obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet heG
          have hlink' : G'.IsLink e x y :=
            (hG'_le_G.isLink_iff (by rwa [edgeSet_subgraphOfSubhypergraph hG'_le])).mpr hlink
          refine ⟨⟨x, y, hlink', ⟨hlink'.left_mem, fun p hp => ?_⟩,
            ⟨hlink'.right_mem, fun p hp => ?_⟩⟩, heG', fun p hp => ?_⟩
          · obtain ⟨p_H, hp_H𝒯, hsep⟩ := hℒ_mem p hp
            have he_p : e ∈ E(p.2) := hsep.2.2.2.2 ▸ hall p_H ⟨hp_H𝒯, p, hp, hsep⟩
            exact (((hloc.isSeparation hp).2.1.isLink_iff he_p).mpr hlink').left_mem
          · obtain ⟨p_H, hp_H𝒯, hsep⟩ := hℒ_mem p hp
            have he_p : e ∈ E(p.2) := hsep.2.2.2.2 ▸ hall p_H ⟨hp_H𝒯, p, hp, hsep⟩
            exact (((hloc.isSeparation hp).2.1.isLink_iff he_p).mpr hlink').right_mem
          · obtain ⟨p_H, hp_H𝒯, hsep⟩ := hℒ_mem p hp
            rw [← hsep.2.2.2.2]
            exact hall p_H ⟨hp_H𝒯, p, hp, hsep⟩
        · rintro ⟨_, heG', hall⟩
          refine ⟨heG', fun p_H ⟨_, p, hp, hsep⟩ => ?_⟩
          rw [hsep.2.2.2.2]
          exact hall p hp
    have hM_eq : (GM10.locationDesign G'_H ℒ_H).2 = (graphLocationDesign G' ℒ).2 := by
      ext X
      simp only [GM10.locationDesign, graphLocationDesign, mem_image, GM10.inter_vertexSet]
      constructor
      · rintro ⟨p_H, ⟨_, p, hp, hsep⟩, rfl⟩
        exact ⟨p, hp, by rw [hsep.2.1, hsep.2.2.2.1]⟩
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨p_H, hp_H𝒯, hsep⟩ := hℒ_mem p hp
        exact ⟨p_H, ⟨hp_H𝒯, p, hp, hsep⟩, by rw [hsep.2.1, hsep.2.2.2.1]⟩
    refine ⟨ℒ_H, hℒ_H_loc, hℒ_H_sub, hcore_le, hℒ_H_loc.isDesign_locationDesign, ?_⟩
    change (subgraphOfSubhypergraph G (GM10.locationCore G'_H ℒ_H),
      (GM10.locationDesign G'_H ℒ_H).2) ∈ 𝒟
    rwa [hcore_eq, hM_eq]
  obtain ⟨ι, hfin, T, τ_H, hover⟩ := GM10.theorem_11_1_proof hθ hperv_H
  let τ : ι → Graph α β := fun t => subgraphOfSubhypergraph G (τ_H t)
  refine ⟨ι, hfin, T, τ, ⟨⟨hover.1.isTree, fun t => subgraphOfSubhypergraph_le (hover.1.le t),
    ?_, ?_, ?_, ?_⟩, ?_⟩⟩
  · ext v
    simp only [mem_iUnion, τ, vertexSet_subgraphOfSubhypergraph]
    have hV_eq := congrArg Hypergraph.vertexSet hover.1.biUnion_eq
    simpa [Hypergraph.biUnion, G_H, Hypergraph.ofGraph] using Set.ext_iff.mp hV_eq v
  · ext e
    simp only [mem_iUnion, τ]
    have h_congr : (∃ i, e ∈ E(subgraphOfSubhypergraph G (τ_H i))) ↔
        (∃ i, e ∈ (τ_H i).edgeSet) :=
      exists_congr fun i => by rw [edgeSet_subgraphOfSubhypergraph (hover.1.le i)]
    rw [h_congr]
    have hE_eq := congrArg Hypergraph.edgeSet hover.1.biUnion_eq
    simpa [Hypergraph.biUnion, G_H, Hypergraph.ofGraph] using Set.ext_iff.mp hE_eq e
  · intro t₁ t₂ hne
    dsimp only [τ]
    rw [edgeSet_subgraphOfSubhypergraph (hover.1.le t₁),
      edgeSet_subgraphOfSubhypergraph (hover.1.le t₂), Set.disjoint_iff_inter_eq_empty]
    exact hover.1.edgeSet_inter_eq hne
  · intro t₁ t₂ t₃ p hp ht₂
    dsimp only [τ]
    rw [vertexSet_subgraphOfSubhypergraph, vertexSet_subgraphOfSubhypergraph,
      vertexSet_subgraphOfSubhypergraph]
    intro v hv
    have hon : GM10.OnTreePath T t₁ t₃ t₂ := by
      intro w hw
      have heq_path : (⟨w, hw⟩ : T.Path t₁ t₃) = ⟨p, hp⟩ :=
        @Subsingleton.elim _ (hover.1.isTree.isAcyclic.subsingleton_path t₁ t₃) _ _
      have heq_walk : w = p := congrArg Subtype.val heq_path
      rwa [heq_walk]
    exact (hover.1.inter_le hon).vertexSet_subset hv
  · intro t₀
    have hdes_eq : graphVertexDesign T τ t₀ =
        (subgraphOfSubhypergraph G (GM10.vertexDesign T τ_H t₀).1,
         (GM10.vertexDesign T τ_H t₀).2) := rfl
    rw [hdes_eq]
    have hτ₀_le : (GM10.vertexDesign T τ_H t₀).1 ≤ G_H := hover.1.le t₀
    have hE_τ₀ : E(subgraphOfSubhypergraph G (GM10.vertexDesign T τ_H t₀).1) ⊆
        (τ_H t₀).edgeSet := by
      rw [edgeSet_subgraphOfSubhypergraph hτ₀_le]
      exact subset_rfl
    rcases hover.2 t₀ with ⟨d_H, ⟨hd_H_le, hd_H_des, hd_mem⟩, Z, hZ_card, henl⟩ | ⟨hdes, hcard⟩
    · left
      refine ⟨(subgraphOfSubhypergraph G d_H.1, d_H.2), hd_mem, Z, hZ_card, ?_⟩
      refine ⟨⟨d_H.1.vertexSet_finite,
        d_H.1.edgeSet_finite.subset (by rw [edgeSet_subgraphOfSubhypergraph hd_H_le]),
        hd_H_des⟩,
        ⟨(τ_H t₀).vertexSet_finite, (τ_H t₀).edgeSet_finite.subset hE_τ₀, henl.isDesign'⟩,
        henl.subset_vertexSet,
        subgraphOfSubhypergraph_mono hd_H_le hτ₀_le henl.le,
        henl.sdiff_subset, ?_, henl.inter_mem⟩
      rw [edgeSet_subgraphOfSubhypergraph hτ₀_le, edgeSet_subgraphOfSubhypergraph hd_H_le]
      exact henl.edgeSet_subset
    · right
      exact ⟨⟨(τ_H t₀).vertexSet_finite, (τ_H t₀).edgeSet_finite.subset hE_τ₀, hdes⟩, hcard⟩

/-! ## Proof of Graph Minors XVI, (2.2) (page 48) -/

/-- Every design `d = (H, M)` has `H` itself as a torso. -/
theorem self_isTorsoOfDesign (d : GraphDesign α β) : IsTorsoOfDesign d d.1 :=
  ⟨rfl, le_rfl, fun _ h => (h.2 h.1).elim⟩

/-- Monotonicity of `HasTreeStructureOver` in the base class `𝒞`. -/
theorem HasTreeStructureOver.mono {𝒞₁ 𝒞₂ : Set (Graph α β)} (hsub : 𝒞₁ ⊆ 𝒞₂)
    {G : Graph α β} (h : HasTreeStructureOver 𝒞₁ G) :
    HasTreeStructureOver 𝒞₂ G := by
  induction h with
  | base hG => exact HasTreeStructureOver.base (hsub hG)
  | cliqueSum hsum _ _ ih₁ ih₂ => exact HasTreeStructureOver.cliqueSum hsum ih₁ ih₂

/-- A complete graph on a finite vertex set has a finite edge set. -/
theorem IsCompleteGraphOn.edgeSet_finite {K : Graph α β} {W : Set α}
    (hK : IsCompleteGraphOn K W) (hW : W.Finite) : E(K).Finite := by
  classical
  have : Fintype W := hW.fintype
  let f : W × W → Option β := fun p =>
    if h : ∃ e, K.IsLink e p.1.1 p.2.1 then some h.choose else none
  have hsub : Option.some '' E(K) ⊆ Set.range f := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet he
    have hx : x ∈ W := hK.1 ▸ hlink.left_mem
    have hy : y ∈ W := hK.1 ▸ hlink.right_mem
    have hxy : x ≠ y := fun h => hK.2.1 e x (h ▸ hlink)
    obtain ⟨_, _, huniq⟩ := hK.2.2 x hx y hy hxy
    have hex : ∃ e', K.IsLink e' x y := ⟨e, hlink⟩
    refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
    dsimp [f]
    rw [dite_eq_left hex]
    exact congrArg Option.some ((huniq hex.choose hex.choose_spec).trans (huniq e hlink).symm)
  exact ((Set.finite_range f).subset hsub).of_finite_image (Option.some_injective β).injOn

/-- If `G` has finite vertex and edge sets and `IsCliqueSum G G₁ G₂`, then `G₁` and `G₂` also have
finite vertex and edge sets. -/
theorem IsCliqueSum.finite_of_finite {G G₁ G₂ : Graph α β}
    (hsum : IsCliqueSum G G₁ G₂) (hV : V(G).Finite) (hE : E(G).Finite) :
    (V(G₁).Finite ∧ E(G₁).Finite) ∧ (V(G₂).Finite ∧ E(G₂).Finite) := by
  rcases hsum with ⟨H₁, H₂, K, hsep, hK, hsep₁, hsep₂⟩
  have hVH₁ : V(H₁).Finite := hV.subset hsep.1.vertexSet_mono
  have hVH₂ : V(H₂).Finite := hV.subset hsep.2.1.vertexSet_mono
  have hVK : V(K).Finite := by
    rw [hK.1]
    exact hVH₁.subset inter_subset_left
  have hEK : E(K).Finite := hK.edgeSet_finite (hVH₁.subset inter_subset_left)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [← hsep₁.2.2.1]; exact hVH₁.union hVK
  · rw [← hsep₁.2.2.2.1]; exact (hE.subset hsep.1.edgeSet_mono).union hEK
  · rw [← hsep₂.2.2.1]; exact hVH₂.union hVK
  · rw [← hsep₂.2.2.2.1]; exact (hE.subset hsep.2.1.edgeSet_mono).union hEK

/-- Every base piece in a tree-structure of a finite graph has finite vertex and edge sets. -/
theorem HasTreeStructureOver.with_finite {𝒞 : Set (Graph α β)} {G : Graph α β}
    (h : HasTreeStructureOver 𝒞 G) (hV : V(G).Finite) (hE : E(G).Finite) :
    HasTreeStructureOver {G' ∈ 𝒞 | V(G').Finite ∧ E(G').Finite} G := by
  induction h with
  | base hG => exact HasTreeStructureOver.base ⟨hG, hV, hE⟩
  | cliqueSum hsum _ _ ih₁ ih₂ =>
    obtain ⟨⟨hV₁, hE₁⟩, ⟨hV₂, hE₂⟩⟩ := hsum.finite_of_finite hV hE
    exact HasTreeStructureOver.cliqueSum hsum (ih₁ hV₁ hE₁) (ih₂ hV₂ hE₂)

/-- The subgraph of `G₀` with vertex set `W` and edge set `F`. -/
def subgraphOfVE (G₀ : Graph α β) (W : Set α) (F : Set β) : Graph α β :=
  (G₀.induce W).restrict F

@[simp]
theorem vertexSet_subgraphOfVE (G₀ : Graph α β) (W : Set α) (F : Set β) :
    V(subgraphOfVE G₀ W F) = W := rfl

theorem subgraphOfVE_le {G₀ : Graph α β} {W : Set α} {F : Set β} (hW : W ⊆ V(G₀)) :
    subgraphOfVE G₀ W F ≤ G₀ :=
  restrict_le.trans (G₀.induce_le hW)

theorem edgeSet_subgraphOfVE {G₀ : Graph α β} {W : Set α} {F : Set β}
    (hF : ∀ e ∈ F, ∃ x ∈ W, ∃ y ∈ W, G₀.IsLink e x y) :
    E(subgraphOfVE G₀ W F) = F := by
  ext e
  simp only [subgraphOfVE, edgeSet_restrict, mem_inter_iff, Graph.edgeSet_induce]
  refine ⟨fun h => h.2, fun he => ⟨?_, he⟩⟩
  obtain ⟨x, hx, y, hy, hlink⟩ := hF e he
  exact ⟨x, y, hlink, hx, hy⟩

theorem isGraphSeparation_subgraphOfVE {G₀ : Graph α β}
    {W₀ W₁ W₂ : Set α} {F₀ F₁ F₂ : Set β}
    (hW₀ : W₀ ⊆ V(G₀)) (hW₁ : W₁ ⊆ V(G₀)) (hW₂ : W₂ ⊆ V(G₀))
    (hF₀ : ∀ e ∈ F₀, ∃ x ∈ W₀, ∃ y ∈ W₀, G₀.IsLink e x y)
    (hF₁ : ∀ e ∈ F₁, ∃ x ∈ W₁, ∃ y ∈ W₁, G₀.IsLink e x y)
    (hF₂ : ∀ e ∈ F₂, ∃ x ∈ W₂, ∃ y ∈ W₂, G₀.IsLink e x y)
    (hW_union : W₁ ∪ W₂ = W₀) (hF_union : F₁ ∪ F₂ = F₀) (hF_disj : Disjoint F₁ F₂) :
    IsGraphSeparation (subgraphOfVE G₀ W₀ F₀)
      (subgraphOfVE G₀ W₁ F₁) (subgraphOfVE G₀ W₂ F₂) := by
  have hle₀ := subgraphOfVE_le (F := F₀) hW₀
  have hle₁ := subgraphOfVE_le (F := F₁) hW₁
  have hle₂ := subgraphOfVE_le (F := F₂) hW₂
  have hE₀ := edgeSet_subgraphOfVE hF₀
  have hE₁ := edgeSet_subgraphOfVE hF₁
  have hE₂ := edgeSet_subgraphOfVE hF₂
  refine ⟨?_, ?_, hW_union, ?_, ?_⟩
  · rw [(Compatible.of_le_le hle₁ hle₀).le_iff, hE₁, hE₀, ← hW_union, ← hF_union]
    exact ⟨subset_union_left, subset_union_left⟩
  · rw [(Compatible.of_le_le hle₂ hle₀).le_iff, hE₂, hE₀, ← hW_union, ← hF_union]
    exact ⟨subset_union_right, subset_union_right⟩
  · rw [hE₁, hE₂, hE₀, hF_union]
  · rw [hE₁, hE₂]
    exact hF_disj

private theorem exists_torso_clique_extension {ι : Type*} [Finite ι]
    {G : Graph α (β ⊕ ℕ)} (τ : ι → Graph α (β ⊕ ℕ)) (hV : V(G).Finite) (hE : E(G).Finite) :
    let adhesionSet (eT : Sym2 ι) : Set α := {v ∈ V(G) | ∀ t ∈ eT, v ∈ V(τ t)}
    ∃ (G_full : Graph α (β ⊕ ℕ)) (cliqueEdges : Sym2 ι → Set (β ⊕ ℕ)),
      V(G_full) = V(G) ∧ G ≤ G_full ∧
      (∀ (eT : Sym2 ι) (e : β ⊕ ℕ), e ∈ cliqueEdges eT →
        ∃ u ∈ adhesionSet eT, ∃ v ∈ adhesionSet eT, G_full.IsLink e u v) ∧
      (∀ eT, Disjoint E(G) (cliqueEdges eT)) ∧
      (∀ {eT₁ eT₂}, eT₁ ≠ eT₂ → Disjoint (cliqueEdges eT₁) (cliqueEdges eT₂)) ∧
      ∀ eT, IsCompleteGraphOn (subgraphOfVE G_full (adhesionSet eT) (cliqueEdges eT))
        (adhesionSet eT) := by
  classical
  intro adhesionSet
  let indexFintype := Fintype.ofFinite ι
  let _ : Fintype V(G) := hV.fintype
  have hN_fin : (Sum.inr ⁻¹' E(G) : Set ℕ).Finite :=
    hE.preimage Sum.inr_injective.injOn
  let B₀ : ℕ := hN_fin.toFinset.sup id + 1
  have hB₀_notMem : ∀ n : ℕ, (Sum.inr (B₀ + n) : β ⊕ ℕ) ∉ E(G) := by
    intro n hmem
    have hn_mem : B₀ + n ∈ hN_fin.toFinset := hN_fin.mem_toFinset.mpr hmem
    have hle : B₀ + n ≤ hN_fin.toFinset.sup id := Finset.le_sup (f := id) hn_mem
    omega
  let enc := Fintype.equivFin (Sym2 ι × Sym2 V(G))
  let freshEdge (eT : Sym2 ι) (x y : V(G)) : β ⊕ ℕ :=
    Sum.inr (B₀ + (enc (eT, s(x, y))).1)
  have hfresh_symm : ∀ (eT : Sym2 ι) (x y : V(G)), freshEdge eT x y = freshEdge eT y x := by
    intro eT x y
    dsimp [freshEdge]
    rw [Sym2.eq_swap]
  have hfresh_notMem : ∀ (eT : Sym2 ι) (x y : V(G)), freshEdge eT x y ∉ E(G) :=
    fun eT x y => hB₀_notMem _
  have hfresh_inj : ∀ {eT₁ eT₂ : Sym2 ι} {x₁ y₁ x₂ y₂ : V(G)},
      freshEdge eT₁ x₁ y₁ = freshEdge eT₂ x₂ y₂ ↔ eT₁ = eT₂ ∧ s(x₁, y₁) = s(x₂, y₂) := by
    intro eT₁ eT₂ x₁ y₁ x₂ y₂
    constructor
    · intro h
      have h1 : B₀ + (enc (eT₁, s(x₁, y₁))).1 = B₀ + (enc (eT₂, s(x₂, y₂))).1 :=
        Sum.inr.inj h
      have h2 : enc (eT₁, s(x₁, y₁)) = enc (eT₂, s(x₂, y₂)) :=
        Fin.ext (Nat.add_left_cancel h1)
      exact Prod.mk.inj (enc.injective h2)
    · rintro ⟨rfl, h⟩
      dsimp [freshEdge]
      rw [h]
  let G_full : Graph α (β ⊕ ℕ) :=
    { vertexSet := V(G)
      edgeSet := E(G) ∪
        {e | ∃ (eT : Sym2 ι) (u v : α) (hu : u ∈ V(G)) (hv : v ∈ V(G)),
          u ≠ v ∧ e = freshEdge eT ⟨u, hu⟩ ⟨v, hv⟩}
      IsLink := fun e u v =>
        G.IsLink e u v ∨
          ∃ (eT : Sym2 ι) (hu : u ∈ V(G)) (hv : v ∈ V(G)),
            u ≠ v ∧ e = freshEdge eT ⟨u, hu⟩ ⟨v, hv⟩
      isLink_symm := fun e _ => ⟨by
        rintro u v (h | ⟨eT, hu, hv, hne, rfl⟩)
        · exact Or.inl h.symm
        · exact Or.inr ⟨eT, hv, hu, hne.symm, hfresh_symm eT ⟨u, hu⟩ ⟨v, hv⟩⟩⟩
      eq_or_eq_of_isLink_of_isLink := by
        rintro e u v z w (h1 | ⟨eT₁, hu, hv, _, rfl⟩) (h2 | ⟨eT₂, hz, hw, _, he₂⟩)
        · exact G.eq_or_eq_of_isLink_of_isLink h1 h2
        · exact (hfresh_notMem eT₂ ⟨z, hz⟩ ⟨w, hw⟩ (he₂ ▸ h1.edge_mem)).elim
        · exact (hfresh_notMem eT₁ ⟨u, hu⟩ ⟨v, hv⟩ h2.edge_mem).elim
        · rcases Sym2.eq_iff.mp (hfresh_inj.mp he₂).2 with ⟨huz, _⟩ | ⟨huw, _⟩
          · exact Or.inl (congrArg Subtype.val huz)
          · exact Or.inr (congrArg Subtype.val huw)
      edge_mem_iff_exists_isLink := fun e => by
        constructor
        · rintro (heG | ⟨eT, u, v, hu, hv, hne, rfl⟩)
          · obtain ⟨u, v, h⟩ := exists_isLink_of_mem_edgeSet heG
            exact ⟨u, v, Or.inl h⟩
          · exact ⟨u, v, Or.inr ⟨eT, hu, hv, hne, rfl⟩⟩
        · rintro ⟨u, v, h | ⟨eT, hu, hv, hne, rfl⟩⟩
          · exact Or.inl h.edge_mem
          · exact Or.inr ⟨eT, u, v, hu, hv, hne, rfl⟩
      left_mem_of_isLink := by
        rintro e u v (h | ⟨_, hu, _⟩)
        · exact h.left_mem
        · exact hu }
  have hG_le_full : G ≤ G_full :=
    ⟨subset_rfl, fun _ _ _ h => Or.inl h⟩
  let cliqueEdges (eT : Sym2 ι) : Set (β ⊕ ℕ) :=
    {e | ∃ (u v : α) (hu : u ∈ adhesionSet eT) (hv : v ∈ adhesionSet eT),
      u ≠ v ∧ e = freshEdge eT ⟨u, hu.1⟩ ⟨v, hv.1⟩}
  have hW_K : ∀ eT : Sym2 ι, adhesionSet eT ⊆ V(G_full) :=
    fun _ _ h => h.1
  have hF_K : ∀ (eT : Sym2 ι) (e : β ⊕ ℕ), e ∈ cliqueEdges eT →
      ∃ u ∈ adhesionSet eT, ∃ v ∈ adhesionSet eT, G_full.IsLink e u v := by
    rintro eT e ⟨u, v, hu, hv, hne, rfl⟩
    exact ⟨u, hu, v, hv, Or.inr ⟨eT, hu.1, hv.1, hne, rfl⟩⟩
  let K (eT : Sym2 ι) : Graph α (β ⊕ ℕ) :=
    subgraphOfVE G_full (adhesionSet eT) (cliqueEdges eT)
  have hK_le : ∀ eT : Sym2 ι, K eT ≤ G_full := fun eT => subgraphOfVE_le (hW_K eT)
  have hK_E : ∀ eT : Sym2 ι, E(K eT) = cliqueEdges eT :=
    fun eT => edgeSet_subgraphOfVE (hF_K eT)
  have hdisj_G_K : ∀ eT : Sym2 ι, Disjoint E(G) (cliqueEdges eT) := by
    intro eT
    refine Set.disjoint_left.mpr ?_
    rintro e heG ⟨u, v, hu, hv, _, rfl⟩
    exact hfresh_notMem eT ⟨u, hu.1⟩ ⟨v, hv.1⟩ heG
  have hdisj_K : ∀ {eT₁ eT₂ : Sym2 ι}, eT₁ ≠ eT₂ →
      Disjoint (cliqueEdges eT₁) (cliqueEdges eT₂) := by
    intro eT₁ eT₂ hne
    refine Set.disjoint_left.mpr ?_
    rintro e ⟨u₁, v₁, hu₁, hv₁, _, rfl⟩ ⟨u₂, v₂, hu₂, hv₂, _, he⟩
    exact hne (hfresh_inj.mp he).1
  have hK_complete : ∀ eT : Sym2 ι, IsCompleteGraphOn (K eT) (adhesionSet eT) := by
    intro eT
    refine ⟨rfl, ?_, ?_⟩
    · intro e x hloop
      have heK : e ∈ cliqueEdges eT := hK_E eT ▸ hloop.edge_mem
      have hlink_full : G_full.IsLink e x x := hloop.mono (hK_le eT)
      rcases hlink_full with hG | ⟨eT', hx, _, hne, _⟩
      · exact Set.disjoint_left.mp (hdisj_G_K eT) hG.edge_mem heK
      · exact hne rfl
    · intro x hx y hy hxy
      refine ⟨freshEdge eT ⟨x, hx.1⟩ ⟨y, hy.1⟩, ?_, ?_⟩
      · have he_mem : freshEdge eT ⟨x, hx.1⟩ ⟨y, hy.1⟩ ∈ E(K eT) := by
          rw [hK_E eT]
          exact ⟨x, y, hx, hy, hxy, rfl⟩
        exact ((hK_le eT).isLink_iff he_mem).mpr (Or.inr ⟨eT, hx.1, hy.1, hxy, rfl⟩)
      · intro e hlink
        have heK : e ∈ cliqueEdges eT := hK_E eT ▸ hlink.edge_mem
        have hlink_full : G_full.IsLink e x y := hlink.mono (hK_le eT)
        rcases hlink_full with hG | ⟨eT', hx', hy', _, rfl⟩
        · exact (Set.disjoint_left.mp (hdisj_G_K eT) hG.edge_mem heK).elim
        · rcases heK with ⟨u, v, hu, hv, _, he⟩
          have heT_eq : eT' = eT := (hfresh_inj.mp he).1
          subst heT_eq
          rfl
  exact ⟨G_full, cliqueEdges, rfl, hG_le_full, hF_K, hdisj_G_K, hdisj_K, hK_complete⟩

private theorem boundary_edges_of_leaf {ι : Type*} {T : SimpleGraph ι}
    [DecidableEq ι] {s : Finset ι} {t₀ t₁ : ι} (ht₀_s : t₀ ∈ s) (ht₁_s : t₁ ∈ s)
    (hadj_t₀t₁ : T.Adj t₀ t₁) (ht₁_uniq : ∀ u ∈ s, T.Adj t₀ u → u = t₁) :
    let boundaryEdges (s : Finset ι) : Set (Sym2 ι) :=
      {eT | ∃ t₁ ∈ s, ∃ t₂ ∉ s, T.Adj t₁ t₂ ∧ eT = s(t₁, t₂)}
    let s' := s.erase t₀
    let e₀ : Sym2 ι := s(t₀, t₁)
    let B₁ := boundaryEdges {t₀} \ {e₀}
    let B₂ := boundaryEdges s' \ {e₀}
    e₀ ∈ boundaryEdges {t₀} ∧ e₀ ∈ boundaryEdges s' ∧ boundaryEdges s = B₁ ∪ B₂ ∧
      Disjoint B₁ B₂ := by
  intro boundaryEdges s' e₀ B₁ B₂
  have ht₀_ne_t₁ := hadj_t₀t₁.ne
  have ht₁_s' : t₁ ∈ s' := Finset.mem_erase.mpr ⟨ht₀_ne_t₁.symm, ht₁_s⟩
  have he₀_mem_bd₁ : e₀ ∈ boundaryEdges {t₀} :=
    ⟨t₀, Finset.mem_singleton_self t₀, t₁, Finset.notMem_singleton.mpr ht₀_ne_t₁.symm,
      hadj_t₀t₁, rfl⟩
  have he₀_mem_bd₂ : e₀ ∈ boundaryEdges s' :=
    ⟨t₁, ht₁_s', t₀, Finset.notMem_erase t₀ s, hadj_t₀t₁.symm, Sym2.eq_swap⟩
  have hB₁_char : ∀ eT : Sym2 ι,
      eT ∈ B₁ ↔ ∃ w ∉ s, T.Adj t₀ w ∧ eT = s(t₀, w) := by
    intro eT
    simp only [B₁, boundaryEdges, mem_sdiff, mem_ofPred_eq, Finset.mem_singleton,
      mem_singleton_iff]
    constructor
    · rintro ⟨⟨u, rfl, w, hw_ne, hadj, rfl⟩, hne_e₀⟩
      refine ⟨w, fun hws => ?_, hadj, rfl⟩
      have hw_eq : w = t₁ := ht₁_uniq w hws hadj
      exact hne_e₀ (hw_eq ▸ rfl)
    · rintro ⟨w, hws, hadj, rfl⟩
      refine ⟨⟨t₀, rfl, w, fun h => hws (h ▸ ht₀_s), hadj, rfl⟩, ?_⟩
      intro heq
      rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hws ht₁_s
      · exact hws ht₀_s
  have hB₂_char : ∀ eT : Sym2 ι,
      eT ∈ B₂ ↔ ∃ u ∈ s', ∃ w ∉ s, T.Adj u w ∧ eT = s(u, w) := by
    intro eT
    simp only [B₂, boundaryEdges, mem_sdiff, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨⟨u, hu_s', w, hw_s', hadj, rfl⟩, hne_e₀⟩
      refine ⟨u, hu_s', w, fun hws => ?_, hadj, rfl⟩
      have hw_t₀ : w = t₀ := by
        by_contra hw_ne
        exact hw_s' (Finset.mem_erase.mpr ⟨hw_ne, hws⟩)
      subst hw_t₀
      have hu_t₁ : u = t₁ := ht₁_uniq u (Finset.mem_of_mem_erase hu_s') hadj.symm
      subst hu_t₁
      exact hne_e₀ Sym2.eq_swap
    · rintro ⟨u, hu_s', w, hws, hadj, rfl⟩
      refine ⟨⟨u, hu_s', w, fun h => hws (Finset.mem_of_mem_erase h), hadj, rfl⟩, ?_⟩
      intro heq
      rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hws ht₁_s
      · exact hws ht₀_s
  have hbd_s : boundaryEdges s = B₁ ∪ B₂ := by
    ext eT
    rw [mem_union, hB₁_char, hB₂_char]
    simp only [boundaryEdges, mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu_s, w, hws, hadj, rfl⟩
      by_cases hu_t₀ : u = t₀
      · subst hu_t₀
        exact Or.inl ⟨w, hws, hadj, rfl⟩
      · exact Or.inr ⟨u, Finset.mem_erase.mpr ⟨hu_t₀, hu_s⟩, w, hws, hadj, rfl⟩
    · rintro (⟨w, hws, hadj, rfl⟩ | ⟨u, hu_s', w, hws, hadj, rfl⟩)
      · exact ⟨t₀, ht₀_s, w, hws, hadj, rfl⟩
      · exact ⟨u, Finset.mem_of_mem_erase hu_s', w, hws, hadj, rfl⟩
  have hB₁_B₂_disj : Disjoint B₁ B₂ := by
    refine Set.disjoint_left.mpr ?_
    intro eT h1 h2
    obtain ⟨w₁, hw₁s, _, rfl⟩ := (hB₁_char eT).mp h1
    obtain ⟨u, hu_s', w₂, hw₂s, _, heq⟩ := (hB₂_char _).mp h2
    rcases Sym2.eq_iff.mp heq with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Finset.ne_of_mem_erase hu_s' rfl
    · exact hw₂s ht₀_s
  exact ⟨he₀_mem_bd₁, he₀_mem_bd₂, hbd_s, hB₁_B₂_disj⟩

private theorem singleton_piece_is_torso {ι : Type*}
    {T : SimpleGraph ι} {τ : ι → Graph α (β ⊕ ℕ)} {G_full : Graph α (β ⊕ ℕ)}
    {adhesionSet : Sym2 ι → Set α} {cliqueEdges : Sym2 ι → Set (β ⊕ ℕ)}
    (hadhesion_mk : ∀ t₁ t₂, adhesionSet s(t₁, t₂) = V(τ t₁) ∩ V(τ t₂))
    (hτ_le : ∀ t, τ t ≤ G_full) (hW_K : ∀ eT, adhesionSet eT ⊆ V(G_full))
    (hF_K : ∀ (eT : Sym2 ι) (e : β ⊕ ℕ), e ∈ cliqueEdges eT →
      ∃ u ∈ adhesionSet eT, ∃ v ∈ adhesionSet eT, G_full.IsLink e u v) :
    let boundaryEdges (s : Finset ι) : Set (Sym2 ι) :=
      {eT | ∃ t₁ ∈ s, ∃ t₂ ∉ s, T.Adj t₁ t₂ ∧ eT = s(t₁, t₂)}
    let pieceV (s : Finset ι) : Set α := ⋃ t ∈ s, V(τ t)
    let pieceE (s : Finset ι) : Set (β ⊕ ℕ) :=
      (⋃ t ∈ s, E(τ t)) ∪ (⋃ eT ∈ boundaryEdges s, cliqueEdges eT)
    (∀ s : Finset ι, pieceV s ⊆ V(G_full)) →
    (∀ (s : Finset ι) (e : β ⊕ ℕ), e ∈ pieceE s →
      ∃ u ∈ pieceV s, ∃ v ∈ pieceV s, G_full.IsLink e u v) →
    ∀ t₀ : ι, IsTorsoOfDesign (graphVertexDesign T τ t₀)
      (subgraphOfVE G_full (pieceV {t₀}) (pieceE {t₀})) := by
  classical
  intro boundaryEdges pieceV pieceE hW_piece hF_piece
  let subPiece (s : Finset ι) := subgraphOfVE G_full (pieceV s) (pieceE s)
  let K (eT : Sym2 ι) := subgraphOfVE G_full (adhesionSet eT) (cliqueEdges eT)
  have hK_le (eT : Sym2 ι) : K eT ≤ G_full := subgraphOfVE_le (hW_K eT)
  have hK_E (eT : Sym2 ι) : E(K eT) = cliqueEdges eT := edgeSet_subgraphOfVE (hF_K eT)
  intro t₀
  have hV_eq : V(τ t₀) = V(subPiece {t₀}) := by
    change V(τ t₀) = ⋃ t ∈ ({t₀} : Finset ι), V(τ t)
    simp
  have hE_eq : E(subPiece {t₀}) = pieceE {t₀} := edgeSet_subgraphOfVE (hF_piece {t₀})
  have hle : τ t₀ ≤ subPiece {t₀} := by
    rw [(Compatible.of_le_le (hτ_le t₀)
      (subgraphOfVE_le (hW_piece {t₀}))).le_iff, hE_eq]
    refine ⟨hV_eq.le, fun e he => Or.inl ?_⟩
    simp [he]
  refine ⟨hV_eq, hle, ?_⟩
  rintro e ⟨he_sub, he_not_tau⟩
  rw [hE_eq] at he_sub
  rcases he_sub with he_tau | he_bd
  · simp only [Finset.mem_singleton, iUnion_iUnion_eq_left] at he_tau
    exact (he_not_tau he_tau).elim
  · obtain ⟨eT, ⟨t₁, ht₁, t₂, _, hadj, rfl⟩, heK⟩ := mem_iUnion₂.mp he_bd
    have ht₁_eq : t₁ = t₀ := Finset.mem_singleton.mp ht₁
    subst ht₁_eq
    refine ⟨V(τ t₁) ∩ V(τ t₂), ⟨t₂, hadj, rfl⟩, ?_⟩
    intro v hinc
    rcases hinc with ⟨w, hlink⟩
    have hlink_full : G_full.IsLink e v w := hlink.mono (subgraphOfVE_le (hW_piece {t₁}))
    have heK_mem : e ∈ E(K s(t₁, t₂)) := by rwa [hK_E]
    have hlink_K : (K s(t₁, t₂)).IsLink e v w :=
      ((hK_le s(t₁, t₂)).isLink_iff heK_mem).mpr hlink_full
    rw [← hadhesion_mk t₁ t₂]
    exact hlink_K.left_mem

private theorem leaf_decomposition_removal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Graph α (β ⊕ ℕ)} {T : SimpleGraph ι} {τ : ι → Graph α (β ⊕ ℕ)}
    (hTD : IsGraphTreeDecomposition G T τ) {s : Finset ι}
    (hs_tree : (T.induce (s : Set ι)).IsTree)
    (x₀ x₁ : s) (hdeg : ((T.induce (s : Set ι)).neighborSet x₀).ncard = 1)
    (hadj_ind : (T.induce (s : Set ι)).Adj x₀ x₁)
    (hx₁_uniq : ∀ u, (T.induce (s : Set ι)).Adj x₀ u → u = x₁) :
    let s' := s.erase x₀.1
    (T.induce (s' : Set ι)).IsTree ∧
      V(τ x₀.1) ∩ (⋃ t ∈ s', V(τ t)) = V(τ x₀.1) ∩ V(τ x₁.1) := by
  classical
  intro s'
  have hdeg1 : (T.induce (s : Set ι)).degree x₀ = 1 :=
    (SimpleGraph.ncard_neighborSet _ _).symm.trans hdeg
  let t₀ := x₀.1
  let t₁ := x₁.1
  have hadj_t₀t₁ : T.Adj t₀ t₁ := hadj_ind
  have ht₁_s' : t₁ ∈ s' := Finset.mem_erase.mpr ⟨hadj_t₀t₁.ne.symm, x₁.2⟩
  -- Show `(T.induce (s' : Set ι)).IsTree`
  have hs'_tree : (T.induce (s' : Set ι)).IsTree := by
    have hconn_compl : ((T.induce (s : Set ι)).induce {x₀}ᶜ).Connected :=
      hs_tree.connected.induce_compl_singleton_of_degree_eq_one hdeg1
    have htree_compl : ((T.induce (s : Set ι)).induce {x₀}ᶜ).IsTree :=
      ⟨hconn_compl, hs_tree.isAcyclic.induce {x₀}ᶜ⟩
    let e_equiv : (s' : Set ι) ≃ ({x₀}ᶜ : Set (s : Set ι)) :=
      { toFun := fun y =>
          ⟨⟨y.1, Finset.mem_of_mem_erase y.2⟩,
            fun h => (Finset.ne_of_mem_erase y.2) (congrArg Subtype.val h)⟩
        invFun := fun z =>
          ⟨z.1.1, Finset.mem_erase.mpr ⟨fun h => z.2 (Subtype.ext h), z.1.2⟩⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
    let iso_ind : T.induce (s' : Set ι) ≃g (T.induce (s : Set ι)).induce {x₀}ᶜ :=
      { toEquiv := e_equiv
        map_rel_iff' := Iff.rfl }
    exact iso_ind.symm.isTree_iff.mp htree_compl
  -- Show `V(τ t₀) ∩ (⋃ t ∈ s', V(τ t)) = V(τ t₀) ∩ V(τ t₁)`
  have hV_inter : V(τ t₀) ∩ (⋃ t ∈ s', V(τ t)) = V(τ t₀) ∩ V(τ t₁) := by
    ext v
    simp only [mem_inter_iff, mem_iUnion, exists_prop]
    refine ⟨?_, fun ⟨hv₀, hv₁⟩ => ⟨hv₀, t₁, ht₁_s', hv₁⟩⟩
    rintro ⟨hv₀, u, hu_s', hvu⟩
    refine ⟨hv₀, ?_⟩
    have hu_s : u ∈ s := Finset.mem_of_mem_erase hu_s'
    have hu_ne : u ≠ t₀ := Finset.ne_of_mem_erase hu_s'
    obtain ⟨p_ind, hp_ind⟩ := hs_tree.connected.exists_isPath x₀ ⟨u, hu_s⟩
    have ht₁_in_p : x₁ ∈ p_ind.support := by
      cases p_ind with
      | nil => exact (hu_ne rfl).elim
      | @cons _ w _ hadj_w q =>
        have hw_eq : w = x₁ := hx₁_uniq w hadj_w
        subst hw_eq
        exact Walk.support_cons _ _ ▸ List.mem_cons_of_mem x₀ q.start_mem_support
    let p := p_ind.map (SimpleGraph.Embedding.induce (s : Set ι)).toHom
    have hp_path : p.IsPath := hp_ind.map Subtype.val_injective
    have ht₁_mem : t₁ ∈ p.support := by
      rw [Walk.support_map, List.mem_map]
      exact ⟨x₁, ht₁_in_p, rfl⟩
    exact hTD.inter_subset_of_mem_path p hp_path ht₁_mem ⟨hv₀, hvu⟩
  exact ⟨hs'_tree, hV_inter⟩

/-- **Graph Minors XVI, (2.2)** (page 48):
"Let $\mathscr{D}$ be a class of designs, and let $\mathscr{D}'$ be the class of torsos of members
of $\mathscr{D}$. If $G$ is a graph with a tree-decomposition $(T, \tau)$ such that $\mathscr{D}$
contains the design of $t$ in $(T, \tau)$ for each $t \in V(T)$, then $G$ is a tree-structure over
$\mathscr{D}'$." -/
theorem theorem_2_2_proof {ι : Type*} [Fintype ι] {G : Graph α (β ⊕ ℕ)}
    {𝒟 : Set (GraphDesign α (β ⊕ ℕ))} {T : SimpleGraph ι} {τ : ι → Graph α (β ⊕ ℕ)}
    (hV : V(G).Finite) (hE : E(G).Finite)
    (hover : IsGraphTreeDecompositionOver G 𝒟 T τ) :
    HasTreeStructureOver (torsosOfClass 𝒟) G := by
  classical
  have hTD := hover.1
  obtain ⟨G_full, cliqueEdges, hV_full, hG_le_full, hF_K, hdisj_G_K, hdisj_K, hK_complete⟩ :=
    exists_torso_clique_extension τ hV hE
  let adhesionSet (eT : Sym2 ι) : Set α := {v ∈ V(G) | ∀ t ∈ eT, v ∈ V(τ t)}
  have hadhesion_mk : ∀ t₁ t₂ : ι, adhesionSet s(t₁, t₂) = V(τ t₁) ∩ V(τ t₂) := by
    intro t₁ t₂
    ext v
    simp only [adhesionSet, mem_ofPred_eq, Sym2.mem_iff, forall_eq_or_imp, forall_eq, mem_inter_iff]
    exact ⟨fun h => h.2, fun h => ⟨(hTD.le_G t₁).vertexSet_mono h.1, h⟩⟩
  have hW_K (eT : Sym2 ι) : adhesionSet eT ⊆ V(G_full) :=
    fun _ h => hV_full.symm ▸ h.1
  let K (eT : Sym2 ι) : Graph α (β ⊕ ℕ) :=
    subgraphOfVE G_full (adhesionSet eT) (cliqueEdges eT)
  have hK_le (eT : Sym2 ι) : K eT ≤ G_full := subgraphOfVE_le (hW_K eT)
  have hK_E (eT : Sym2 ι) : E(K eT) = cliqueEdges eT := edgeSet_subgraphOfVE (hF_K eT)
  let boundaryEdges (s : Finset ι) : Set (Sym2 ι) :=
    {eT : Sym2 ι | ∃ t₁ ∈ s, ∃ t₂ ∉ s, T.Adj t₁ t₂ ∧ eT = s(t₁, t₂)}
  let pieceV (s : Finset ι) : Set α := ⋃ t ∈ s, V(τ t)
  let pieceE (s : Finset ι) : Set (β ⊕ ℕ) :=
    (⋃ t ∈ s, E(τ t)) ∪ (⋃ eT ∈ boundaryEdges s, cliqueEdges eT)
  have hW_piece : ∀ s : Finset ι, pieceV s ⊆ V(G_full) :=
    fun s => iUnion₂_subset fun t _ => ((hTD.le_G t).trans hG_le_full).vertexSet_mono
  have hF_piece : ∀ (s : Finset ι) (e : β ⊕ ℕ), e ∈ pieceE s →
      ∃ u ∈ pieceV s, ∃ v ∈ pieceV s, G_full.IsLink e u v := by
    intro s e he
    rcases he with he_tau | he_bd
    · obtain ⟨t, hts, het⟩ := mem_iUnion₂.mp he_tau
      obtain ⟨u, v, hlink⟩ := exists_isLink_of_mem_edgeSet het
      exact ⟨u, mem_iUnion₂.mpr ⟨t, hts, hlink.left_mem⟩,
        v, mem_iUnion₂.mpr ⟨t, hts, hlink.right_mem⟩,
        hlink.mono ((hTD.le_G t).trans hG_le_full)⟩
    · obtain ⟨eT, ⟨t₁, ht₁s, t₂, _, _, rfl⟩, heK⟩ := mem_iUnion₂.mp he_bd
      obtain ⟨u, hu, v, hv, hlink⟩ := hF_K s(t₁, t₂) e heK
      change u ∈ adhesionSet s(t₁, t₂) at hu
      change v ∈ adhesionSet s(t₁, t₂) at hv
      rw [hadhesion_mk] at hu hv
      have hu_t₁ : u ∈ V(τ t₁) := hu.1
      have hv_t₁ : v ∈ V(τ t₁) := hv.1
      exact ⟨u, mem_iUnion₂.mpr ⟨t₁, ht₁s, hu_t₁⟩,
        v, mem_iUnion₂.mpr ⟨t₁, ht₁s, hv_t₁⟩, hlink⟩
  let subPiece (s : Finset ι) : Graph α (β ⊕ ℕ) :=
    subgraphOfVE G_full (pieceV s) (pieceE s)
  have hsubPiece_singleton_torso (t₀ : ι) :
      IsTorsoOfDesign (graphVertexDesign T τ t₀) (subPiece {t₀}) :=
    singleton_piece_is_torso hadhesion_mk
      (fun t => (hTD.le_G t).trans hG_le_full) hW_K hF_K hW_piece hF_piece t₀
  have hmain : ∀ (n : ℕ) (s : Finset ι), s.card = n → (T.induce (s : Set ι)).IsTree →
      HasTreeStructureOver (torsosOfClass 𝒟) (subPiece s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro s hcard hs_tree
      have hs_nonempty : s.Nonempty := by
        obtain ⟨⟨x, hx⟩⟩ := hs_tree.connected.nonempty
        exact ⟨x, hx⟩
      by_cases hn1 : n ≤ 1
      · have hcard1 : s.card ≤ 1 := hcard ▸ hn1
        obtain ⟨t₀, rfl⟩ := Finset.card_eq_one.mp (le_antisymm hcard1 hs_nonempty.card_pos)
        exact HasTreeStructureOver.base ⟨graphVertexDesign T τ t₀, hover.2 t₀,
          hsubPiece_singleton_torso t₀⟩
      · have hcard2 : 1 < s.card := by omega
        obtain ⟨a₁, ha₁, a₂, ha₂, ha_ne⟩ := Finset.one_lt_card.mp hcard2
        have : Nontrivial (s : Set ι) :=
          ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, fun h => ha_ne (congrArg Subtype.val h)⟩
        obtain ⟨x₀, hdeg1⟩ := hs_tree.exists_vert_degree_one_of_nontrivial
        obtain ⟨x₁, hadj_ind, hx₁_uniq⟩ :=
          (SimpleGraph.degree_eq_one_iff_existsUnique_adj (G := T.induce (s : Set ι))
            (v := x₀)).mp hdeg1
        let t₀ : ι := x₀.1
        let t₁ : ι := x₁.1
        have ht₀_s : t₀ ∈ s := x₀.2
        have ht₁_s : t₁ ∈ s := x₁.2
        have hadj_t₀t₁ : T.Adj t₀ t₁ := hadj_ind
        have ht₀_ne_t₁ : t₀ ≠ t₁ := hadj_t₀t₁.ne
        have ht₁_uniq : ∀ u ∈ s, T.Adj t₀ u → u = t₁ := by
          intro u hu hadj_u
          exact congrArg Subtype.val (hx₁_uniq ⟨u, hu⟩ hadj_u)
        let s' : Finset ι := s.erase t₀
        have ht₁_s' : t₁ ∈ s' := Finset.mem_erase.mpr ⟨ht₀_ne_t₁.symm, ht₁_s⟩
        have hs'_insert : insert t₀ s' = s := Finset.insert_erase ht₀_s
        obtain ⟨hs'_tree, hV_inter⟩ :=
          leaf_decomposition_removal hTD hs_tree x₀ x₁
            ((SimpleGraph.ncard_neighborSet _ _).trans hdeg1) hadj_ind hx₁_uniq
        -- Decompose `boundaryEdges` around `e₀ := s(t₀, t₁)`
        let e₀ : Sym2 ι := s(t₀, t₁)
        let B₁ : Set (Sym2 ι) := boundaryEdges {t₀} \ {e₀}
        let B₂ : Set (Sym2 ι) := boundaryEdges s' \ {e₀}
        obtain ⟨he₀_mem_bd₁, he₀_mem_bd₂, hbd_s, hB₁_B₂_disj⟩ :=
          boundary_edges_of_leaf ht₀_s ht₁_s hadj_t₀t₁ ht₁_uniq
        -- Define `H₁` and `H₂`
        let E₁ : Set (β ⊕ ℕ) := E(τ t₀) ∪ (⋃ eT ∈ B₁, cliqueEdges eT)
        let E₂ : Set (β ⊕ ℕ) := (⋃ u ∈ s', E(τ u)) ∪ (⋃ eT ∈ B₂, cliqueEdges eT)
        have hE₁_sub : E₁ ⊆ pieceE {t₀} := by
          refine union_subset_union ?_ (biUnion_subset_biUnion_left sdiff_subset)
          simp
        have hE₂_sub : E₂ ⊆ pieceE s' :=
          union_subset_union subset_rfl (biUnion_subset_biUnion_left sdiff_subset)
        have hF_H₁ : ∀ e ∈ E₁, ∃ u ∈ pieceV {t₀}, ∃ v ∈ pieceV {t₀}, G_full.IsLink e u v :=
          fun e he => hF_piece {t₀} e (hE₁_sub he)
        have hF_H₂ : ∀ e ∈ E₂, ∃ u ∈ pieceV s', ∃ v ∈ pieceV s', G_full.IsLink e u v :=
          fun e he => hF_piece s' e (hE₂_sub he)
        let H₁ : Graph α (β ⊕ ℕ) := subgraphOfVE G_full (pieceV {t₀}) E₁
        let H₂ : Graph α (β ⊕ ℕ) := subgraphOfVE G_full (pieceV s') E₂
        have hV_t₀ : pieceV {t₀} = V(τ t₀) := by simp [pieceV]
        have hsum : IsCliqueSum (subPiece s) (subPiece {t₀}) (subPiece s') := by
          refine ⟨H₁, H₂, K e₀, ?_, ?_, ?_, ?_⟩
          · refine isGraphSeparation_subgraphOfVE (hW_piece s) (hW_piece {t₀}) (hW_piece s')
              (hF_piece s) hF_H₁ hF_H₂ ?_ ?_ ?_
            · ext v
              simp [pieceV, ← hs'_insert]
            · dsimp only [E₁, E₂, pieceE]
              rw [union_union_union_comm, ← biUnion_union, ← hbd_s]
              congr 1
              ext e
              simp [← hs'_insert]
            · refine Disjoint.union_left ?_ ?_ <;> refine Disjoint.union_right ?_ ?_
              · rw [disjoint_iUnion₂_right]
                intro u hu_s'
                exact hTD.edge_disjoint (Finset.ne_of_mem_erase hu_s').symm
              · rw [disjoint_iUnion₂_right]
                intro eT _
                exact Disjoint.mono_left (hTD.le_G t₀).edgeSet_mono (hdisj_G_K eT)
              · rw [disjoint_iUnion₂_left]
                intro eT _
                rw [disjoint_iUnion₂_right]
                intro u _
                exact (Disjoint.mono_left (hTD.le_G u).edgeSet_mono (hdisj_G_K eT)).symm
              · rw [disjoint_iUnion₂_left]
                intro eT₁ h₁
                rw [disjoint_iUnion₂_right]
                intro eT₂ h₂
                exact hdisj_K fun heq => Set.disjoint_left.mp hB₁_B₂_disj h₁ (heq ▸ h₂)
          · have hV_inter_H : V(H₁) ∩ V(H₂) = adhesionSet e₀ := by
              change pieceV {t₀} ∩ pieceV s' = adhesionSet s(t₀, t₁)
              rw [hV_t₀, hV_inter, hadhesion_mk]
            rw [hV_inter_H]
            exact hK_complete e₀
          · refine isGraphSeparation_subgraphOfVE (hW_piece {t₀}) (hW_piece {t₀}) (hW_K e₀)
              (hF_piece {t₀}) hF_H₁ (hF_K e₀) ?_ ?_ ?_
            · rw [hV_t₀, hadhesion_mk]
              exact union_eq_self_of_subset_right inter_subset_left
            · dsimp only [E₁, pieceE]
              rw [Finset.set_biUnion_singleton, Set.union_assoc]
              congr 1
              rw [Set.union_comm, ← biUnion_insert, insert_sdiff_singleton,
                insert_eq_of_mem he₀_mem_bd₁]
            · refine Disjoint.union_left ?_ ?_
              · exact Disjoint.mono_left (hTD.le_G t₀).edgeSet_mono (hdisj_G_K e₀)
              · rw [disjoint_iUnion₂_left]
                intro eT heT
                exact hdisj_K (Ne.symm fun h => heT.2 (h.symm ▸ rfl))
          · refine isGraphSeparation_subgraphOfVE (hW_piece s') (hW_piece s') (hW_K e₀)
              (hF_piece s') hF_H₂ (hF_K e₀) ?_ ?_ ?_
            · rw [hadhesion_mk]
              exact union_eq_self_of_subset_right fun v hv =>
                mem_iUnion₂.mpr ⟨t₁, ht₁_s', hv.2⟩
            · dsimp only [E₂, pieceE]
              rw [Set.union_assoc]
              congr 1
              rw [Set.union_comm, ← biUnion_insert, insert_sdiff_singleton,
                insert_eq_of_mem he₀_mem_bd₂]
            · refine Disjoint.union_left ?_ ?_
              · rw [disjoint_iUnion₂_left]
                intro u _
                exact Disjoint.mono_left (hTD.le_G u).edgeSet_mono (hdisj_G_K e₀)
              · rw [disjoint_iUnion₂_left]
                intro eT heT
                exact hdisj_K (Ne.symm fun h => heT.2 (h.symm ▸ rfl))
        have hlt : s'.card < n := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem ht₀_s
        have htree_t₀ : (T.induce (({t₀} : Finset ι) : Set ι)).IsTree := by
          have : Nonempty (({t₀} : Finset ι) : Set ι) := ⟨⟨t₀, Finset.mem_singleton_self t₀⟩⟩
          have : Subsingleton (({t₀} : Finset ι) : Set ι) :=
            ⟨fun a b => Subtype.ext ((Finset.mem_singleton.mp a.2).trans
              (Finset.mem_singleton.mp b.2).symm)⟩
          exact SimpleGraph.IsTree.of_subsingleton
        exact HasTreeStructureOver.cliqueSum hsum
          (ih 1 (by omega) {t₀} (Finset.card_singleton t₀) htree_t₀)
          (ih s'.card hlt s' rfl hs'_tree)
  have huniv_tree : (T.induce ((Finset.univ : Finset ι) : Set ι)).IsTree := by
    rw [Finset.coe_univ]
    let iso_univ : T.induce (Set.univ : Set ι) ≃g T :=
      { toEquiv := Equiv.Set.univ ι
        map_rel_iff' := Iff.rfl }
    exact iso_univ.isTree_iff.mpr hTD.isTree
  have huniv_eq : subPiece Finset.univ = G := by
    refine (Compatible.of_le_le (subgraphOfVE_le (hW_piece Finset.univ)) hG_le_full).ext ?_ ?_
    · change (⋃ t ∈ (Finset.univ : Finset ι), V(τ t)) = V(G)
      simpa using hTD.vertexSet_union
    · rw [edgeSet_subgraphOfVE (hF_piece Finset.univ)]
      have hbd_univ : boundaryEdges Finset.univ = ∅ := by
        ext eT
        simp [boundaryEdges]
      dsimp only [pieceE]
      rw [hbd_univ, biUnion_empty, union_empty]
      simpa using hTD.edgeSet_union
  rw [← huniv_eq]
  exact hmain Finset.univ.card Finset.univ rfl huniv_tree

/-! ## Proof of Graph Minors XVI, (2.3) (page 48) -/

/-- Every torso of a member of `𝒟^n` is a loose `(≤ n)`-vertex extension of a torso of a member of
`𝒟` (Graph Minors XVI, Section 2, page 48):
"Now for $n \ge 0$, if $\mathscr{D}$ is a class of designs then every torso of a member of
$\mathscr{D}^n$ is a $(\le n)$-vertex extension of a torso of a member of $\mathscr{D}$."
This uses `IsLooseVertexExtension` because the definition of `𝒟^n` on page 47 allows `Z` to meet
`V(H)`, so a torso of `d` has vertex set `V(H)` and can retain vertices of `Z ∩ V(H)`. -/
theorem exists_isTorsoOfDesign_isLooseVertexExtension_of_isGraphEnlargement
    {n : ℕ} {d d' : GraphDesign α β} {G' : Graph α β}
    (henl : IsGraphEnlargement n d d') (htorso : IsTorsoOfDesign d' G') :
    ∃ H : Graph α β, IsTorsoOfDesign d H ∧ IsLooseVertexExtension n G' H := by
  rcases henl with ⟨Z, hZ_card, hvia⟩
  have hd_le_G' : d.1 ≤ G' := hvia.le.trans htorso.2.1
  have hdel_le_G' : GM09.deleteVertices G' Z ≤ G' := G'.induce_le sdiff_subset
  have hV_sub_d : V(G') \ Z ⊆ V(d.1) := by
    intro v ⟨hvG', hvZ⟩
    rw [← htorso.1] at hvG'
    by_contra hvd
    exact hvZ (hvia.sdiff_subset ⟨hvG', hvd⟩)
  let F : Set β := E(d.1) ∪ E(GM09.deleteVertices G' Z)
  have hW_H : V(d.1) ⊆ V(G') := hd_le_G'.vertexSet_mono
  have hF_H : ∀ e ∈ F, ∃ x ∈ V(d.1), ∃ y ∈ V(d.1), G'.IsLink e x y := by
    rintro e (hed | he_del)
    · obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet hed
      exact ⟨x, hlink.left_mem, y, hlink.right_mem, hlink.mono hd_le_G'⟩
    · obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet he_del
      exact ⟨x, hV_sub_d hlink.left_mem, y, hV_sub_d hlink.right_mem, hlink.mono hdel_le_G'⟩
  let H : Graph α β := subgraphOfVE G' V(d.1) F
  have hH_le_G' : H ≤ G' := subgraphOfVE_le hW_H
  have hH_E : E(H) = F := edgeSet_subgraphOfVE hF_H
  refine ⟨H, ⟨rfl, ?_, ?_⟩, ?_⟩
  · rw [(Compatible.of_le_le hd_le_G' hH_le_G').le_iff, hH_E]
    exact ⟨subset_rfl, subset_union_left⟩
  · rintro e ⟨heH, hed⟩
    rw [hH_E] at heH
    have he_del : e ∈ E(GM09.deleteVertices G' Z) := heH.resolve_left hed
    have heG' : e ∈ E(G') := hdel_le_G'.edgeSet_mono he_del
    have hed' : e ∉ E(d'.1) := fun h => hed (hvia.edgeSet_subset h)
    obtain ⟨X, hX_mem, hX_inc⟩ := htorso.2.2 e ⟨heG', hed'⟩
    have hX_ne_Z : X ≠ Z := by
      rintro rfl
      obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet he_del
      have hx_Z : x ∈ X := hX_inc x ⟨y, hlink.mono hdel_le_G'⟩
      exact hlink.left_mem.2 hx_Z
    refine ⟨X ∩ V(d.1), hvia.inter_mem hX_mem hX_ne_Z, ?_⟩
    intro v ⟨w, hlink⟩
    exact ⟨hX_inc v ⟨w, hlink.mono hH_le_G'⟩, hlink.left_mem⟩
  · refine ⟨Z, htorso.1 ▸ hvia.subset_vertexSet, hZ_card, hH_le_G', ?_⟩
    have hdelH_le_G' : GM09.deleteVertices H Z ≤ G' :=
      (H.induce_le sdiff_subset).trans hH_le_G'
    refine (Compatible.of_le_le hdel_le_G' hdelH_le_G').ext ?_ ?_
    · change V(G') \ Z = V(d.1) \ Z
      exact Subset.antisymm (fun v hv => ⟨hV_sub_d hv, hv.2⟩)
        (sdiff_subset_sdiff_left hW_H)
    · ext e
      simp only [GM09.deleteVertices, Graph.edgeSet_induce]
      constructor
      · intro he_del
        rcases he_del with ⟨x, y, hlink, hx, hy⟩
        have heH : e ∈ E(H) := by
          rw [hH_E]
          exact Or.inr ⟨x, y, hlink, hx, hy⟩
        exact ⟨x, y, (hH_le_G'.isLink_iff heH).mpr hlink,
          ⟨hV_sub_d hx, hx.2⟩, ⟨hV_sub_d hy, hy.2⟩⟩
      · rintro ⟨x, y, hlink, hx, hy⟩
        exact ⟨x, y, hlink.mono hH_le_G', ⟨hW_H hx.1, hx.2⟩, ⟨hW_H hy.1, hy.2⟩⟩

/-- **Graph Minors XVI, (2.3)** (page 48):
"For any $\theta \ge 1$, let $\mathscr{D}$ be a class of designs which is $\theta$-pervasive in a
graph $G$. Then $G$ may be constructed by clique-sums starting from graphs $G'$ such that either
* $|V(G')| \le 4\theta - 3$, or
* $G'$ is a $(\le 3\theta - 2)$-vertex extension of a torso of a member of $\mathscr{D}$."

Note: This theorem is stated with the loose notion `IsLooseVertexExtension` (`G' \ Z = H \ Z` for a
subgraph `H ≤ G'` with `|Z| ≤ 3θ - 2`), because the sentence preceding (2.3) on page 48 ("every
torso of a member of $\mathscr{D}^n$ is a $(\le n)$-vertex extension of a torso of a
member of $\mathscr{D}$") fails with
the strict definition `deleteVertices G' Z = H` when the enlargement set `Z` meets `V(H)`. -/
theorem theorem_2_3_proof {G : Graph α (β ⊕ ℕ)} {θ : ℕ} {𝒟 : Set (GraphDesign α (β ⊕ ℕ))}
    (hV : V(G).Finite) (hE : E(G).Finite) (hθ : 1 ≤ θ)
    (hperv : IsGraphPervasive G θ 𝒟) :
    HasTreeStructureOver
      {G' : Graph α (β ⊕ ℕ) | V(G').ncard ≤ 4 * θ - 3 ∨
        ∃ H ∈ torsosOfClass 𝒟, IsLooseVertexExtension (3 * θ - 2) G' H} G := by
  obtain ⟨ι, hfin, T, τ, hover⟩ := theorem_2_1_proof hV hE hθ hperv
  refine (theorem_2_2_proof hV hE hover).mono ?_
  rintro G' ⟨d', hd'_mem, htorso⟩
  rcases hd'_mem with ⟨d, hd_mem, henl⟩ | ⟨_, hcard⟩
  · right
    obtain ⟨H, hH_torso, hext⟩ :=
      exists_isTorsoOfDesign_isLooseVertexExtension_of_isGraphEnlargement henl htorso
    exact ⟨H, ⟨d, hd_mem, hH_torso⟩, hext⟩
  · left
    rwa [← htorso.1]

end GraphMinor.GM16
