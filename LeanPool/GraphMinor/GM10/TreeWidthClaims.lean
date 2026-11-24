/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.TreeWidthBasic

/-!
# Claims 1–3 of Theorem (5.1): Graph Minors X, Section 5 (Part 2)

This file formalizes Claims (1), (2), and (3) in the proof of **(5.1)** of Robertson and Seymour,
*Graph Minors. X. Obstructions to tree-decomposition*, J. Combin. Theory Ser. B 52 (1991) 153–190
(page 169):
- `theorem_5_1_claim_1`: Any tree-decomposition `(T, τ)` of `G` can be modified without increasing
  its width so that for each `e ∈ E(G)` there is a leaf `t` of `T` with `τ(t) = K_e`.
- `theorem_5_1_claim_2`: Assuming `G` has no isolated vertices and `E(G) ≠ ∅`, we may further
  arrange that `|E(τ(t))| = 1` for every leaf `t` of `T`.
- `theorem_5_1_claim_3`: We may further arrange that every vertex of `T` has valency `≤ 3`.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph Hypergraph

variable {α β ι : Type*}

/-! ## Claim (1) of (5.1) -/

/-- Deleting an edge `e ∉ H.edgeSet` leaves `H` unchanged. -/
theorem deleteEdges_singleton_eq_self {H : Hypergraph α β} {e : β} (he : e ∉ H.edgeSet) :
    H.deleteEdges {e} = H := by
  ext x
  · rfl
  · simp only [Hypergraph.deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff, and_iff_left_iff_imp]
    rintro hx rfl
    exact he hx
  · simp only [Hypergraph.deleteEdges, Set.mem_singleton_iff, and_iff_left_iff_imp]
    rintro hinc rfl
    exact he (H.edge_mem_of_inc hinc)

/-- Single step of Claim (1) of (5.1): given an edge `e ∈ E(τ(t₀))`, attaching a new leaf `none`
to `t₀` with `τ'(none) = K_e` and `τ'(some t) = τ(t) \ {e}` produces a tree-decomposition of `G`
of at most the same width. -/
theorem attachLeaf_edge_isTreeDecomposition [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ)
    {t₀ : ι} {e : β} (ht₀ : e ∈ (τ t₀).edgeSet) :
    let τ' : Option ι → Hypergraph α β
      | some t => (τ t).deleteEdges {e}
      | none => edgeHypergraph G e
    IsTreeDecomposition G (attachLeaf T t₀) τ' ∧
      treeDecompWidthPlusOne τ' ≤ treeDecompWidthPlusOne τ := by
  intro τ'
  have heG : e ∈ G.edgeSet := (h.le t₀).edgeSet_subset ht₀
  have hends_sub : G.ends e ⊆ (τ t₀).vertexSet := h.ends_subset_vertexSet_of_edge_mem ht₀
  have hle_G : ∀ a : Option ι, τ' a ≤ G := by
    rintro (_ | t)
    · exact edgeHypergraph_le heG
    · exact (deleteEdges_le (τ t) {e}).trans (h.le t)
  refine ⟨⟨isTree_attachLeaf h.isTree t₀, hle_G, ?_, ?_, ?_⟩, ?_⟩
  · ext x
    · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      constructor
      · rintro ⟨a, hx⟩
        exact (hle_G a).vertexSet_subset hx
      · intro hxG
        obtain ⟨t, ht⟩ := h.vertex_mem_iff.1 hxG
        exact ⟨some t, ht⟩
    · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      constructor
      · rintro ⟨a, hx⟩
        exact (hle_G a).edgeSet_subset hx
      · intro hxG
        by_cases hxe : x = e
        · subst hxe
          exact ⟨none, Set.mem_singleton x⟩
        · obtain ⟨t, ht⟩ := h.edge_mem_iff.1 hxG
          exact ⟨some t, ht, hxe⟩
    · simp only [Hypergraph.biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, hinc⟩
        exact inc_of_le (hle_G a) hinc
      · intro hincG
        by_cases hxe : x = e
        · subst hxe
          exact ⟨none, rfl, hincG⟩
        · obtain ⟨t, ht⟩ := h.inc_iff.1 hincG
          exact ⟨some t, ht, hxe⟩
  · rintro (_ | t₁) (_ | t₂) hne
    · exact (hne rfl).elim
    · ext f
      simp only [τ', edgeHypergraph, Hypergraph.deleteEdges, inter_edgeSet, Set.mem_inter_iff,
        Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, _, hne_f⟩
      exact hne_f rfl
    · ext f
      simp only [τ', edgeHypergraph, Hypergraph.deleteEdges, inter_edgeSet, Set.mem_inter_iff,
        Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hne_f⟩, rfl⟩
      exact hne_f rfl
    · ext f
      simp only [τ', Hypergraph.deleteEdges, inter_edgeSet, Set.mem_inter_iff, Set.mem_sdiff,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨hf₁, _⟩, ⟨hf₂, _⟩⟩
      have hmem : f ∈ (τ t₁ ∩ τ t₂).edgeSet := ⟨hf₁, hf₂⟩
      rw [h.edgeSet_inter_eq (fun h ↦ hne (congrArg Option.some h))] at hmem
      exact hmem
  · rintro (_ | t₁) c (_ | t₂) hp
    · have hc : c = none := onTreePath_self_iff.1 hp
      subst hc
      exact GM10.inter_le_left (hle_G none) (hle_G none)
    · refine (le_iff_of_le (GM10.inter_le (hle_G none) (hle_G (some t₂))) (hle_G c)).2 ⟨?_, ?_⟩
      · cases c with
        | none =>
          exact Set.inter_subset_left
        | some t₃ =>
          have hpT : OnTreePath T t₀ t₂ t₃ := onTreePath_projAttach_of_some hp
          have hleT := (h.inter_le hpT).vertexSet_subset
          intro v ⟨hv₁, hv₂⟩
          exact hleT ⟨hends_sub hv₁, hv₂⟩
      · intro f ⟨hf₁, _, hne_f⟩
        exact (hne_f hf₁).elim
    · refine (le_iff_of_le (GM10.inter_le (hle_G (some t₁)) (hle_G none)) (hle_G c)).2 ⟨?_, ?_⟩
      · cases c with
        | none =>
          exact Set.inter_subset_right
        | some t₃ =>
          have hpT : OnTreePath T t₁ t₀ t₃ := onTreePath_projAttach_of_some hp
          have hleT := (h.inter_le hpT).vertexSet_subset
          intro v ⟨hv₁, hv₂⟩
          exact hleT ⟨hv₁, hends_sub hv₂⟩
      · intro f ⟨⟨_, hne_f⟩, hf₂⟩
        exact (hne_f hf₂).elim
    · cases c with
      | none =>
        rcases eq_or_eq_of_onTreePath_of_unique_adj (isTree_attachLeaf h.isTree t₀).connected
          (fun w₁ w₂ h₁ h₂ ↦ (adj_attachLeaf_none_iff.1 h₁).trans
            (adj_attachLeaf_none_iff.1 h₂).symm) hp with h1 | h2
        · exact nomatch h1
        · exact nomatch h2
      | some t₃ =>
        have hpT : OnTreePath T t₁ t₂ t₃ := onTreePath_projAttach_of_some hp
        have hleT := h.inter_le hpT
        refine (le_iff_of_le (GM10.inter_le (hle_G (some t₁)) (hle_G (some t₂)))
          (hle_G (some t₃))).2 ⟨hleT.vertexSet_subset, ?_⟩
        rintro f ⟨⟨hf₁, hfe⟩, ⟨hf₂, _⟩⟩
        exact ⟨hleT.edgeSet_subset ⟨hf₁, hf₂⟩, hfe⟩
  · have : Nonempty ι := h.nonempty
    rw [treeDecompWidthPlusOne_le_iff]
    rintro (_ | t)
    · exact (Set.ncard_le_ncard hends_sub (τ t₀).vertexSet_finite).trans
        (ncard_vertexSet_le_treeDecompWidthPlusOne τ t₀)
    · exact ncard_vertexSet_le_treeDecompWidthPlusOne τ t

/-- **Claim (1) of (5.1)** (Graph Minors X, Section 5, page 169):
"(1) *We may assume that for each $e \in E(G)$, there is a leaf $t$ of $T$ with $E(\tau(t)) =
\{e\}$ and $V(\tau(t))$ the set of ends of $e$, and hence that $E(\tau(t)) = \emptyset$ for
each $t \in V(T)$ with valency $\ge 2$." -/
theorem theorem_5_1_claim_1 [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ) :
    ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (τ' : ι' → Hypergraph α β),
      IsTreeDecomposition G T' τ' ∧
      treeDecompWidthPlusOne τ' ≤ treeDecompWidthPlusOne τ ∧
      (∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T', τ' t = edgeHypergraph G e) ∧
      (∀ t ∉ leafSet T', (τ' t).edgeSet = ∅) := by
  classical
  have hmain : ∀ (k : ℕ) (ι₀ : Type) [Fintype ι₀] (T₀ : SimpleGraph ι₀)
      (τ₀ : ι₀ → Hypergraph α β),
      IsTreeDecomposition G T₀ τ₀ →
      {e ∈ G.edgeSet | ¬ ∃ t ∈ leafSet T₀, τ₀ t = edgeHypergraph G e}.ncard = k →
      ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (τ' : ι' → Hypergraph α β),
        IsTreeDecomposition G T' τ' ∧
        treeDecompWidthPlusOne τ' ≤ treeDecompWidthPlusOne τ₀ ∧
        ∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T', τ' t = edgeHypergraph G e := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro ι₀ _ T₀ τ₀ h₀ hcard
      let B : Set β := {e ∈ G.edgeSet | ¬ ∃ t ∈ leafSet T₀, τ₀ t = edgeHypergraph G e}
      have hB_fin : B.Finite := G.edgeSet_finite.subset fun _ he ↦ he.1
      by_cases hB : B.Nonempty
      · obtain ⟨e, heG, he_not⟩ := hB
        obtain ⟨t₀, ht₀⟩ := h₀.edge_mem_iff.1 heG
        let τ₁ : Option ι₀ → Hypergraph α β
          | some t => (τ₀ t).deleteEdges {e}
          | none => edgeHypergraph G e
        obtain ⟨h₁, hw₁⟩ := attachLeaf_edge_isTreeDecomposition h₀ ht₀
        let B₁ : Set β :=
          {f ∈ G.edgeSet | ¬ ∃ t ∈ leafSet (attachLeaf T₀ t₀), τ₁ t = edgeHypergraph G f}
        have hB₁_sub : B₁ ⊆ B := by
          intro f ⟨hfG, hf_not⟩
          refine ⟨hfG, ?_⟩
          rintro ⟨t₁, ht₁_leaf, hτ₀_t₁⟩
          have ht₁_ne : t₁ ≠ t₀ := by
            rintro rfl
            have he_mem : e ∈ (edgeHypergraph G f).edgeSet := hτ₀_t₁ ▸ ht₀
            have hef : e = f := Set.mem_singleton_iff.1 he_mem
            subst hef
            exact he_not ⟨t₁, ht₁_leaf, hτ₀_t₁⟩
          have he_not_t₁ : e ∉ (τ₀ t₁).edgeSet :=
            fun he_t₁ ↦ ht₁_ne (h₀.eq_of_edge_mem ht₀ he_t₁).symm
          apply hf_not
          refine ⟨some t₁, (isLeaf_attachLeaf_some_iff ht₁_ne).2 ht₁_leaf, ?_⟩
          change (τ₀ t₁).deleteEdges {e} = edgeHypergraph G f
          rw [deleteEdges_singleton_eq_self he_not_t₁, hτ₀_t₁]
        have he_not_B₁ : e ∉ B₁ := by
          intro ⟨_, hnot⟩
          exact hnot ⟨none, isLeaf_attachLeaf_none T₀ t₀, rfl⟩
        have hlt : B₁.ncard < k := by
          rw [← hcard]
          exact Set.ncard_lt_ncard ⟨hB₁_sub, fun hsub ↦ he_not_B₁ (hsub ⟨heG, he_not⟩)⟩ hB_fin
        obtain ⟨ι', hfin', T', τ', h', hw', hclaim⟩ := ih B₁.ncard hlt (Option ι₀)
          (attachLeaf T₀ t₀) τ₁ h₁ rfl
        exact ⟨ι', hfin', T', τ', h', hw'.trans hw₁, hclaim⟩
      · rw [Set.not_nonempty_iff_eq_empty] at hB
        refine ⟨ι₀, inferInstance, T₀, τ₀, h₀, le_rfl, ?_⟩
        intro e heG
        by_contra hnot
        have heB : e ∈ B := ⟨heG, hnot⟩
        rw [hB] at heB
        exact heB
  let eFin := Fintype.equivFin ι
  obtain ⟨ι', hfin', T', τ', h', hw', hclaim⟩ :=
    hmain _ (Fin (Fintype.card ι)) (T.map eFin.toEmbedding) (τ ∘ eFin.symm) (h.relabel eFin) rfl
  rw [treeDecompWidthPlusOne_comp_equiv] at hw'
  refine ⟨ι', hfin', T', τ', h', hw', hclaim, ?_⟩
  intro t ht_not_leaf
  ext e
  simp only [Set.mem_empty_iff_false, iff_false]
  intro he_t
  obtain ⟨t_e, ht_e_leaf, hτ'_te⟩ := hclaim e ((h'.le t).edgeSet_subset he_t)
  have he_te : e ∈ (τ' t_e).edgeSet := by
    rw [hτ'_te]
    exact Set.mem_singleton e
  have heq : t = t_e := h'.eq_of_edge_mem he_t he_te
  exact ht_not_leaf (heq ▸ ht_e_leaf)

/-! ## Claim (2) of (5.1) -/

/-- The canonical graph homomorphism `T.induce S →g T`. -/
@[expose] def induceHom (T : SimpleGraph ι) (S : Set ι) : T.induce S →g T where
  toFun := Subtype.val
  map_rel' h := h

/-- In an induced subgraph `T.induce S`, the degree of any `x : S` is at most `T.degree x.1`. -/
theorem degree_induce_le [Fintype ι] (T : SimpleGraph ι) (S : Set ι) [Fintype S]
    [DecidableRel (T.induce S).Adj] [DecidableRel T.Adj] (x : S) :
    (T.induce S).degree x ≤ T.degree x.1 := by
  rw [← ncard_neighborSet, ← ncard_neighborSet]
  have hsub : Subtype.val '' (T.induce S).neighborSet x ⊆ T.neighborSet x.1 := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-- If `x.1` is a leaf of `T`, then `x` is a leaf of `T.induce S`. -/
theorem isLeaf_induce_of_isLeaf [Fintype ι] {T : SimpleGraph ι} {S : Set ι} [Fintype S]
    {x : S} (hx : IsLeaf T x.1) : IsLeaf (T.induce S) x := by
  classical
  exact (degree_induce_le T S x).trans hx

/-- Deleting a degree-1 vertex `t₀` from a tree `T` produces a tree `T.induce {t₀}ᶜ`. -/
theorem isTree_induce_compl_singleton [Fintype ι] {T : SimpleGraph ι} (hT : T.IsTree)
    {t₀ : ι} (hdeg1 : by classical exact T.degree t₀ = 1) :
    (T.induce {t₀}ᶜ).IsTree := by
  classical
  exact ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hdeg1,
    hT.isAcyclic.comap (induceHom T {t₀}ᶜ) Subtype.val_injective⟩

/-- In a tree `T` where `T.induce {t₀}ᶜ` is connected, `OnTreePath (T.induce {t₀}ᶜ) a b c` implies
`OnTreePath T a.1 b.1 c.1`. -/
theorem onTreePath_of_induce_compl_singleton {T : SimpleGraph ι} (hT : T.IsTree) {t₀ : ι}
    (hconn : (T.induce {t₀}ᶜ).Connected) {a b c : ({t₀}ᶜ : Set ι)}
    (hp : OnTreePath (T.induce {t₀}ᶜ) a b c) :
    OnTreePath T a.1 b.1 c.1 := by
  obtain ⟨q, hq⟩ := hconn.exists_isPath a b
  have hq_map : (q.map (induceHom T {t₀}ᶜ)).IsPath :=
    hq.map Subtype.val_injective
  change OnTreePath T (induceHom T {t₀}ᶜ a) (induceHom T {t₀}ᶜ b) (induceHom T {t₀}ᶜ c)
  rw [onTreePath_iff_of_isPath hT hq_map, Walk.support_map, List.mem_map]
  exact ⟨c, hp q hq, rfl⟩

/-- **Claim (2) of (5.1)** (Graph Minors X, Section 5, page 169):
"(2) *We may assume that $|E(\tau(t))| = 1$ for each leaf $t$ of $T$." -/
theorem theorem_5_1_claim_2 [Fintype ι] {G : Hypergraph α β}
    (hno_iso : ∀ v ∈ G.vertexSet, ∃ e, G.Inc e v) (hE : G.edgeSet.Nonempty)
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ)
    (hclaim1 : ∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T, τ t = edgeHypergraph G e) :
    ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (τ' : ι' → Hypergraph α β),
      IsTreeDecomposition G T' τ' ∧
      treeDecompWidthPlusOne τ' ≤ treeDecompWidthPlusOne τ ∧
      (∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T', τ' t = edgeHypergraph G e) ∧
      (∀ t ∈ leafSet T', ∃ e ∈ G.edgeSet, τ' t = edgeHypergraph G e) ∧
      (∀ t ∉ leafSet T', (τ' t).edgeSet = ∅) := by
  classical
  have hmain : ∀ (n : ℕ) (ι₀ : Type) [Fintype ι₀] (T₀ : SimpleGraph ι₀)
      (τ₀ : ι₀ → Hypergraph α β),
      IsTreeDecomposition G T₀ τ₀ →
      (∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T₀, τ₀ t = edgeHypergraph G e) →
      Fintype.card ι₀ = n →
      ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (τ' : ι' → Hypergraph α β),
        IsTreeDecomposition G T' τ' ∧
        treeDecompWidthPlusOne τ' ≤ treeDecompWidthPlusOne τ₀ ∧
        (∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T', τ' t = edgeHypergraph G e) ∧
        (∀ t ∈ leafSet T', (τ' t).edgeSet.Nonempty) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro ι₀ _ T₀ τ₀ h₀ hc1 hcard
      by_cases hbad : ∃ t₀ ∈ leafSet T₀, (τ₀ t₀).edgeSet = ∅
      · obtain ⟨t₀, ht₀_leaf, ht₀_empty⟩ := hbad
        obtain ⟨e₀, he₀⟩ := hE
        obtain ⟨t_e₀, _, hτ₀_te₀⟩ := hc1 e₀ he₀
        have ht₀_ne_te₀ : t₀ ≠ t_e₀ := by
          rintro rfl
          have hmem : e₀ ∈ (τ₀ t₀).edgeSet := by
            rw [hτ₀_te₀]
            exact Set.mem_singleton e₀
          rw [ht₀_empty] at hmem
          exact hmem
        have hdeg_pos : 1 ≤ T₀.degree t₀ := by
          obtain ⟨p, _⟩ := h₀.isTree.connected.exists_isPath t₀ t_e₀
          cases p with
          | nil => exact (ht₀_ne_te₀ rfl).elim
          | @cons _ w _ hadj _ =>
            rw [← card_neighborFinset_eq_degree]
            exact Finset.card_pos.2 ⟨w, (mem_neighborFinset T₀ t₀ w).2 hadj⟩
        have hdeg1 : T₀.degree t₀ = 1 := le_antisymm ht₀_leaf hdeg_pos
        let S : Set ι₀ := {t₀}ᶜ
        let T₁ := T₀.induce S
        let τ₁ : S → Hypergraph α β := fun x ↦ τ₀ x.1
        have hT₁_tree : T₁.IsTree := isTree_induce_compl_singleton h₀.isTree hdeg1
        have hc1' : ∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T₁, τ₁ t = edgeHypergraph G e := by
          intro e heG
          obtain ⟨t, ht_leaf, hτ_t⟩ := hc1 e heG
          have ht_ne : t ≠ t₀ := by
            rintro rfl
            have hmem : e ∈ (τ₀ t).edgeSet := by
              rw [hτ_t]
              exact Set.mem_singleton e
            rw [ht₀_empty] at hmem
            exact hmem
          exact ⟨⟨t, ht_ne⟩, isLeaf_induce_of_isLeaf ht_leaf, hτ_t⟩
        have h₁ : IsTreeDecomposition G T₁ τ₁ := by
          refine ⟨hT₁_tree, fun x ↦ h₀.le x.1, ?_, ?_, ?_⟩
          · ext x
            · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
              constructor
              · rintro ⟨a, hx⟩
                exact (h₀.le a.1).vertexSet_subset hx
              · intro hxG
                obtain ⟨e, hinc⟩ := hno_iso x hxG
                obtain ⟨t, _, hτ_t⟩ := hc1' e (G.edge_mem_of_inc hinc)
                refine ⟨t, ?_⟩
                rw [hτ_t]
                exact hinc
            · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
              constructor
              · rintro ⟨a, hx⟩
                exact (h₀.le a.1).edgeSet_subset hx
              · intro heG
                obtain ⟨t, _, hτ_t⟩ := hc1' x heG
                refine ⟨t, ?_⟩
                rw [hτ_t]
                exact Set.mem_singleton x
            · simp only [Hypergraph.biUnion, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨a, hinc⟩
                exact inc_of_le (h₀.le a.1) hinc
              · intro hincG
                obtain ⟨t, _, hτ_t⟩ := hc1' x (G.edge_mem_of_inc hincG)
                refine ⟨t, ?_⟩
                rw [hτ_t]
                exact ⟨rfl, hincG⟩
          · intro x y hne
            exact h₀.edgeSet_inter_eq (fun h ↦ hne (Subtype.ext h))
          · intro a c b hp
            exact h₀.inter_le (onTreePath_of_induce_compl_singleton h₀.isTree hT₁_tree.connected hp)
        have hw₁ : treeDecompWidthPlusOne τ₁ ≤ treeDecompWidthPlusOne τ₀ := by
          have : Nonempty S := h₁.nonempty
          rw [treeDecompWidthPlusOne_le_iff]
          intro x
          exact ncard_vertexSet_le_treeDecompWidthPlusOne τ₀ x.1
        have hlt : Fintype.card S < n := by
          rw [← hcard]
          exact Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
            (by rintro ⟨⟨x, hx⟩, rfl⟩; exact hx rfl)
        obtain ⟨ι', hfin', T', τ', h', hw', hc1'', hne'⟩ :=
          ih (Fintype.card S) hlt S T₁ τ₁ h₁ hc1' rfl
        exact ⟨ι', hfin', T', τ', h', hw'.trans hw₁, hc1'', hne'⟩
      · push Not at hbad
        exact ⟨ι₀, inferInstance, T₀, τ₀, h₀, le_rfl, hc1, hbad⟩
  let eFin := Fintype.equivFin ι
  have hc1_fin : ∀ e ∈ G.edgeSet, ∃ t ∈ leafSet (T.map eFin.toEmbedding),
      (τ ∘ eFin.symm) t = edgeHypergraph G e := by
    intro e heG
    obtain ⟨t, ht_leaf, hτ_t⟩ := hclaim1 e heG
    refine ⟨eFin t, (isLeaf_map eFin t).2 ht_leaf, ?_⟩
    simpa using hτ_t
  obtain ⟨ι', hfin', T', τ', h', hw', hc1', hne'⟩ :=
    hmain _ (Fin (Fintype.card ι)) (T.map eFin.toEmbedding) (τ ∘ eFin.symm)
      (h.relabel eFin) hc1_fin rfl
  rw [treeDecompWidthPlusOne_comp_equiv] at hw'
  have hnonleaf_empty : ∀ t ∉ leafSet T', (τ' t).edgeSet = ∅ := by
    intro t ht_not_leaf
    ext e
    simp only [Set.mem_empty_iff_false, iff_false]
    intro he_t
    obtain ⟨t_e, ht_e_leaf, hτ'_te⟩ := hc1' e ((h'.le t).edgeSet_subset he_t)
    have he_te : e ∈ (τ' t_e).edgeSet := by
      rw [hτ'_te]
      exact Set.mem_singleton e
    have heq : t = t_e := h'.eq_of_edge_mem he_t he_te
    exact ht_not_leaf (heq ▸ ht_e_leaf)
  have hleaf_eq : ∀ t ∈ leafSet T', ∃ e ∈ G.edgeSet, τ' t = edgeHypergraph G e := by
    intro t ht_leaf
    obtain ⟨e, he_t⟩ := hne' t ht_leaf
    have heG : e ∈ G.edgeSet := (h'.le t).edgeSet_subset he_t
    obtain ⟨t_e, _, hτ'_te⟩ := hc1' e heG
    have he_te : e ∈ (τ' t_e).edgeSet := by
      rw [hτ'_te]
      exact Set.mem_singleton e
    have heq : t = t_e := h'.eq_of_edge_mem he_t he_te
    exact ⟨e, heG, heq ▸ hτ'_te⟩
  exact ⟨ι', hfin', T', τ', h', hw', hc1', hleaf_eq, hnonleaf_empty⟩

/-! ## Claim (3) of (5.1): splitting vertices of degree `≥ 4` -/

/-- Split a vertex `t₀` of `T` by pulling two of its neighbors `w₁, w₂` onto a new vertex
`none : Option ι` adjacent to `some t₀`, `some w₁`, and `some w₂`
(Graph Minors X, Section 5, proof of (5.1), Claim (3), page 169). -/
@[expose] def splitVertex (T : SimpleGraph ι) (t₀ w₁ w₂ : ι) : SimpleGraph (Option ι) where
  Adj a b :=
    match a, b with
    | some x, some y =>
        T.Adj x y ∧ ¬ (x = t₀ ∧ (y = w₁ ∨ y = w₂)) ∧ ¬ (y = t₀ ∧ (x = w₁ ∨ x = w₂))
    | some x, none => x = t₀ ∨ x = w₁ ∨ x = w₂
    | none, some y => y = t₀ ∨ y = w₁ ∨ y = w₂
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    rintro (_ | x) h
    · exact h
    · exact T.loopless.irrefl x h.1⟩

/-- Every walk `p : T.Walk u v` lifts to a walk in `splitVertex T t₀ w₁ w₂` from `some u` to
`some v` whose support maps into `p.support` under `projAttach t₀`. -/
theorem exists_walk_splitVertex {T : SimpleGraph ι} {t₀ w₁ w₂ : ι}
    {u v : ι} (p : T.Walk u v) :
    ∃ w : (splitVertex T t₀ w₁ w₂).Walk (some u) (some v),
      ∀ z ∈ w.support, projAttach t₀ z ∈ p.support := by
  induction p with
  | nil =>
    refine ⟨Walk.nil, fun z hz ↦ ?_⟩
    rw [Walk.support_nil, List.mem_singleton] at hz
    subst hz
    simp [projAttach]
  | @cons a b c hadj q ih =>
    obtain ⟨wq, hwq⟩ := ih
    have hedge : ∃ we : (splitVertex T t₀ w₁ w₂).Walk (some a) (some b),
        ∀ z ∈ we.support, projAttach t₀ z = a ∨ projAttach t₀ z = b := by
      by_cases h1 : a = t₀ ∧ (b = w₁ ∨ b = w₂)
      · have ha : (splitVertex T t₀ w₁ w₂).Adj (some a) none := Or.inl h1.1
        have hb : (splitVertex T t₀ w₁ w₂).Adj none (some b) := Or.inr h1.2
        refine ⟨Walk.cons ha (Walk.cons hb Walk.nil), fun z hz ↦ ?_⟩
        rw [Walk.support_cons, Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.mem_cons, List.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inl h1.1.symm
        · exact Or.inr rfl
      · by_cases h2 : b = t₀ ∧ (a = w₁ ∨ a = w₂)
        · have ha : (splitVertex T t₀ w₁ w₂).Adj (some a) none := Or.inr h2.2
          have hb : (splitVertex T t₀ w₁ w₂).Adj none (some b) := Or.inl h2.1
          refine ⟨Walk.cons ha (Walk.cons hb Walk.nil), fun z hz ↦ ?_⟩
          rw [Walk.support_cons, Walk.support_cons, Walk.support_nil, List.mem_cons,
            List.mem_cons, List.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr h2.1.symm
          · exact Or.inr rfl
        · have hab : (splitVertex T t₀ w₁ w₂).Adj (some a) (some b) := ⟨hadj, h1, h2⟩
          refine ⟨Walk.cons hab Walk.nil, fun z hz ↦ ?_⟩
          rw [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
    obtain ⟨we, hwe⟩ := hedge
    refine ⟨we.append wq, fun z hz ↦ ?_⟩
    rcases (Walk.mem_support_append_iff _ _).1 hz with h1 | h2
    · rcases hwe z h1 with heq | heq
      · rw [heq]; exact List.mem_cons_self
      · rw [heq]; exact List.mem_cons_of_mem a q.start_mem_support
    · exact List.mem_cons_of_mem a (hwq z h2)

/-- A short walk in `splitVertex T t₀ w₁ w₂` from `a` to `some (projAttach t₀ a)` whose support
maps into `{projAttach t₀ a}`. -/
@[expose] def toSomeWalkSplit (T : SimpleGraph ι) (t₀ w₁ w₂ : ι) :
    ∀ a : Option ι, (splitVertex T t₀ w₁ w₂).Walk a (some (projAttach t₀ a))
  | some _ => Walk.nil
  | none => Walk.cons (show (splitVertex T t₀ w₁ w₂).Adj none (some t₀) from Or.inl rfl) Walk.nil

theorem projAttach_mem_toSomeWalkSplit {T : SimpleGraph ι} {t₀ w₁ w₂ : ι} {a z : Option ι}
    (hz : z ∈ (toSomeWalkSplit T t₀ w₁ w₂ a).support) :
    projAttach t₀ z = projAttach t₀ a := by
  cases a with
  | none =>
    dsimp only [toSomeWalkSplit, projAttach] at hz ⊢
    rw [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton] at hz
    rcases hz with rfl | rfl <;> rfl
  | some x =>
    dsimp only [toSomeWalkSplit, projAttach] at hz ⊢
    rw [Walk.support_nil, List.mem_singleton] at hz
    subst hz
    rfl

/-- `OnTreePath (splitVertex T t₀ w₁ w₂) a b c` implies
`OnTreePath T (projAttach t₀ a) (projAttach t₀ b) (projAttach t₀ c)`. -/
theorem onTreePath_projAttach_of_splitVertex {T : SimpleGraph ι} {t₀ w₁ w₂ : ι}
    {a b c : Option ι} (h : OnTreePath (splitVertex T t₀ w₁ w₂) a b c) :
    OnTreePath T (projAttach t₀ a) (projAttach t₀ b) (projAttach t₀ c) := by
  intro p _
  obtain ⟨wp, hwp⟩ := exists_walk_splitVertex (t₀ := t₀) (w₁ := w₁) (w₂ := w₂) p
  let w : (splitVertex T t₀ w₁ w₂).Walk a b :=
    (toSomeWalkSplit T t₀ w₁ w₂ a).append
      (wp.append (toSomeWalkSplit T t₀ w₁ w₂ b).reverse)
  have hm : c ∈ w.support := mem_support_of_onTreePath h w
  rcases (Walk.mem_support_append_iff _ _).1 hm with h1 | h2
  · rw [projAttach_mem_toSomeWalkSplit h1]
    exact p.start_mem_support
  · rcases (Walk.mem_support_append_iff _ _).1 h2 with h3 | h4
    · exact hwp c h3
    · have h4' : c ∈ (toSomeWalkSplit T t₀ w₁ w₂ b).support.reverse :=
        Walk.support_reverse (toSomeWalkSplit T t₀ w₁ w₂ b) ▸ h4
      rw [projAttach_mem_toSomeWalkSplit (List.mem_reverse.1 h4')]
      exact p.end_mem_support

/-- Degrees of vertices in `splitVertex T t₀ w₁ w₂`:
- `degree none = 3`
- `degree (some t₀) = T.degree t₀ - 1`
- `degree (some x) = T.degree x` for `x ≠ t₀`. -/
theorem degrees_splitVertex [Fintype ι] {T : SimpleGraph ι} {t₀ w₁ w₂ : ι}
    [DecidableRel (splitVertex T t₀ w₁ w₂).Adj] [DecidableRel T.Adj]
    (hadj₁ : T.Adj t₀ w₁) (hadj₂ : T.Adj t₀ w₂) (hw12 : w₁ ≠ w₂) :
    (splitVertex T t₀ w₁ w₂).degree none = 3 ∧
      (splitVertex T t₀ w₁ w₂).degree (some t₀) + 1 = T.degree t₀ ∧
      ∀ x : ι, x ≠ t₀ → (splitVertex T t₀ w₁ w₂).degree (some x) = T.degree x := by
  let T' := splitVertex T t₀ w₁ w₂
  have hne₁ : t₀ ≠ w₁ := hadj₁.ne
  have hne₂ : t₀ ≠ w₂ := hadj₂.ne
  refine ⟨?_, ?_, ?_⟩
  · rw [← ncard_neighborSet]
    have hset : T'.neighborSet none = {some t₀, some w₁, some w₂} := by
      ext z
      cases z <;> simp [T', splitVertex, mem_neighborSet]
    rw [hset, Set.ncard_insert_of_notMem, Set.ncard_pair (Option.some_injective ι |>.ne hw12)]
    simp [hne₁, hne₂]
  · rw [← ncard_neighborSet, ← ncard_neighborSet]
    let S₀ : Set ι := T.neighborSet t₀ \ {w₁, w₂}
    have hset : T'.neighborSet (some t₀) = insert none (Option.some '' S₀) := by
      ext z
      cases z with
      | none =>
        simp [T', splitVertex, mem_neighborSet]
      | some y =>
        simp [T', splitVertex, mem_neighborSet, S₀, hne₁, hne₂]
    have hnone_not : (none : Option ι) ∉ Option.some '' S₀ := by simp
    rw [hset, Set.ncard_insert_of_notMem hnone_not (Set.toFinite _),
      Set.ncard_image_of_injective _ (Option.some_injective ι)]
    have hsub : ({w₁, w₂} : Set ι) ⊆ T.neighborSet t₀ := by
      rintro y (rfl | rfl) <;> assumption
    have hdiff : S₀.ncard = (T.neighborSet t₀).ncard - ({w₁, w₂} : Set ι).ncard :=
      Set.ncard_sdiff hsub (Set.toFinite _)
    have hpair : ({w₁, w₂} : Set ι).ncard = 2 := Set.ncard_pair hw12
    have hge2 : 2 ≤ (T.neighborSet t₀).ncard := by
      rw [← hpair]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  · intro x hxt₀
    rw [← ncard_neighborSet, ← ncard_neighborSet]
    have hbij : Set.BijOn (projAttach t₀) (T'.neighborSet (some x)) (T.neighborSet x) := by
      refine ⟨?_, ?_, ?_⟩
      · rintro (_ | y) hz
        · simp only [T', splitVertex, mem_neighborSet] at hz
          rcases hz with rfl | rfl | rfl
          · exact (hxt₀ rfl).elim
          · exact hadj₁.symm
          · exact hadj₂.symm
        · exact hz.1
      · rintro (_ | y₁) hz₁ (_ | y₂) hz₂ heq
        · rfl
        · change t₀ = y₂ at heq
          subst heq
          rcases hz₁ with rfl | hxw₁ | hxw₂
          · exact (hxt₀ rfl).elim
          · exact (hz₂.2.2 ⟨rfl, Or.inl hxw₁⟩).elim
          · exact (hz₂.2.2 ⟨rfl, Or.inr hxw₂⟩).elim
        · change y₁ = t₀ at heq
          subst heq
          rcases hz₂ with rfl | hxw₁ | hxw₂
          · exact (hxt₀ rfl).elim
          · exact (hz₁.2.2 ⟨rfl, Or.inl hxw₁⟩).elim
          · exact (hz₁.2.2 ⟨rfl, Or.inr hxw₂⟩).elim
        · exact congrArg Option.some heq
      · intro y hy
        by_cases hcase : y = t₀ ∧ (x = w₁ ∨ x = w₂)
        · exact ⟨none, Or.inr hcase.2, hcase.1.symm⟩
        · refine ⟨some y, ?_, rfl⟩
          change T.Adj x y ∧ ¬ (x = t₀ ∧ (y = w₁ ∨ y = w₂)) ∧ ¬ (y = t₀ ∧ (x = w₁ ∨ x = w₂))
          refine ⟨hy, ?_, hcase⟩
          rintro ⟨rfl, _⟩
          exact hxt₀ rfl
    rw [← hbij.image_eq, hbij.injOn.ncard_image]

/-- Leaves of `splitVertex T t₀ w₁ w₂` when `4 ≤ T.degree t₀` are exactly `some x` for leaves `x`
of `T`. -/
theorem mem_leafSet_splitVertex_iff [Fintype ι] {T : SimpleGraph ι} {t₀ w₁ w₂ : ι}
    [DecidableRel T.Adj]
    (hadj₁ : T.Adj t₀ w₁) (hadj₂ : T.Adj t₀ w₂) (hw12 : w₁ ≠ w₂)
    (ht₀_deg : 4 ≤ T.degree t₀) (a : Option ι) :
    a ∈ leafSet (splitVertex T t₀ w₁ w₂) ↔ ∃ x ∈ leafSet T, a = some x := by
  classical
  obtain ⟨hdeg_none, hdeg_t₀, hdeg_other⟩ := degrees_splitVertex hadj₁ hadj₂ hw12
  have hleaf_T : ∀ x : ι, x ∈ leafSet T ↔ T.degree x ≤ 1 := by
    intro x
    unfold leafSet IsLeaf
    rw [Set.mem_ofPred_eq]
    convert Iff.rfl
  have hleaf_T' : ∀ z : Option ι,
      z ∈ leafSet (splitVertex T t₀ w₁ w₂) ↔ (splitVertex T t₀ w₁ w₂).degree z ≤ 1 := by
    intro z
    unfold leafSet IsLeaf
    rw [Set.mem_ofPred_eq]
  have ht₀_not_leaf : t₀ ∉ leafSet T := by
    rw [hleaf_T]
    omega
  cases a with
  | none =>
    rw [hleaf_T']
    constructor
    · intro hnone
      omega
    · rintro ⟨_, _, h⟩
      exact nomatch h
  | some x =>
    rw [hleaf_T']
    by_cases hxt₀ : x = t₀
    · subst hxt₀
      constructor
      · intro hsome
        omega
      · rintro ⟨y, hy, heq⟩
        exact (ht₀_not_leaf (Option.some.inj heq ▸ hy)).elim
    · constructor
      · intro hx
        refine ⟨x, ?_, rfl⟩
        rw [hleaf_T, ← hdeg_other x hxt₀]
        exact hx
      · rintro ⟨y, hy, heq⟩
        cases Option.some.inj heq
        rw [hleaf_T] at hy
        rwa [hdeg_other x hxt₀]

/-- When `4 ≤ T.degree t₀`, splitting `t₀` strictly decreases `∑ x, (degree x - 3)`. -/
theorem sum_degree_sub_three_splitVertex_lt [Fintype ι] {T : SimpleGraph ι} {t₀ w₁ w₂ : ι}
    [DecidableRel (splitVertex T t₀ w₁ w₂).Adj] [DecidableRel T.Adj]
    (hadj₁ : T.Adj t₀ w₁) (hadj₂ : T.Adj t₀ w₂) (hw12 : w₁ ≠ w₂)
    (ht₀_deg : 4 ≤ T.degree t₀) :
    (∑ a : Option ι, ((splitVertex T t₀ w₁ w₂).degree a - 3)) <
      ∑ x : ι, (T.degree x - 3) := by
  classical
  let T' := splitVertex T t₀ w₁ w₂
  obtain ⟨hdeg_none, hdeg_t₀, hdeg_other⟩ := degrees_splitVertex hadj₁ hadj₂ hw12
  have hs1 : ∑ x : ι, (T'.degree (some x) - 3) =
      (T'.degree (some t₀) - 3) + ∑ x ∈ Finset.univ.erase t₀, (T'.degree (some x) - 3) :=
    (Finset.add_sum_erase (Finset.univ : Finset ι)
      (fun x ↦ T'.degree (some x) - 3) (Finset.mem_univ t₀)).symm
  have hs2 : ∑ x : ι, (T.degree x - 3) =
      (T.degree t₀ - 3) + ∑ x ∈ Finset.univ.erase t₀, (T.degree x - 3) :=
    (Finset.add_sum_erase (Finset.univ : Finset ι)
      (fun x ↦ T.degree x - 3) (Finset.mem_univ t₀)).symm
  have heq_rest : ∑ x ∈ Finset.univ.erase t₀, (T'.degree (some x) - 3) =
      ∑ x ∈ Finset.univ.erase t₀, (T.degree x - 3) := by
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [hdeg_other x (Finset.ne_of_mem_erase hx)]
  have hdeg_t₀' : T'.degree (some t₀) + 1 = T.degree t₀ := hdeg_t₀
  rw [Fintype.sum_option, hdeg_none, hs1, hs2, heq_rest]
  omega

/-- Splitting a vertex `t₀` of a tree `T` with neighbors `w₁ ≠ w₂` produces a tree. -/
theorem isTree_splitVertex [Finite ι] {T : SimpleGraph ι} (hT : T.IsTree) {t₀ w₁ w₂ : ι}
    (hadj₁ : T.Adj t₀ w₁) (hadj₂ : T.Adj t₀ w₂) (hw12 : w₁ ≠ w₂) :
    (splitVertex T t₀ w₁ w₂).IsTree := by
  classical
  let := Fintype.ofFinite ι
  let T' := splitVertex T t₀ w₁ w₂
  have hconn : T'.Connected := by
    refine Connected.mk fun a b ↦ ?_
    obtain ⟨p⟩ := hT.connected (projAttach t₀ a) (projAttach t₀ b)
    obtain ⟨wp, _⟩ := exists_walk_splitVertex (t₀ := t₀) (w₁ := w₁) (w₂ := w₂) p
    exact ⟨(toSomeWalkSplit T t₀ w₁ w₂ a).append
      (wp.append (toSomeWalkSplit T t₀ w₁ w₂ b).reverse)⟩
  obtain ⟨hdeg_none, hdeg_t₀, hdeg_other⟩ := degrees_splitVertex hadj₁ hadj₂ hw12
  have hsum_some : ∑ x : ι, T'.degree (some x) + 1 = ∑ x : ι, T.degree x := by
    have h1 : ∑ x : ι, T'.degree (some x) =
        T'.degree (some t₀) + ∑ x ∈ Finset.univ.erase t₀, T'.degree (some x) :=
      (Finset.add_sum_erase (Finset.univ : Finset ι) (fun x ↦ T'.degree (some x))
        (Finset.mem_univ t₀)).symm
    have h2 : ∑ x : ι, T.degree x =
        T.degree t₀ + ∑ x ∈ Finset.univ.erase t₀, T.degree x :=
      (Finset.add_sum_erase (Finset.univ : Finset ι) (fun x ↦ T.degree x)
        (Finset.mem_univ t₀)).symm
    have heq_rest : ∑ x ∈ Finset.univ.erase t₀, T'.degree (some x) =
        ∑ x ∈ Finset.univ.erase t₀, T.degree x := by
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      exact hdeg_other x (Finset.ne_of_mem_erase hx)
    have hdeg_t₀' : T'.degree (some t₀) + 1 = T.degree t₀ := hdeg_t₀
    rw [h1, h2, heq_rest]
    omega
  have hsum_all : ∑ z : Option ι, T'.degree z = (∑ x : ι, T.degree x) + 2 := by
    rw [Fintype.sum_option, hdeg_none]
    omega
  have htwice' := T'.sum_degrees_eq_twice_card_edges
  have htwice := T.sum_degrees_eq_twice_card_edges
  have hedge : Nat.card T'.edgeSet = Nat.card T.edgeSet + 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← T'.edgeFinset_card,
      ← T.edgeFinset_card]
    omega
  have hcardT : Nat.card T.edgeSet + 1 = Nat.card ι :=
    (isTree_iff_connected_and_card.1 hT).2
  refine isTree_iff_connected_and_card.2 ⟨hconn, ?_⟩
  rw [hedge, hcardT, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]

/-- Single step of Claim (3) of (5.1): splitting a non-leaf vertex `t₀` with `(τ t₀).edgeSet = ∅`
preserves `IsTreeDecomposition` and `treeDecompWidthPlusOne`. -/
theorem splitVertex_isTreeDecomposition [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ)
    {t₀ w₁ w₂ : ι} (hadj₁ : T.Adj t₀ w₁) (hadj₂ : T.Adj t₀ w₂) (hw12 : w₁ ≠ w₂)
    (ht₀_empty : (τ t₀).edgeSet = ∅) :
    IsTreeDecomposition G (splitVertex T t₀ w₁ w₂) (fun a ↦ τ (projAttach t₀ a)) ∧
      treeDecompWidthPlusOne (fun a ↦ τ (projAttach t₀ a)) ≤ treeDecompWidthPlusOne τ := by
  refine ⟨⟨isTree_splitVertex h.isTree hadj₁ hadj₂ hw12, fun a ↦ h.le (projAttach t₀ a),
    ?_, ?_, ?_⟩, ?_⟩
  · ext x
    · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      constructor
      · rintro ⟨a, hx⟩
        exact (h.le (projAttach t₀ a)).vertexSet_subset hx
      · intro hxG
        obtain ⟨t, ht⟩ := h.vertex_mem_iff.1 hxG
        exact ⟨some t, ht⟩
    · simp only [Hypergraph.biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      constructor
      · rintro ⟨a, hx⟩
        exact (h.le (projAttach t₀ a)).edgeSet_subset hx
      · intro heG
        obtain ⟨t, ht⟩ := h.edge_mem_iff.1 heG
        exact ⟨some t, ht⟩
    · simp only [Hypergraph.biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, hinc⟩
        exact inc_of_le (h.le (projAttach t₀ a)) hinc
      · intro hincG
        obtain ⟨t, ht⟩ := h.inc_iff.1 hincG
        exact ⟨some t, ht⟩
  · intro a b hne
    by_cases hproj : projAttach t₀ a = projAttach t₀ b
    · have ha : projAttach t₀ a = t₀ := by
        cases a <;> cases b
        · exact (hne rfl).elim
        · exact rfl
        · exact hproj
        · exact (hne (congrArg Option.some hproj)).elim
      change (τ (projAttach t₀ a)).edgeSet ∩ (τ (projAttach t₀ b)).edgeSet = ∅
      rw [← hproj, ha, ht₀_empty, Set.inter_self]
    · exact h.edgeSet_inter_eq hproj
  · intro a c b hp
    exact h.inter_le (onTreePath_projAttach_of_splitVertex hp)
  · rw [treeDecompWidthPlusOne_le_iff]
    intro a
    exact ncard_vertexSet_le_treeDecompWidthPlusOne τ (projAttach t₀ a)

/-- **Claim (3) of (5.1)** (Graph Minors X, Section 5, page 169):
"(3) *We may assume that every vertex of $T$ has valency $\le 3$." -/
theorem theorem_5_1_claim_3 [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ)
    (hc1 : ∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T, τ t = edgeHypergraph G e)
    (hc2 : ∀ t ∈ leafSet T, ∃ e ∈ G.edgeSet, τ t = edgeHypergraph G e)
    (hnonleaf : ∀ t ∉ leafSet T, (τ t).edgeSet = ∅) :
    ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (τ' : ι' → Hypergraph α β),
      IsTreeDecomposition G T' τ' ∧
      treeDecompWidthPlusOne τ' ≤ treeDecompWidthPlusOne τ ∧
      (∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T', τ' t = edgeHypergraph G e) ∧
      (∀ t ∈ leafSet T', ∃ e ∈ G.edgeSet, τ' t = edgeHypergraph G e) ∧
      (∀ t ∉ leafSet T', (τ' t).edgeSet = ∅) ∧
      (∀ t : ι', by classical exact T'.degree t ≤ 3) := by
  classical
  have hmain : ∀ (m : ℕ) (ι₀ : Type) [Fintype ι₀] (T₀ : SimpleGraph ι₀)
      (τ₀ : ι₀ → Hypergraph α β),
      IsTreeDecomposition G T₀ τ₀ →
      (∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T₀, τ₀ t = edgeHypergraph G e) →
      (∀ t ∈ leafSet T₀, ∃ e ∈ G.edgeSet, τ₀ t = edgeHypergraph G e) →
      (∀ t ∉ leafSet T₀, (τ₀ t).edgeSet = ∅) →
      (∑ x : ι₀, (T₀.degree x - 3)) = m →
      ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (τ' : ι' → Hypergraph α β),
        IsTreeDecomposition G T' τ' ∧
        treeDecompWidthPlusOne τ' ≤ treeDecompWidthPlusOne τ₀ ∧
        (∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T', τ' t = edgeHypergraph G e) ∧
        (∀ t ∈ leafSet T', ∃ e ∈ G.edgeSet, τ' t = edgeHypergraph G e) ∧
        (∀ t ∉ leafSet T', (τ' t).edgeSet = ∅) ∧
        (∀ t : ι', T'.degree t ≤ 3) := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro ι₀ _ T₀ τ₀ h₀ h1 h2 hnl hsum
      by_cases hex : ∃ t₀ : ι₀, 4 ≤ T₀.degree t₀
      · obtain ⟨t₀, ht₀_deg⟩ := hex
        have hcard_ge2 : 1 < (T₀.neighborFinset t₀).card := by
          rw [card_neighborFinset_eq_degree]
          omega
        obtain ⟨w₁, w₂, hw₁, hw₂, hw12⟩ := Finset.one_lt_card_iff.1 hcard_ge2
        have hadj₁ : T₀.Adj t₀ w₁ := (mem_neighborFinset T₀ t₀ w₁).1 hw₁
        have hadj₂ : T₀.Adj t₀ w₂ := (mem_neighborFinset T₀ t₀ w₂).1 hw₂
        have ht₀_not_leaf : t₀ ∉ leafSet T₀ := by
          intro hleaf
          change T₀.degree t₀ ≤ 1 at hleaf
          omega
        obtain ⟨h₁, hw₁_le⟩ :=
          splitVertex_isTreeDecomposition h₀ hadj₁ hadj₂ hw12 (hnl t₀ ht₀_not_leaf)
        let T₁ := splitVertex T₀ t₀ w₁ w₂
        let τ₁ : Option ι₀ → Hypergraph α β := fun a ↦ τ₀ (projAttach t₀ a)
        have hleaf_iff := mem_leafSet_splitVertex_iff hadj₁ hadj₂ hw12 ht₀_deg
        have h1' : ∀ e ∈ G.edgeSet, ∃ t ∈ leafSet T₁, τ₁ t = edgeHypergraph G e := by
          intro e heG
          obtain ⟨x, hx_leaf, hτ_x⟩ := h1 e heG
          exact ⟨some x, (hleaf_iff (some x)).2 ⟨x, hx_leaf, rfl⟩, hτ_x⟩
        have h2' : ∀ a ∈ leafSet T₁, ∃ e ∈ G.edgeSet, τ₁ a = edgeHypergraph G e := by
          intro a ha_leaf
          obtain ⟨x, hx_leaf, rfl⟩ := (hleaf_iff a).1 ha_leaf
          exact h2 x hx_leaf
        have hnl' : ∀ a ∉ leafSet T₁, (τ₁ a).edgeSet = ∅ := by
          rintro (_ | x) ha_not
          · exact hnl t₀ ht₀_not_leaf
          · exact hnl x (fun hx ↦ ha_not ((hleaf_iff (some x)).2 ⟨x, hx, rfl⟩))
        have hlt : (∑ a : Option ι₀, (T₁.degree a - 3)) < m := by
          rw [← hsum]
          exact sum_degree_sub_three_splitVertex_lt hadj₁ hadj₂ hw12 ht₀_deg
        obtain ⟨ι', hfin', T', τ', h', hw', hc1', hc2', hnl'', hdeg'⟩ :=
          ih (∑ a : Option ι₀, (T₁.degree a - 3)) hlt (Option ι₀) T₁ τ₁ h₁ h1' h2' hnl' rfl
        exact ⟨ι', hfin', T', τ', h', hw'.trans hw₁_le, hc1', hc2', hnl'', hdeg'⟩
      · push Not at hex
        exact ⟨ι₀, inferInstance, T₀, τ₀, h₀, le_rfl, h1, h2, hnl, fun t ↦ by have := hex t; omega⟩
  let eFin := Fintype.equivFin ι
  have hc1_fin : ∀ e ∈ G.edgeSet, ∃ t ∈ leafSet (T.map eFin.toEmbedding),
      (τ ∘ eFin.symm) t = edgeHypergraph G e := by
    intro e heG
    obtain ⟨t, ht_leaf, hτ_t⟩ := hc1 e heG
    refine ⟨eFin t, (isLeaf_map eFin t).2 ht_leaf, ?_⟩
    simpa using hτ_t
  have hc2_fin : ∀ t ∈ leafSet (T.map eFin.toEmbedding),
      ∃ e ∈ G.edgeSet, (τ ∘ eFin.symm) t = edgeHypergraph G e := by
    intro t ht_leaf
    obtain ⟨x, rfl⟩ := eFin.surjective t
    rw [leafSet, Set.mem_ofPred_eq, isLeaf_map] at ht_leaf
    simpa using hc2 x ht_leaf
  have hnl_fin : ∀ t ∉ leafSet (T.map eFin.toEmbedding),
      ((τ ∘ eFin.symm) t).edgeSet = ∅ := by
    intro t ht_not
    obtain ⟨x, rfl⟩ := eFin.surjective t
    rw [leafSet, Set.mem_ofPred_eq, isLeaf_map] at ht_not
    simpa using hnonleaf x ht_not
  obtain ⟨ι', hfin', T', τ', h', hw', hc1', hc2', hnl', hdeg'⟩ :=
    hmain _ (Fin (Fintype.card ι)) (T.map eFin.toEmbedding) (τ ∘ eFin.symm)
      (h.relabel eFin) hc1_fin hc2_fin hnl_fin rfl
  rw [treeDecompWidthPlusOne_comp_equiv] at hw'
  refine ⟨ι', hfin', T', τ', h', hw', hc1', hc2', hnl', fun t ↦ ?_⟩
  convert hdeg' t

end GraphMinor.GM10
