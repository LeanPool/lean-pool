/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Defs2
public import LeanPool.GraphMinor.GM10.TangleLemmas
public import LeanPool.GraphMinor.GM10.BranchWidth

/-!
# Graph Minors XVII, Section 14: Hypergraph Form of the Excluded Minor Theorem

This file formalizes Section 14 (pages 207–210) of Robertson and Seymour, *Graph Minors. XVII.
Taming a Vortex*, J. Combin. Theory Ser. B 77 (1999), 162–210.
-/

public section

namespace GraphMinor.GM17

open Set Function
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Tangles in the 1-Skeleton: (14.1) (Pages 207–209) -/

/-- Every separation `(A', B')` of `G*` lifts to a separation `(A, B)` of `G` with the same vertex
sets `V(A) = V(A')` and `V(B) = V(B')`. -/
theorem exists_separation_of_oneSkeletonHypergraph_separation
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {A' B' : Hypergraph α (Sym2 α)}
    (hsep' : (oneSkeletonHypergraph G).IsSeparation A' B') :
    ∃ A B : Hypergraph α β, G.IsSeparation A B ∧
      A.vertexSet = A'.vertexSet ∧ B.vertexSet = B'.vertexSet := by
  have hends : ∀ e ∈ G.edgeSet, G.ends e ⊆ A'.vertexSet ∨ G.ends e ⊆ B'.vertexSet := by
    intro e he
    by_contra! hnot
    rcases hnot with ⟨hnotA, hnotB⟩
    obtain ⟨u, hu, huA⟩ := not_subset.mp hnotA
    obtain ⟨v, hv, hvB⟩ := not_subset.mp hnotB
    have huv_ne : u ≠ v := by
      rintro rfl
      have huG : u ∈ G.vertexSet := G.vertex_mem_of_inc hu
      have huAB : u ∈ A'.vertexSet ∪ B'.vertexSet := hsep'.vertexSet_union.symm ▸ huG
      exact huAB.elim huA hvB
    have hs_edge : s(u, v) ∈ (oneSkeletonHypergraph G).edgeSet := by
      change s(u, v) ∈ G.skeleton.edgeSet
      rw [SimpleGraph.mem_edgeSet]
      exact ⟨huv_ne, e, hu, hv⟩
    have hs_AB : s(u, v) ∈ A'.edgeSet ∪ B'.edgeSet := hsep'.edgeSet_union.symm ▸ hs_edge
    rcases hs_AB with hsA | hsB
    · have hu_inc : A'.Inc s(u, v) u :=
        (inc_iff_of_le hsep'.left_le hsA).2 ⟨hs_edge, Sym2.mem_mk_left u v⟩
      exact huA (A'.vertex_mem_of_inc hu_inc)
    · have hv_inc : B'.Inc s(u, v) v :=
        (inc_iff_of_le hsep'.right_le hsB).2 ⟨hs_edge, Sym2.mem_mk_right u v⟩
      exact hvB (B'.vertex_mem_of_inc hv_inc)
  let A : Hypergraph α β :=
    { vertexSet := A'.vertexSet
      edgeSet := {e ∈ G.edgeSet | G.ends e ⊆ A'.vertexSet}
      Inc := fun e v => (e ∈ G.edgeSet ∧ G.ends e ⊆ A'.vertexSet) ∧ G.Inc e v
      vertex_mem_of_inc := fun _ _ h => h.1.2 h.2
      edge_mem_of_inc := fun _ _ h => h.1
      vertexSet_finite := A'.vertexSet_finite
      edgeSet_finite := G.edgeSet_finite.subset fun _ h => h.1 }
  let B : Hypergraph α β :=
    { vertexSet := B'.vertexSet
      edgeSet := {e ∈ G.edgeSet | ¬ G.ends e ⊆ A'.vertexSet}
      Inc := fun e v => (e ∈ G.edgeSet ∧ ¬ G.ends e ⊆ A'.vertexSet) ∧ G.Inc e v
      vertex_mem_of_inc := fun e _ h => (hends e h.1.1).resolve_left h.1.2 h.2
      edge_mem_of_inc := fun _ _ h => h.1
      vertexSet_finite := B'.vertexSet_finite
      edgeSet_finite := G.edgeSet_finite.subset fun _ h => h.1 }
  have hA_le : A ≤ G :=
    { vertexSet_subset := hsep'.left_le.vertexSet_subset
      edgeSet_subset := fun _ h => h.1
      ends_eq := fun e he => by ext v; exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩ }
  have hB_le : B ≤ G :=
    { vertexSet_subset := hsep'.right_le.vertexSet_subset
      edgeSet_subset := fun _ h => h.1
      ends_eq := fun e he => by ext v; exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩ }
  refine ⟨A, B, (isSeparation_iff_of_le hA_le hB_le).2 ⟨hsep'.vertexSet_union, ?_, ?_⟩, rfl, rfl⟩
  · ext e
    simp only [A, B, mem_union, mem_sep_iff]
    exact ⟨fun h => h.elim And.left And.left, fun he => by
      by_cases h : G.ends e ⊆ A'.vertexSet
      · exact Or.inl ⟨he, h⟩
      · exact Or.inr ⟨he, h⟩⟩
  · ext e
    change (e ∈ G.edgeSet ∧ G.ends e ⊆ A'.vertexSet) ∧
      (e ∈ G.edgeSet ∧ ¬ G.ends e ⊆ A'.vertexSet) ↔ False
    tauto

/-- Given `(A, B) ∈ 𝒯` and `W ⊆ V(B)` with `|(V(A) ∪ W) ∩ V(B)| < θ`, there is a separation
`(A⁺, B⁻) ∈ 𝒯` with `V(A⁺) = V(A) ∪ W`, `V(B⁻) = V(B)`, and
`E(A⁺) = {e ∈ E(G) | G.ends e ⊆ V(A) ∪ W}`. -/
private theorem exists_maximal_separation_in_tangle
    {α : Type u} {β : Type v} {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯)
    {W : Set α} (hWB : W ⊆ B.vertexSet)
    (hord : ((A.vertexSet ∪ W) ∩ B.vertexSet).ncard < θ) :
    ∃ Aplus Bminus : Hypergraph α β, (Aplus, Bminus) ∈ 𝒯 ∧
      Aplus.vertexSet = A.vertexSet ∪ W ∧
      Bminus.vertexSet = B.vertexSet ∧
      Aplus.edgeSet = {e ∈ G.edgeSet | G.ends e ⊆ A.vertexSet ∪ W} := by
  have hsep := h𝒯.isSeparation hAB
  have hWG : W ⊆ G.vertexSet := hWB.trans hsep.right_le.vertexSet_subset
  have hends_B : ∀ e ∈ G.edgeSet, ¬ G.ends e ⊆ A.vertexSet ∪ W → G.ends e ⊆ B.vertexSet := by
    intro e he hnot
    have he_not_A : e ∉ A.edgeSet := by
      intro heA
      apply hnot
      intro v hv
      have hvA : A.Inc e v := (inc_iff_of_le hsep.left_le heA).2 hv
      exact Or.inl (A.vertex_mem_of_inc hvA)
    have heB : e ∈ B.edgeSet := (hsep.edgeSet_union.symm ▸ he).resolve_left he_not_A
    intro v hv
    exact B.vertex_mem_of_inc ((inc_iff_of_le hsep.right_le heB).2 hv)
  let Aplus : Hypergraph α β :=
    { vertexSet := A.vertexSet ∪ W
      edgeSet := {e ∈ G.edgeSet | G.ends e ⊆ A.vertexSet ∪ W}
      Inc := fun e v => (e ∈ G.edgeSet ∧ G.ends e ⊆ A.vertexSet ∪ W) ∧ G.Inc e v
      vertex_mem_of_inc := fun _ _ h => h.1.2 h.2
      edge_mem_of_inc := fun _ _ h => h.1
      vertexSet_finite := A.vertexSet_finite.union (B.vertexSet_finite.subset hWB)
      edgeSet_finite := G.edgeSet_finite.subset fun _ h => h.1 }
  let Bminus : Hypergraph α β :=
    { vertexSet := B.vertexSet
      edgeSet := {e ∈ G.edgeSet | ¬ G.ends e ⊆ A.vertexSet ∪ W}
      Inc := fun e v => (e ∈ G.edgeSet ∧ ¬ G.ends e ⊆ A.vertexSet ∪ W) ∧ G.Inc e v
      vertex_mem_of_inc := fun e _ h => hends_B e h.1.1 h.1.2 h.2
      edge_mem_of_inc := fun _ _ h => h.1
      vertexSet_finite := B.vertexSet_finite
      edgeSet_finite := G.edgeSet_finite.subset fun _ h => h.1 }
  have hAplus_le : Aplus ≤ G :=
    { vertexSet_subset := union_subset hsep.left_le.vertexSet_subset hWG
      edgeSet_subset := fun _ h => h.1
      ends_eq := fun e he => by ext v; exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩ }
  have hBminus_le : Bminus ≤ G :=
    { vertexSet_subset := hsep.right_le.vertexSet_subset
      edgeSet_subset := fun _ h => h.1
      ends_eq := fun e he => by ext v; exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩ }
  have hsep_new : G.IsSeparation Aplus Bminus := by
    rw [isSeparation_iff_of_le hAplus_le hBminus_le]
    refine ⟨?_, ?_, ?_⟩
    · change (A.vertexSet ∪ W) ∪ B.vertexSet = G.vertexSet
      rw [Set.union_assoc, union_eq_right.mpr hWB, hsep.vertexSet_union]
    · ext e
      simp only [Aplus, Bminus, mem_union, mem_sep_iff]
      exact ⟨fun h => h.elim And.left And.left, fun he => by
        by_cases h : G.ends e ⊆ A.vertexSet ∪ W
        · exact Or.inl ⟨he, h⟩
        · exact Or.inr ⟨he, h⟩⟩
    · ext e
      change (e ∈ G.edgeSet ∧ G.ends e ⊆ A.vertexSet ∪ W) ∧
        (e ∈ G.edgeSet ∧ ¬ G.ends e ⊆ A.vertexSet ∪ W) ↔ False
      tauto
  have hmem : (Aplus, Bminus) ∈ 𝒯 :=
    theorem_2_9_case_1 h𝒯 hAB hsep_new hord subset_rfl
  exact ⟨Aplus, Bminus, hmem, rfl, rfl, rfl⟩

/-- Claim (1) in the proof of **Graph Minors XVII, (14.1)** (page 208):
"If $(A'_1, B'_1), (A'_2, B'_2) \in \mathscr{T}^*$ then $B'_1 \not\subseteq A'_2$." -/
theorem theorem_14_1_claim_1
    {α : Type u} {β : Type v} {G : Hypergraph α β} {θ θstar : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A'₁ B'₁ A'₂ B'₂ : Hypergraph α (Sym2 α)}
    (h1 : (A'₁, B'₁) ∈ oneSkeletonTangle G 𝒯 θstar)
    (h2 : (A'₂, B'₂) ∈ oneSkeletonTangle G 𝒯 θstar) :
    ¬ B'₁ ≤ A'₂ := by
  intro hle
  obtain ⟨_, _, ⟨A₁, B₁⟩, hAB₁, hVA₁, hVB₁⟩ := h1
  obtain ⟨_, _, ⟨A₂, B₂⟩, hAB₂, hVA₂, hVB₂⟩ := h2
  have hsub : B₁.vertexSet ⊆ A₂.vertexSet := by
    rw [hVB₁, hVA₂]
    exact hle.vertexSet_subset
  have hsep₂ := (h𝒯.isSeparation hAB₂).symm
  have hord₂ : separationOrder B₂ A₂ < θ := by
    rw [separationOrder_comm]
    exact h𝒯.order_lt hAB₂
  have hB₂A₂ : (B₂, A₂) ∈ 𝒯 := theorem_2_9_case_1 h𝒯 hAB₁ hsep₂ hord₂ hsub
  exact GraphMinor.GM10.theorem_2_1_proof h𝒯 hAB₂ hB₂A₂

/-- Claim (2) in the proof of **Graph Minors XVII, (14.1)** (page 208):
"There do not exist subhypergraphs $A'_1$, $A'_2$, $A'_3$ of $G^*$, mutually edge-disjoint, with
$A'_1 \cup A'_2 \cup A'_3 = G^*$, and with $(A'_1, A'_2 \cup A'_3)$, $(A'_2, A'_3 \cup A'_1)$,
$(A'_3, A'_1 \cup A'_2)$ all in $\mathscr{T}^*$." -/
theorem theorem_14_1_claim_2
    {α : Type u} {β : Type v} {G : Hypergraph α β} {θ θstar : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hlt : 3 * θstar < 2 * θ + 3) (h𝒯 : IsTangle G θ 𝒯) :
    ¬ ∃ A'₁ A'₂ A'₃ : Hypergraph α (Sym2 α),
      A'₁ ≤ oneSkeletonHypergraph G ∧
      A'₂ ≤ oneSkeletonHypergraph G ∧
      A'₃ ≤ oneSkeletonHypergraph G ∧
      Disjoint A'₁.edgeSet A'₂.edgeSet ∧
      Disjoint A'₁.edgeSet A'₃.edgeSet ∧
      Disjoint A'₂.edgeSet A'₃.edgeSet ∧
      A'₁ ∪ A'₂ ∪ A'₃ = oneSkeletonHypergraph G ∧
      (A'₁, A'₂ ∪ A'₃) ∈ oneSkeletonTangle G 𝒯 θstar ∧
      (A'₂, A'₃ ∪ A'₁) ∈ oneSkeletonTangle G 𝒯 θstar ∧
      (A'₃, A'₁ ∪ A'₂) ∈ oneSkeletonTangle G 𝒯 θstar := by
  rintro ⟨A'₁, A'₂, A'₃, _, _, _, _, _, _, hU', hm1, hm2, hm3⟩
  let B'₁ := A'₂ ∪ A'₃
  let B'₂ := A'₃ ∪ A'₁
  let B'₃ := A'₁ ∪ A'₂
  let V₁ := A'₁.vertexSet
  let V₂ := A'₂.vertexSet
  let V₃ := A'₃.vertexSet
  let W₀ := V₁ ∩ V₂ ∩ V₃
  let W₁ := (V₂ ∩ V₃) \ V₁
  let W₂ := (V₃ ∩ V₁) \ V₂
  let W₃ := (V₁ ∩ V₂) \ V₃
  let W := W₀ ∪ W₁ ∪ W₂ ∪ W₃
  have hW₀_fin : W₀.Finite := A'₁.vertexSet_finite.subset (inter_subset_left.trans
    inter_subset_left)
  have hW₁_fin : W₁.Finite := A'₂.vertexSet_finite.subset (sdiff_subset.trans inter_subset_left)
  have hW₂_fin : W₂.Finite := A'₃.vertexSet_finite.subset (sdiff_subset.trans inter_subset_left)
  have hW₃_fin : W₃.Finite := A'₁.vertexSet_finite.subset (sdiff_subset.trans inter_subset_left)
  have hdisj01 : Disjoint W₀ W₁ := Set.disjoint_left.mpr fun _ h0 h1 => h1.2 h0.1.1
  have hdisj02 : Disjoint W₀ W₂ := Set.disjoint_left.mpr fun _ h0 h2 => h2.2 h0.1.2
  have hdisj03 : Disjoint W₀ W₃ := Set.disjoint_left.mpr fun _ h0 h3 => h3.2 h0.2
  have hdisj12 : Disjoint W₁ W₂ := Set.disjoint_left.mpr fun _ h1 h2 => h1.2 h2.1.2
  have hdisj13 : Disjoint W₁ W₃ := Set.disjoint_left.mpr fun _ h1 h3 => h1.2 h3.1.1
  have hdisj23 : Disjoint W₂ W₃ := Set.disjoint_left.mpr fun _ h2 h3 => h2.2 h3.1.2
  have hI₁ : V₁ ∩ (V₂ ∪ V₃) = W₀ ∪ W₂ ∪ W₃ := by
    ext x
    simp only [W₀, W₂, W₃, mem_inter_iff, mem_union, mem_sdiff]
    tauto
  have hI₂ : V₂ ∩ (V₃ ∪ V₁) = W₀ ∪ W₃ ∪ W₁ := by
    ext x
    simp only [W₀, W₃, W₁, mem_inter_iff, mem_union, mem_sdiff]
    tauto
  have hI₃ : V₃ ∩ (V₁ ∪ V₂) = W₀ ∪ W₁ ∪ W₂ := by
    ext x
    simp only [W₀, W₁, W₂, mem_inter_iff, mem_union, mem_sdiff]
    tauto
  have hcard1 : (W₀ ∪ W₂ ∪ W₃).ncard = W₀.ncard + W₂.ncard + W₃.ncard := by
    rw [ncard_union_eq (hdisj03.union_left hdisj23) (hW₀_fin.union hW₂_fin) hW₃_fin,
      ncard_union_eq hdisj02 hW₀_fin hW₂_fin]
  have hcard2 : (W₀ ∪ W₃ ∪ W₁).ncard = W₀.ncard + W₃.ncard + W₁.ncard := by
    rw [ncard_union_eq (hdisj01.union_left hdisj13.symm) (hW₀_fin.union hW₃_fin) hW₁_fin,
      ncard_union_eq hdisj03 hW₀_fin hW₃_fin]
  have hcard3 : (W₀ ∪ W₁ ∪ W₂).ncard = W₀.ncard + W₁.ncard + W₂.ncard := by
    rw [ncard_union_eq (hdisj02.union_left hdisj12) (hW₀_fin.union hW₁_fin) hW₂_fin,
      ncard_union_eq hdisj01 hW₀_fin hW₁_fin]
  have hcardW : W.ncard = W₀.ncard + W₁.ncard + W₂.ncard + W₃.ncard := by
    dsimp [W]
    rw [ncard_union_eq ((hdisj03.union_left hdisj13).union_left hdisj23)
      ((hW₀_fin.union hW₁_fin).union hW₂_fin) hW₃_fin, hcard3]
  have hord1 : W₀.ncard + W₂.ncard + W₃.ncard < θstar := by
    have h : (V₁ ∩ (V₂ ∪ V₃)).ncard < θstar := hm1.2.1
    rwa [hI₁, hcard1] at h
  have hord2 : W₀.ncard + W₃.ncard + W₁.ncard < θstar := by
    have h : (V₂ ∩ (V₃ ∪ V₁)).ncard < θstar := hm2.2.1
    rwa [hI₂, hcard2] at h
  have hord3 : W₀.ncard + W₁.ncard + W₂.ncard < θstar := by
    have h : (V₃ ∩ (V₁ ∪ V₂)).ncard < θstar := hm3.2.1
    rwa [hI₃, hcard3] at h
  have hW_lt : W.ncard < θ := by
    rw [hcardW]
    omega
  obtain ⟨hsep'1, _, ⟨A₁₀, B₁₀⟩, hAB₁₀, hVA₁₀, hVB₁₀⟩ := hm1
  obtain ⟨hsep'2, _, ⟨A₂₀, B₂₀⟩, hAB₂₀, hVA₂₀, hVB₂₀⟩ := hm2
  obtain ⟨hsep'3, _, ⟨A₃₀, B₃₀⟩, hAB₃₀, hVA₃₀, hVB₃₀⟩ := hm3
  change A₁₀.vertexSet = V₁ at hVA₁₀
  change B₁₀.vertexSet = V₂ ∪ V₃ at hVB₁₀
  change A₂₀.vertexSet = V₂ at hVA₂₀
  change B₂₀.vertexSet = V₃ ∪ V₁ at hVB₂₀
  change A₃₀.vertexSet = V₃ at hVA₃₀
  change B₃₀.vertexSet = V₁ ∪ V₂ at hVB₃₀
  have hW₁_sub : W₁ ⊆ B₁₀.vertexSet := by
    rw [hVB₁₀]
    exact fun _ hx => Or.inl hx.1.1
  have hW₂_sub : W₂ ⊆ B₂₀.vertexSet := by
    rw [hVB₂₀]
    exact fun _ hx => Or.inl hx.1.1
  have hW₃_sub : W₃ ⊆ B₃₀.vertexSet := by
    rw [hVB₃₀]
    exact fun _ hx => Or.inl hx.1.1
  have hW_eq1 : (A₁₀.vertexSet ∪ W₁) ∩ B₁₀.vertexSet = W := by
    rw [hVA₁₀, union_inter_distrib_right, inter_eq_left.mpr hW₁_sub, hVB₁₀, hI₁]
    dsimp [W]
    ac_rfl
  have hW_eq2 : (A₂₀.vertexSet ∪ W₂) ∩ B₂₀.vertexSet = W := by
    rw [hVA₂₀, union_inter_distrib_right, inter_eq_left.mpr hW₂_sub, hVB₂₀, hI₂]
    dsimp [W]
    ac_rfl
  have hW_eq3 : (A₃₀.vertexSet ∪ W₃) ∩ B₃₀.vertexSet = W := by
    rw [hVA₃₀, union_inter_distrib_right, inter_eq_left.mpr hW₃_sub, hVB₃₀, hI₃]
  obtain ⟨A₁, B₁, hAB₁, hVA₁, _, hEA₁⟩ :=
    exists_maximal_separation_in_tangle h𝒯 hAB₁₀ hW₁_sub (hW_eq1.symm ▸ hW_lt)
  obtain ⟨A₂, B₂, hAB₂, hVA₂, _, hEA₂⟩ :=
    exists_maximal_separation_in_tangle h𝒯 hAB₂₀ hW₂_sub (hW_eq2.symm ▸ hW_lt)
  obtain ⟨A₃, B₃, hAB₃, hVA₃, _, hEA₃⟩ :=
    exists_maximal_separation_in_tangle h𝒯 hAB₃₀ hW₃_sub (hW_eq3.symm ▸ hW_lt)
  rw [hVA₁₀] at hVA₁ hEA₁
  rw [hVA₂₀] at hVA₂ hEA₂
  rw [hVA₃₀] at hVA₃ hEA₃
  have hW_sub_1 : W ⊆ V₁ ∪ W₁ := by
    have : W = (V₁ ∩ (V₂ ∪ V₃)) ∪ W₁ := by
      rw [hI₁]; dsimp [W]; ac_rfl
    rw [this]
    exact union_subset_union_left _ inter_subset_left
  have hU'_V : (V₁ ∪ V₂) ∪ V₃ = G.vertexSet :=
    congrArg Hypergraph.vertexSet hU'
  have hV_union : (A₁ ∪ A₂ ∪ A₃).vertexSet = G.vertexSet := by
    have hle := union_le (union_le (h𝒯.isSeparation hAB₁).left_le (h𝒯.isSeparation hAB₂).left_le)
      (h𝒯.isSeparation hAB₃).left_le
    refine Subset.antisymm hle.vertexSet_subset ?_
    rw [← hU'_V]
    intro x hx
    simp only [union_vertexSet, hVA₁, hVA₂, hVA₃, mem_union] at hx ⊢
    tauto
  have hE_union : (A₁ ∪ A₂ ∪ A₃).edgeSet = G.edgeSet := by
    have hle := union_le (union_le (h𝒯.isSeparation hAB₁).left_le (h𝒯.isSeparation hAB₂).left_le)
      (h𝒯.isSeparation hAB₃).left_le
    refine Subset.antisymm hle.edgeSet_subset ?_
    intro e heG
    simp only [union_edgeSet, hEA₁, hEA₂, hEA₃, mem_union, mem_sep_iff]
    by_cases hsubW : G.ends e ⊆ W
    · exact Or.inl (Or.inl ⟨heG, hsubW.trans hW_sub_1⟩)
    · obtain ⟨v, hv_end, hv_notW⟩ := not_subset.mp hsubW
      have hvG : v ∈ (V₁ ∪ V₂) ∪ V₃ :=
        hU'_V.symm ▸ G.vertex_mem_of_inc hv_end
      have hadj_sub : ∀ {A' B' : Hypergraph α (Sym2 α)},
          (oneSkeletonHypergraph G).IsSeparation A' B' →
          v ∈ A'.vertexSet → v ∉ B'.vertexSet → G.ends e ⊆ A'.vertexSet := by
        intro A' B' hsep' hvA' hv_notB' v' hv'_end
        by_cases hvv' : v' = v
        · exact hvv' ▸ hvA'
        · have hs_edge : s(v, v') ∈ (oneSkeletonHypergraph G).edgeSet := by
            change s(v, v') ∈ G.skeleton.edgeSet
            rw [SimpleGraph.mem_edgeSet]
            exact ⟨Ne.symm hvv', e, hv_end, hv'_end⟩
          rcases hsep'.edgeSet_union.symm ▸ hs_edge with hsA | hsB
          · exact A'.vertex_mem_of_inc
              ((inc_iff_of_le hsep'.left_le hsA).2 ⟨hs_edge, Sym2.mem_mk_right v v'⟩)
          · exfalso
            exact hv_notB' (B'.vertex_mem_of_inc
              ((inc_iff_of_le hsep'.right_le hsB).2 ⟨hs_edge, Sym2.mem_mk_left v v'⟩))
      have hv_not1 : v ∉ V₁ ∩ (V₂ ∪ V₃) := by
        rw [hI₁]
        intro h
        apply hv_notW
        simp only [W, mem_union] at h ⊢
        tauto
      have hv_not2 : v ∉ V₂ ∩ (V₃ ∪ V₁) := by
        rw [hI₂]
        intro h
        apply hv_notW
        simp only [W, mem_union] at h ⊢
        tauto
      have hv_not3 : v ∉ V₃ ∩ (V₁ ∪ V₂) := by
        rw [hI₃]
        intro h
        apply hv_notW
        simp only [W, mem_union] at h ⊢
        tauto
      rcases hvG with (hv1 | hv2) | hv3
      · have hnotB1 : v ∉ B'₁.vertexSet := fun hB => hv_not1 ⟨hv1, hB⟩
        exact Or.inl (Or.inl ⟨heG, (hadj_sub hsep'1 hv1 hnotB1).trans subset_union_left⟩)
      · have hnotB2 : v ∉ B'₂.vertexSet := fun hB => hv_not2 ⟨hv2, hB⟩
        exact Or.inl (Or.inr ⟨heG, (hadj_sub hsep'2 hv2 hnotB2).trans subset_union_left⟩)
      · have hnotB3 : v ∉ B'₃.vertexSet := fun hB => hv_not3 ⟨hv3, hB⟩
        exact Or.inr ⟨heG, (hadj_sub hsep'3 hv3 hnotB3).trans subset_union_left⟩
  have hle_all := union_le (union_le (h𝒯.isSeparation hAB₁).left_le (h𝒯.isSeparation hAB₂).left_le)
    (h𝒯.isSeparation hAB₃).left_le
  exact h𝒯.axiom2 hAB₁ hAB₂ hAB₃
    (eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle_all le_rfl hV_union hE_union)

/-- **Graph Minors XVII, (14.1)** (page 207):
"Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$. Let $\theta^* \ge 1$ with
$\theta^* < 2/3\theta + 1$, and let $\mathscr{T}^*$ be the set of all separations $(A', B')$ of
$G^*$ of order $< \theta^*$ such that there exists $(A, B) \in \mathscr{T}$ with $V(A) = V(A')$
and $V(B) = V(B')$. Then $\mathscr{T}^*$ is a tangle in $G^*$ of order $\theta^*$." -/
theorem theorem_14_1_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β} {θ θstar : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h1 : 1 ≤ θstar) (hlt : 3 * θstar < 2 * θ + 3) (h𝒯 : IsTangle G θ 𝒯) :
    IsTangle (oneSkeletonHypergraph G) θstar (oneSkeletonTangle G 𝒯 θstar) := by
  have hθ_ge1 : 1 ≤ θ := h𝒯.one_le
  have hθstar_le_θ : θstar ≤ θ := by omega
  have hsep : ∀ ⦃A' B'⦄, (A', B') ∈ oneSkeletonTangle G 𝒯 θstar →
      (oneSkeletonHypergraph G).IsSeparation A' B' := fun _ _ h => h.1
  have hord : ∀ ⦃A' B'⦄, (A', B') ∈ oneSkeletonTangle G 𝒯 θstar →
      separationOrder A' B' < θstar := fun _ _ h => h.2.1
  have hax1 : TangleAxiom1 (oneSkeletonHypergraph G) θstar (oneSkeletonTangle G 𝒯 θstar) := by
    intro A' B' hsep' hord'
    obtain ⟨A, B, hsepAB, hVA, hVB⟩ := exists_separation_of_oneSkeletonHypergraph_separation hsep'
    have hordAB : separationOrder A B < θ := by
      change (A.vertexSet ∩ B.vertexSet).ncard < θ
      rw [hVA, hVB]
      exact hord'.trans_le hθstar_le_θ
    rcases h𝒯.axiom1 hsepAB hordAB with hAB | hBA
    · exact Or.inl ⟨hsep', hord', ⟨(A, B), hAB, hVA, hVB⟩⟩
    · exact Or.inr ⟨hsep'.symm, by rwa [separationOrder_comm], ⟨(B, A), hBA, hVB, hVA⟩⟩
  have hax3 : TangleAxiom3 (oneSkeletonHypergraph G) (oneSkeletonTangle G 𝒯 θstar) := by
    intro A' B' ⟨_, _, ⟨A, B⟩, hAB, hVA, _⟩ hVA'_G
    exact h𝒯.axiom3 hAB (hVA.trans hVA'_G)
  refine ⟨h1, hsep, hord, hax1, ?_, hax3⟩
  by_cases h2 : 2 ≤ θstar
  · exact GraphMinor.GM10.theorem_4_5_proof h2 hsep hord hax1
      (fun _ _ _ _ hm1 hm2 => theorem_14_1_claim_1 h𝒯 hm1 hm2)
      (theorem_14_1_claim_2 hlt h𝒯)
  · have hθstar_eq1 : θstar = 1 := by omega
    intro A'₁ B'₁ A'₂ B'₂ A'₃ B'₃ hm1 hm2 hm3 hU'
    obtain ⟨hsep'1, hord'1, ⟨A₁₀, B₁₀⟩, hAB₁₀, hVA₁₀, hVB₁₀⟩ := hm1
    obtain ⟨hsep'2, hord'2, ⟨A₂₀, B₂₀⟩, hAB₂₀, hVA₂₀, hVB₂₀⟩ := hm2
    obtain ⟨hsep'3, hord'3, ⟨A₃₀, B₃₀⟩, hAB₃₀, hVA₃₀, hVB₃₀⟩ := hm3
    change separationOrder A'₁ B'₁ < θstar at hord'1
    change separationOrder A'₂ B'₂ < θstar at hord'2
    change separationOrder A'₃ B'₃ < θstar at hord'3
    change A₁₀.vertexSet = A'₁.vertexSet at hVA₁₀
    change B₁₀.vertexSet = B'₁.vertexSet at hVB₁₀
    change A₂₀.vertexSet = A'₂.vertexSet at hVA₂₀
    change B₂₀.vertexSet = B'₂.vertexSet at hVB₂₀
    change A₃₀.vertexSet = A'₃.vertexSet at hVA₃₀
    change B₃₀.vertexSet = B'₃.vertexSet at hVB₃₀
    have hemp1 : (A₁₀.vertexSet ∪ ∅) ∩ B₁₀.vertexSet = ∅ := by
      rw [union_empty, hVA₁₀, hVB₁₀]
      apply (ncard_eq_zero (A'₁ ∩ B'₁).vertexSet_finite).mp
      change separationOrder A'₁ B'₁ = 0
      omega
    have hemp2 : (A₂₀.vertexSet ∪ ∅) ∩ B₂₀.vertexSet = ∅ := by
      rw [union_empty, hVA₂₀, hVB₂₀]
      apply (ncard_eq_zero (A'₂ ∩ B'₂).vertexSet_finite).mp
      change separationOrder A'₂ B'₂ = 0
      omega
    have hemp3 : (A₃₀.vertexSet ∪ ∅) ∩ B₃₀.vertexSet = ∅ := by
      rw [union_empty, hVA₃₀, hVB₃₀]
      apply (ncard_eq_zero (A'₃ ∩ B'₃).vertexSet_finite).mp
      change separationOrder A'₃ B'₃ = 0
      omega
    have h0_lt_θ : (∅ : Set α).ncard < θ := by rw [ncard_empty]; omega
    obtain ⟨A₁, B₁, hAB₁, hVA₁, _, hEA₁⟩ :=
      exists_maximal_separation_in_tangle h𝒯 hAB₁₀ (empty_subset _) (hemp1.symm ▸ h0_lt_θ)
    obtain ⟨A₂, B₂, hAB₂, hVA₂, _, hEA₂⟩ :=
      exists_maximal_separation_in_tangle h𝒯 hAB₂₀ (empty_subset _) (hemp2.symm ▸ h0_lt_θ)
    obtain ⟨A₃, B₃, hAB₃, hVA₃, _, hEA₃⟩ :=
      exists_maximal_separation_in_tangle h𝒯 hAB₃₀ (empty_subset _) (hemp3.symm ▸ h0_lt_θ)
    rw [union_empty, hVA₁₀] at hVA₁ hEA₁
    rw [union_empty, hVA₂₀] at hVA₂ hEA₂
    rw [union_empty, hVA₃₀] at hVA₃ hEA₃
    have hle_all := union_le (union_le (h𝒯.isSeparation hAB₁).left_le
      (h𝒯.isSeparation hAB₂).left_le)
      (h𝒯.isSeparation hAB₃).left_le
    have hV_union : (A₁ ∪ A₂ ∪ A₃).vertexSet = G.vertexSet := by
      have hU'_V : (A'₁ ∪ A'₂ ∪ A'₃).vertexSet = G.vertexSet :=
        congrArg Hypergraph.vertexSet hU'
      simpa [union_vertexSet, hVA₁, hVA₂, hVA₃] using hU'_V
    have hE_union : (A₁ ∪ A₂ ∪ A₃).edgeSet = G.edgeSet := by
      refine Subset.antisymm hle_all.edgeSet_subset ?_
      intro e heG
      simp only [union_edgeSet, hEA₁, hEA₂, hEA₃, mem_union, mem_sep_iff]
      by_cases hne : (G.ends e).Nonempty
      · obtain ⟨v, hv_end⟩ := hne
        have hvG : v ∈ (A'₁ ∪ A'₂ ∪ A'₃).vertexSet :=
          hU'.symm ▸ (G.vertex_mem_of_inc hv_end : v ∈ (oneSkeletonHypergraph G).vertexSet)
        have hdisj_AB : ∀ {A' B' : Hypergraph α (Sym2 α)},
            (oneSkeletonHypergraph G).IsSeparation A' B' →
            (A'.vertexSet ∩ B'.vertexSet) = ∅ →
            v ∈ A'.vertexSet → G.ends e ⊆ A'.vertexSet := by
          intro A' B' hsep' hdisj hvA' v' hv'_end
          by_cases hvv' : v' = v
          · exact hvv' ▸ hvA'
          · have hs_edge : s(v, v') ∈ (oneSkeletonHypergraph G).edgeSet := by
              change s(v, v') ∈ G.skeleton.edgeSet
              rw [SimpleGraph.mem_edgeSet]
              exact ⟨Ne.symm hvv', e, hv_end, hv'_end⟩
            rcases hsep'.edgeSet_union.symm ▸ hs_edge with hsA | hsB
            · exact A'.vertex_mem_of_inc
                ((inc_iff_of_le hsep'.left_le hsA).2 ⟨hs_edge, Sym2.mem_mk_right v v'⟩)
            · exfalso
              have hvB' : v ∈ B'.vertexSet := B'.vertex_mem_of_inc
                ((inc_iff_of_le hsep'.right_le hsB).2 ⟨hs_edge, Sym2.mem_mk_left v v'⟩)
              exact notMem_empty v (hdisj ▸ ⟨hvA', hvB'⟩)
        rcases hvG with (hv1 | hv2) | hv3
        · rw [union_empty, hVA₁₀, hVB₁₀] at hemp1
          exact Or.inl (Or.inl ⟨heG, hdisj_AB hsep'1 hemp1 hv1⟩)
        · rw [union_empty, hVA₂₀, hVB₂₀] at hemp2
          exact Or.inl (Or.inr ⟨heG, hdisj_AB hsep'2 hemp2 hv2⟩)
        · rw [union_empty, hVA₃₀, hVB₃₀] at hemp3
          exact Or.inr ⟨heG, hdisj_AB hsep'3 hemp3 hv3⟩
      · rw [not_nonempty_iff_eq_empty] at hne
        exact Or.inl (Or.inl ⟨heG, hne.symm ▸ empty_subset _⟩)
    exact h𝒯.axiom2 hAB₁ hAB₂ hAB₃
      (eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle_all le_rfl hV_union hE_union)

end GraphMinor.GM17
