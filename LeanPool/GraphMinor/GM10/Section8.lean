/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs2
public import LeanPool.GraphMinor.GM10.Statements
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM10.Section6
import LeanPool.GraphMinor.GM10.TreeWidth

/-!
# Robust and Titanic Separations (Graph Minors X, Section 8)

This file formalizes Section 8 of Graph Minors X (pages 174–177):
- `theorem_8_1`: **Graph Minors X, (8.1)** (page 174).
- `theorem_8_2`: **Graph Minors X, (8.2)** (page 174), every titanic separation is robust.
- `theorem_8_3`: **Graph Minors X, (8.3)** (page 175), transferring a tangle across a titanic
  separation.
- `theorem_8_4`: **Graph Minors X, (8.4)** (page 176), deleting an edge with at most one end.
- `theorem_8_5`: **Graph Minors X, (8.5)** (page 177), deleting a set of `< θ` vertices in a graph.
-/

public section

namespace GraphMinor.GM10

open Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## Graph Minors X, (8.1) -/

/-- If `A ≤ G` and `(C, D)` is a separation of `G`, then `(A ∩ C, A ∩ D)` is a separation of `A`. -/
theorem _root_.GraphMinor.Hypergraph.IsSeparation.inter_left {G A C D : Hypergraph α β}
    (hCD : G.IsSeparation C D) (hA : A ≤ G) :
    A.IsSeparation (A ∩ C) (A ∩ D) := by
  have hAC : A ∩ C ≤ A := inter_le_left hA hCD.left_le
  have hAD : A ∩ D ≤ A := inter_le_left hA hCD.right_le
  rw [isSeparation_iff_of_le hAC hAD]
  refine ⟨?_, ?_, ?_⟩
  · change (A.vertexSet ∩ C.vertexSet) ∪ (A.vertexSet ∩ D.vertexSet) = A.vertexSet
    rw [← Set.inter_union_distrib_left, hCD.vertexSet_union,
      Set.inter_eq_left.2 hA.vertexSet_subset]
  · change (A.edgeSet ∩ C.edgeSet) ∪ (A.edgeSet ∩ D.edgeSet) = A.edgeSet
    rw [← Set.inter_union_distrib_left, hCD.edgeSet_union,
      Set.inter_eq_left.2 hA.edgeSet_subset]
  · ext e
    change e ∈ (A.edgeSet ∩ C.edgeSet) ∩ (A.edgeSet ∩ D.edgeSet) ↔ e ∈ (∅ : Set β)
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, heC⟩, ⟨_, heD⟩⟩
    exact hCD.notMem_edgeSet_right heC heD

/-- Submodularity identity for the orders of `(A, B)` and `(C, D)` in the proof of
**Graph Minors X, (8.1)** (page 174):
`|V(A ∩ B)| + |V(C ∩ D)| = |V((A ∩ C) ∩ (B ∪ D))| + |V((A ∪ C) ∩ (B ∩ D))|`. -/
theorem separationOrder_add_separationOrder {G A B C D : Hypergraph α β}
    (hAB : G.IsSeparation A B) (hCD : G.IsSeparation C D) :
    separationOrder A B + separationOrder C D =
      separationOrder (A ∩ C) (B ∪ D) + separationOrder (A ∪ C) (B ∩ D) := by
  let S₁ := (A ∩ B).vertexSet
  let S₂ := (C ∩ D).vertexSet
  let T₁ := ((A ∩ C) ∩ (B ∪ D)).vertexSet
  let T₂ := ((A ∪ C) ∩ (B ∩ D)).vertexSet
  have h_union : S₁ ∪ S₂ = T₁ ∪ T₂ := by
    ext v
    simp only [S₁, S₂, T₁, T₂, inter_vertexSet, union_vertexSet, Set.mem_union, Set.mem_inter_iff]
    constructor
    · intro h
      have hvG : v ∈ G.vertexSet := by
        rcases h with ⟨hvA, _⟩ | ⟨hvC, _⟩
        · exact hAB.left_le.vertexSet_subset hvA
        · exact hCD.left_le.vertexSet_subset hvC
      have hvAB : v ∈ A.vertexSet ∪ B.vertexSet := hAB.vertexSet_union.symm ▸ hvG
      have hvCD : v ∈ C.vertexSet ∪ D.vertexSet := hCD.vertexSet_union.symm ▸ hvG
      simp only [Set.mem_union] at hvAB hvCD
      tauto
    · tauto
  have h_inter : S₁ ∩ S₂ = T₁ ∩ T₂ := by
    ext v
    simp only [S₁, S₂, T₁, T₂, inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union]
    tauto
  have h1 := Set.ncard_union_add_ncard_inter S₁ S₂
    (A ∩ B).vertexSet_finite (C ∩ D).vertexSet_finite
  have h2 := Set.ncard_union_add_ncard_inter T₁ T₂
    ((A ∩ C) ∩ (B ∪ D)).vertexSet_finite ((A ∪ C) ∩ (B ∩ D)).vertexSet_finite
  rw [h_union, h_inter] at h1
  unfold separationOrder
  change S₁.ncard + S₂.ncard = T₁.ncard + T₂.ncard
  omega

/-- **Graph Minors X, (8.1)** (page 174):
"Let* $(A, B)$ *be a robust separation of* $G$, *and let* $(C, D)$ *be a separation of* $G$.
*Then one of* $(A \cup C, B \cap D)$, $(A \cup D, B \cap C)$ *has order at most that of*
$(C, D)$." -/
theorem theorem_8_1_proof {G A B C D : Hypergraph α β}
    (hAB : IsRobust G A B) (hCD : G.IsSeparation C D) :
    separationOrder (A ∪ C) (B ∩ D) ≤ separationOrder C D ∨
      separationOrder (A ∪ D) (B ∩ C) ≤ separationOrder C D := by
  have hACD : A.IsSeparation (A ∩ C) (A ∩ D) := hCD.inter_left hAB.1.left_le
  rcases hAB.2 hACD with h1 | h2
  · left
    have heq : ((A ∩ C) ∩ (B ∪ (A ∩ D))).vertexSet = ((A ∩ C) ∩ (B ∪ D)).vertexSet := by
      ext v
      simp only [inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union]
      tauto
    have h1' : separationOrder A B ≤ separationOrder (A ∩ C) (B ∪ D) := by
      unfold separationOrder at h1 ⊢
      rwa [heq] at h1
    have hsum := separationOrder_add_separationOrder hAB.1 hCD
    omega
  · right
    have heq : ((A ∩ D) ∩ (B ∪ (A ∩ C))).vertexSet = ((A ∩ D) ∩ (B ∪ C)).vertexSet := by
      ext v
      simp only [inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union]
      tauto
    have h2' : separationOrder A B ≤ separationOrder (A ∩ D) (B ∪ C) := by
      unfold separationOrder at h2 ⊢
      rwa [heq] at h2
    have hsum := separationOrder_add_separationOrder hAB.1 hCD.symm
    rw [separationOrder_comm D C] at hsum
    omega

/-! ## Graph Minors X, (8.2) -/

private lemma bot_le (G : Hypergraph α β) : (⊥ : Hypergraph α β) ≤ G where
  vertexSet_subset := Set.empty_subset _
  edgeSet_subset := Set.empty_subset _
  ends_eq _ h := h.elim

private lemma robust_step_of_ncard_le {A B C D : Hypergraph α β}
    (hCD : A.IsSeparation C D)
    (hle : (C ∩ B).vertexSet.ncard ≤ (C ∩ D).vertexSet.ncard) :
    separationOrder A B ≤ separationOrder D (B ∪ C) := by
  have h1 : (A ∩ B).vertexSet = (C ∩ B).vertexSet ∪ ((D ∩ B).vertexSet \ C.vertexSet) := by
    ext v
    have hU := Set.ext_iff.1 hCD.vertexSet_union v
    simp only [inter_vertexSet, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff] at hU ⊢
    tauto
  have h2 : (D ∩ (B ∪ C)).vertexSet = (C ∩ D).vertexSet ∪ ((D ∩ B).vertexSet \ C.vertexSet) := by
    ext v
    simp only [inter_vertexSet, union_vertexSet, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  have hdisj1 : Disjoint (C ∩ B).vertexSet ((D ∩ B).vertexSet \ C.vertexSet) :=
    Set.disjoint_left.2 fun _ hv1 hv2 ↦ hv2.2 hv1.1
  have hdisj2 : Disjoint (C ∩ D).vertexSet ((D ∩ B).vertexSet \ C.vertexSet) :=
    Set.disjoint_left.2 fun _ hv1 hv2 ↦ hv2.2 hv1.1
  have hc1 := Set.ncard_union_eq hdisj1 (C ∩ B).vertexSet_finite
    ((D ∩ B).vertexSet_finite.sdiff)
  have hc2 := Set.ncard_union_eq hdisj2 (C ∩ D).vertexSet_finite
    ((D ∩ B).vertexSet_finite.sdiff)
  rw [separationOrder, h1, hc1, separationOrder, h2, hc2]
  omega

/-- **Graph Minors X, (8.2)** (page 174):
"Every titanic separation is robust." -/
theorem theorem_8_2_proof {G A B : Hypergraph α β} (h : IsTitanic G A B) :
    IsRobust G A B := by
  refine ⟨h.1, fun {C D} hCD ↦ ?_⟩
  have hU : C ∪ D ∪ ⊥ = A := by
    rw [hCD.union_eq]
    ext <;> simp [union_inc]
  have hd1 : Disjoint C.edgeSet D.edgeSet := hCD.disjoint_edgeSet
  have hd2 : Disjoint D.edgeSet (⊥ : Hypergraph α β).edgeSet := by simp
  have hd3 : Disjoint C.edgeSet (⊥ : Hypergraph α β).edgeSet := by simp
  rcases h.2 hCD.left_le hCD.right_le (bot_le A) hU hd1 hd2 hd3 with h1 | h2 | h3
  · left
    have hZ : ((C ∪ D) ∩ (⊥ : Hypergraph α β)).vertexSet = ∅ := by simp
    have hAB : ((C ∪ D) ∩ B).vertexSet = (A ∩ B).vertexSet := by rw [hCD.union_eq]
    rw [hZ, hAB, Set.ncard_empty] at h1
    unfold separationOrder
    omega
  · left
    have hD1 : ((D ∪ ⊥) ∩ B).vertexSet = (D ∩ B).vertexSet := by simp
    have hD2 : ((D ∪ ⊥) ∩ C).vertexSet = (D ∩ C).vertexSet := by simp
    rw [hD1, hD2] at h2
    exact robust_step_of_ncard_le hCD.symm h2
  · right
    have hC1 : ((⊥ ∪ C) ∩ B).vertexSet = (C ∩ B).vertexSet := by simp
    have hC2 : ((⊥ ∪ C) ∩ D).vertexSet = (C ∩ D).vertexSet := by simp
    rw [hC1, hC2] at h3
    exact robust_step_of_ncard_le hCD h3

/-! ## Graph Minors X, (8.3) -/

private lemma isSeparation_extend_of_isSeparation {G C D P Q : Hypergraph α β}
    (hCD : G.IsSeparation C D) (hPQ : D.IsSeparation P Q) :
    G.IsSeparation P (Q ∪ C) := by
  have hP_G : P ≤ G := hPQ.left_le.trans hCD.right_le
  have hQC_G : Q ∪ C ≤ G := union_le (hPQ.right_le.trans hCD.right_le) hCD.left_le
  rw [isSeparation_iff_of_le hP_G hQC_G]
  refine ⟨?_, ?_, ?_⟩
  · rw [union_vertexSet, ← Set.union_assoc, hPQ.vertexSet_union, Set.union_comm,
      hCD.vertexSet_union]
  · rw [union_edgeSet, ← Set.union_assoc, hPQ.edgeSet_union, Set.union_comm,
      hCD.edgeSet_union]
  · ext e
    simp only [union_edgeSet, Set.mem_inter_iff, Set.mem_union, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨heP, heQ | heC⟩
    · exact hPQ.notMem_edgeSet_right heP heQ
    · exact hCD.notMem_edgeSet_right heC (hPQ.left_le.edgeSet_subset heP)

private lemma inter_union_eq_of_isSeparation {G' C' D B' : Hypergraph α β}
    (hC'D : G'.IsSeparation C' D) (hB' : B' ≤ G') :
    (B' ∩ D) ∪ C' = B' ∪ C' := by
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (union_le (inter_le hB' hC'D.right_le) hC'D.left_le)
    (union_le hB' hC'D.left_le) ?_ ?_
  · ext v
    have hV : v ∈ B'.vertexSet → v ∈ C'.vertexSet ∪ D.vertexSet :=
      fun hv ↦ hC'D.vertexSet_union.symm ▸ hB'.vertexSet_subset hv
    simp only [union_vertexSet, inter_vertexSet, Set.mem_union, Set.mem_inter_iff] at hV ⊢
    tauto
  · ext e
    have hE : e ∈ B'.edgeSet → e ∈ C'.edgeSet ∪ D.edgeSet :=
      fun he ↦ hC'D.edgeSet_union.symm ▸ hB'.edgeSet_subset he
    simp only [union_edgeSet, inter_edgeSet, Set.mem_union, Set.mem_inter_iff] at hE ⊢
    tauto

private lemma separationOrder_extend_eq {C C' D P Q : Hypergraph α β}
    (hV_inter : (C ∩ D).vertexSet = (C' ∩ D).vertexSet)
    (hPQ : D.IsSeparation P Q) :
    separationOrder P (Q ∪ C) = separationOrder P (Q ∪ C') := by
  have hP_D : P.vertexSet ⊆ D.vertexSet := hPQ.left_le.vertexSet_subset
  have hset : (P ∩ (Q ∪ C)).vertexSet = (P ∩ (Q ∪ C')).vertexSet := by
    have hCD_eq := Set.ext_iff.1 hV_inter
    ext v
    have hvD : v ∈ P.vertexSet → v ∈ D.vertexSet := fun hv ↦ hP_D hv
    have hCDv := hCD_eq v
    simp only [inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union] at hCDv ⊢
    tauto
  rw [separationOrder, hset, separationOrder]

private lemma theorem_8_3_axiom1 {G G' C C' D : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hCD : G.IsSeparation C D) (hC'D : IsTitanic G' C' D)
    (hV_inter : (C ∩ D).vertexSet = (C' ∩ D).vertexSet)
    (h𝒯 : IsTangle G θ 𝒯) :
    TangleAxiom1 G' θ (titanicTransferredTangle G' D 𝒯 θ) := by
  intro A' B' hsep' hord'
  have hrob : IsRobust G' C' D := theorem_8_2_proof hC'D
  have hstep : ∀ {X' Y' : Hypergraph α β}, G'.IsSeparation X' Y' →
      separationOrder X' Y' < θ →
      separationOrder (C' ∪ Y') (D ∩ X') ≤ separationOrder X' Y' →
      (X', Y') ∈ titanicTransferredTangle G' D 𝒯 θ ∨
        (Y', X') ∈ titanicTransferredTangle G' D 𝒯 θ := by
    intro X' Y' hs' ho' hle'
    have hPQ' : D.IsSeparation (X' ∩ D) (Y' ∩ D) := by
      simpa [inter_comm] using hs'.inter_left hC'D.1.right_le
    have hsepG : G.IsSeparation (X' ∩ D) ((Y' ∩ D) ∪ C) :=
      isSeparation_extend_of_isSeparation hCD hPQ'
    have hord_eq : separationOrder (X' ∩ D) ((Y' ∩ D) ∪ C) =
        separationOrder (C' ∪ Y') (D ∩ X') := by
      rw [separationOrder_extend_eq hV_inter hPQ',
        inter_union_eq_of_isSeparation hC'D.1 hs'.right_le,
        separationOrder_comm, union_comm Y' C', inter_comm X' D]
    have hordG : separationOrder (X' ∩ D) ((Y' ∩ D) ∪ C) < θ := by omega
    rcases h𝒯.axiom1 hsepG hordG with hm | hm
    · refine Or.inl ⟨hs', ho', ⟨(X' ∩ D, (Y' ∩ D) ∪ C), hm, ?_⟩⟩
      simp
    · refine Or.inr ⟨hs'.symm, by rwa [separationOrder_comm],
        ⟨((Y' ∩ D) ∪ C, X' ∩ D), hm, ?_⟩⟩
      ext e
      simp only [inter_edgeSet, union_edgeSet, Set.mem_inter_iff, Set.mem_union]
      exact ⟨fun ⟨he, heD⟩ ↦ ⟨(he.resolve_right (hCD.notMem_edgeSet_left heD)).1, heD⟩,
        fun ⟨heY, heD⟩ ↦ ⟨Or.inl ⟨heY, heD⟩, heD⟩⟩
  rcases theorem_8_1_proof hrob hsep'.symm with h1 | h2
  · rw [separationOrder_comm B' A'] at h1
    exact hstep hsep' hord' h1
  · exact (hstep hsep'.symm (by rwa [separationOrder_comm]) h2).symm

private lemma theorem_8_3_part_i {G G' C D : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hCD : G.IsSeparation C D) (hD_le : D ≤ G')
    (hθ : 2 ≤ θ) (h𝒯 : IsTangle G θ 𝒯) (hCD_mem : (C, D) ∈ 𝒯)
    {A₁' B₁' A₂' B₂' : Hypergraph α β}
    (h₁ : (A₁', B₁') ∈ titanicTransferredTangle G' D 𝒯 θ)
    (h₂ : (A₂', B₂') ∈ titanicTransferredTangle G' D 𝒯 θ) :
    ¬ B₁' ≤ A₂' := by
  intro hle
  rcases h₁.2.2 with ⟨⟨A₁, B₁⟩, hm₁, hE₁⟩
  rcases h₂.2.2 with ⟨⟨A₂, B₂⟩, hm₂, hE₂⟩
  dsimp only at hm₁ hE₁ hm₂ hE₂
  apply theorem_2_3_proof h𝒯 hθ hCD_mem hm₁ hm₂
  have hsep₁' := h₁.1
  have hEU' : A₁'.edgeSet ∪ A₂'.edgeSet = G'.edgeSet := by
    refine Set.Subset.antisymm
      (Set.union_subset hsep₁'.left_le.edgeSet_subset h₂.1.left_le.edgeSet_subset) ?_
    rw [← hsep₁'.edgeSet_union]
    exact Set.union_subset_union subset_rfl hle.edgeSet_subset
  ext e
  simp only [union_edgeSet, Set.mem_union]
  constructor
  · rintro ((heC | he₁) | he₂)
    · exact hCD.left_le.edgeSet_subset heC
    · exact (h𝒯.isSeparation hm₁).left_le.edgeSet_subset he₁
    · exact (h𝒯.isSeparation hm₂).left_le.edgeSet_subset he₂
  · intro heG
    have heCD : e ∈ C.edgeSet ∪ D.edgeSet := hCD.edgeSet_union.symm ▸ heG
    rcases heCD with heC | heD
    · exact Or.inl (Or.inl heC)
    · have heG' : e ∈ A₁'.edgeSet ∪ A₂'.edgeSet := hEU'.symm ▸ hD_le.edgeSet_subset heD
      rcases heG' with he₁' | he₂'
      · have heAD : e ∈ (A₁ ∩ D).edgeSet := by
          rw [hE₁]
          exact ⟨he₁', heD⟩
        exact Or.inl (Or.inr heAD.1)
      · have heAD : e ∈ (A₂ ∩ D).edgeSet := by
          rw [hE₂]
          exact ⟨he₂', heD⟩
        exact Or.inr heAD.1

private lemma theorem_8_3_part_ii_step {G G' C C' D : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hCD : G.IsSeparation C D) (hC'D : G'.IsSeparation C' D)
    (hV_inter : (C ∩ D).vertexSet = (C' ∩ D).vertexSet)
    (hθ : 2 ≤ θ) (h𝒯 : IsTangle G θ 𝒯) (hCD_mem : (C, D) ∈ 𝒯)
    {A₁' A₂' A₃' : Hypergraph α β}
    (hU' : A₁' ∪ A₂' ∪ A₃' = G')
    (h₁ : (A₁', A₂' ∪ A₃') ∈ titanicTransferredTangle G' D 𝒯 θ)
    (h₂ : (A₂', A₃' ∪ A₁') ∈ titanicTransferredTangle G' D 𝒯 θ)
    (h₃ : (A₃', A₁' ∪ A₂') ∈ titanicTransferredTangle G' D 𝒯 θ)
    (htit : (((A₂' ∩ C') ∪ (A₃' ∩ C')) ∩ D).vertexSet.ncard ≤
      (((A₂' ∩ C') ∪ (A₃' ∩ C')) ∩ (A₁' ∩ C')).vertexSet.ncard) :
    False := by
  let B₁' := A₂' ∪ A₃'
  have hsep₁' : G'.IsSeparation A₁' B₁' := h₁.1
  have hord₁' : separationOrder A₁' B₁' < θ := h₁.2.1
  rcases h₁.2.2 with ⟨⟨A₁, B₁⟩, hm₁, hE₁⟩
  rcases h₂.2.2 with ⟨⟨A₂, B₂⟩, hm₂, hE₂⟩
  rcases h₃.2.2 with ⟨⟨A₃, B₃⟩, hm₃, hE₃⟩
  dsimp only at hm₁ hE₁ hm₂ hE₂ hm₃ hE₃
  have hBC_D : (((A₂' ∩ C') ∪ (A₃' ∩ C')) ∩ D).vertexSet = ((B₁' ∩ C') ∩ D).vertexSet := by
    ext v
    simp only [B₁', inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union]
    tauto
  have hBC_A : (((A₂' ∩ C') ∪ (A₃' ∩ C')) ∩ (A₁' ∩ C')).vertexSet =
      ((B₁' ∩ C') ∩ A₁').vertexSet := by
    ext v
    simp only [B₁', inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union]
    tauto
  rw [hBC_D, hBC_A] at htit
  let R := (A₁'.vertexSet \ C'.vertexSet) ∩ (B₁' ∩ D).vertexSet
  have hR_fin : R.Finite := (A₁'.vertexSet_finite.sdiff).inter_of_left _
  have hset1 : ((A₁' ∪ C') ∩ (B₁' ∩ D)).vertexSet = ((B₁' ∩ C') ∩ D).vertexSet ∪ R := by
    ext v
    simp only [R, inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union,
      Set.mem_sdiff]
    constructor
    · rintro ⟨hvA | hvC, hvB, hvD⟩
      · by_cases hvC : v ∈ C'.vertexSet
        · exact Or.inl ⟨⟨hvB, hvC⟩, hvD⟩
        · exact Or.inr ⟨⟨hvA, hvC⟩, hvB, hvD⟩
      · exact Or.inl ⟨⟨hvB, hvC⟩, hvD⟩
    · tauto
  have hset2 : (A₁' ∩ B₁').vertexSet = ((B₁' ∩ C') ∩ A₁').vertexSet ∪ R := by
    ext v
    have hV_A₁ : v ∈ A₁'.vertexSet → v ∈ C'.vertexSet ∪ D.vertexSet :=
      fun hv ↦ hC'D.vertexSet_union.symm ▸ hsep₁'.left_le.vertexSet_subset hv
    simp only [R, inter_vertexSet, Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro ⟨hvA, hvB⟩
      by_cases hvC : v ∈ C'.vertexSet
      · exact Or.inl ⟨⟨hvB, hvC⟩, hvA⟩
      · have hvD : v ∈ D.vertexSet := (hV_A₁ hvA).resolve_left hvC
        exact Or.inr ⟨⟨hvA, hvC⟩, hvB, hvD⟩
    · tauto
  have hdisj1 : Disjoint ((B₁' ∩ C') ∩ D).vertexSet R :=
    Set.disjoint_left.2 fun _ hv1 hv2 ↦ hv2.1.2 hv1.1.2
  have hdisj2 : Disjoint ((B₁' ∩ C') ∩ A₁').vertexSet R :=
    Set.disjoint_left.2 fun _ hv1 hv2 ↦ hv2.1.2 hv1.1.2
  have hc1 := Set.ncard_union_eq hdisj1 ((B₁' ∩ C') ∩ D).vertexSet_finite hR_fin
  have hc2 := Set.ncard_union_eq hdisj2 ((B₁' ∩ C') ∩ A₁').vertexSet_finite hR_fin
  have hord_le : separationOrder (A₁' ∪ C') (B₁' ∩ D) ≤ separationOrder A₁' B₁' := by
    rw [separationOrder, hset1, hc1, separationOrder, hset2, hc2]
    omega
  have hPQ : D.IsSeparation (B₁' ∩ D) (A₁' ∩ D) := by
    simpa [inter_comm] using hsep₁'.symm.inter_left hC'D.right_le
  have hsepG : G.IsSeparation (B₁' ∩ D) ((A₁' ∩ D) ∪ C) :=
    isSeparation_extend_of_isSeparation hCD hPQ
  have hordG_eq : separationOrder (B₁' ∩ D) ((A₁' ∩ D) ∪ C) =
      separationOrder (A₁' ∪ C') (B₁' ∩ D) := by
    rw [separationOrder_extend_eq hV_inter hPQ,
      inter_union_eq_of_isSeparation hC'D hsep₁'.left_le,
      separationOrder_comm]
  have hordG : separationOrder (B₁' ∩ D) ((A₁' ∩ D) ∪ C) < θ := by omega
  rcases h𝒯.axiom1 hsepG hordG with hm | hm
  · apply theorem_2_3_proof h𝒯 hθ hm hCD_mem hm₁
    ext e
    simp only [union_edgeSet, inter_edgeSet, Set.mem_union, Set.mem_inter_iff]
    constructor
    · rintro ((⟨_, heD⟩ | heC) | heA₁)
      · exact hCD.right_le.edgeSet_subset heD
      · exact hCD.left_le.edgeSet_subset heC
      · exact (h𝒯.isSeparation hm₁).left_le.edgeSet_subset heA₁
    · intro heG
      have heCD : e ∈ C.edgeSet ∪ D.edgeSet := hCD.edgeSet_union.symm ▸ heG
      rcases heCD with heC | heD
      · exact Or.inl (Or.inr heC)
      · have heG' : e ∈ A₁'.edgeSet ∪ B₁'.edgeSet :=
          hsep₁'.edgeSet_union.symm ▸ hC'D.right_le.edgeSet_subset heD
        rcases heG' with heA₁' | heB₁'
        · have heAD : e ∈ (A₁ ∩ D).edgeSet := by
            rw [hE₁]
            exact ⟨heA₁', heD⟩
          exact Or.inr heAD.1
        · exact Or.inl (Or.inl ⟨heB₁', heD⟩)
  · apply theorem_2_3_proof h𝒯 hθ hm hm₂ hm₃
    ext e
    simp only [union_edgeSet, inter_edgeSet, Set.mem_union, Set.mem_inter_iff]
    constructor
    · rintro (((⟨_, heD⟩ | heC) | heA₂) | heA₃)
      · exact hCD.right_le.edgeSet_subset heD
      · exact hCD.left_le.edgeSet_subset heC
      · exact (h𝒯.isSeparation hm₂).left_le.edgeSet_subset heA₂
      · exact (h𝒯.isSeparation hm₃).left_le.edgeSet_subset heA₃
    · intro heG
      have heCD : e ∈ C.edgeSet ∪ D.edgeSet := hCD.edgeSet_union.symm ▸ heG
      rcases heCD with heC | heD
      · exact Or.inl (Or.inl (Or.inr heC))
      · have heU' : e ∈ (A₁' ∪ A₂' ∪ A₃').edgeSet :=
          (congrArg Hypergraph.edgeSet hU').symm ▸ hC'D.right_le.edgeSet_subset heD
        rcases heU' with (he₁' | he₂') | he₃'
        · exact Or.inl (Or.inl (Or.inl ⟨he₁', heD⟩))
        · have heAD : e ∈ (A₂ ∩ D).edgeSet := by
            rw [hE₂]
            exact ⟨he₂', heD⟩
          exact Or.inl (Or.inr heAD.1)
        · have heAD : e ∈ (A₃ ∩ D).edgeSet := by
            rw [hE₃]
            exact ⟨he₃', heD⟩
          exact Or.inr heAD.1

/-- **Graph Minors X, (8.3)** (page 175):
"Let* $(C, D)$ *be a separation of a hypergraph* $G$, *and let* $(C', D)$ *be a titanic
separation of a hypergraph* $G'$, *with* $V(C \cap D) = V(C' \cap D)$. *Let* $\mathscr{T}$
*be a tangle in* $G$ *of order* $\theta \ge 2$ *with* $(C, D) \in \mathscr{T}$. *Let*
$\mathscr{T}'$ *be the set of all separations* $(A', B')$ *of* $G'$ *of order* $<\theta$
*such that there exists* $(A, B) \in \mathscr{T}$ *with* $E(A \cap D) = E(A' \cap D)$.
*Then* $\mathscr{T}'$ *is a tangle in* $G'$ *of order* $\theta$." -/
theorem theorem_8_3_proof
    {G G' C C' D : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hCD : G.IsSeparation C D) (hC'D : IsTitanic G' C' D)
    (hV_inter : (C ∩ D).vertexSet = (C' ∩ D).vertexSet)
    (hθ : 2 ≤ θ) (h𝒯 : IsTangle G θ 𝒯) (hCD_mem : (C, D) ∈ 𝒯) :
    IsTangle G' θ (titanicTransferredTangle G' D 𝒯 θ) := by
  let 𝒯' := titanicTransferredTangle G' D 𝒯 θ
  have h1_le : 1 ≤ θ := by omega
  have hsep' : ∀ ⦃A' B' : Hypergraph α β⦄, (A', B') ∈ 𝒯' → G'.IsSeparation A' B' :=
    fun _ _ h ↦ h.1
  have hord' : ∀ ⦃A' B' : Hypergraph α β⦄, (A', B') ∈ 𝒯' → separationOrder A' B' < θ :=
    fun _ _ h ↦ h.2.1
  have hax1 : TangleAxiom1 G' θ 𝒯' :=
    theorem_8_3_axiom1 hCD hC'D hV_inter h𝒯
  have hax2 : TangleAxiom2 G' 𝒯' := by
    refine theorem_4_5_statement.{u, v} G' θ 𝒯' hθ (fun _ _ h ↦ ⟨hsep' h, hord' h⟩) hax1 ?_ ?_
    · intro A₁' B₁' A₂' B₂' h₁ h₂
      exact theorem_8_3_part_i hCD hC'D.1.right_le hθ h𝒯 hCD_mem h₁ h₂
    · rintro ⟨A₁', A₂', A₃', hle₁, hle₂, hle₃, hd₁₂, hd₂₃, hd₁₃, hU', h₁, h₂, h₃⟩
      let F₁ := A₁' ∩ C'
      let F₂ := A₂' ∩ C'
      let F₃ := A₃' ∩ C'
      have hF₁ : F₁ ≤ C' := inter_le_right hle₁ hC'D.1.left_le
      have hF₂ : F₂ ≤ C' := inter_le_right hle₂ hC'D.1.left_le
      have hF₃ : F₃ ≤ C' := inter_le_right hle₃ hC'D.1.left_le
      have hFU : F₁ ∪ F₂ ∪ F₃ = C' := by
        refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq
          (union_le (union_le hF₁ hF₂) hF₃) le_rfl ?_ ?_
        · change (A₁'.vertexSet ∩ C'.vertexSet) ∪ (A₂'.vertexSet ∩ C'.vertexSet) ∪
            (A₃'.vertexSet ∩ C'.vertexSet) = C'.vertexSet
          have hVU : (A₁' ∪ A₂' ∪ A₃').vertexSet = G'.vertexSet :=
            congrArg Hypergraph.vertexSet hU'
          calc
            (A₁'.vertexSet ∩ C'.vertexSet) ∪ (A₂'.vertexSet ∩ C'.vertexSet) ∪
                (A₃'.vertexSet ∩ C'.vertexSet)
              = (A₁' ∪ A₂' ∪ A₃').vertexSet ∩ C'.vertexSet := by
                simp [Set.union_inter_distrib_right]
            _ = G'.vertexSet ∩ C'.vertexSet := by rw [hVU]
            _ = C'.vertexSet := Set.inter_eq_right.2 hC'D.1.left_le.vertexSet_subset
        · change (A₁'.edgeSet ∩ C'.edgeSet) ∪ (A₂'.edgeSet ∩ C'.edgeSet) ∪
            (A₃'.edgeSet ∩ C'.edgeSet) = C'.edgeSet
          have hEU : (A₁' ∪ A₂' ∪ A₃').edgeSet = G'.edgeSet :=
            congrArg Hypergraph.edgeSet hU'
          calc
            (A₁'.edgeSet ∩ C'.edgeSet) ∪ (A₂'.edgeSet ∩ C'.edgeSet) ∪
                (A₃'.edgeSet ∩ C'.edgeSet)
              = (A₁' ∪ A₂' ∪ A₃').edgeSet ∩ C'.edgeSet := by
                simp [Set.union_inter_distrib_right]
            _ = G'.edgeSet ∩ C'.edgeSet := by rw [hEU]
            _ = C'.edgeSet := Set.inter_eq_right.2 hC'D.1.left_le.edgeSet_subset
      have hdF₁₂ : Disjoint F₁.edgeSet F₂.edgeSet :=
        hd₁₂.mono Set.inter_subset_left Set.inter_subset_left
      have hdF₂₃ : Disjoint F₂.edgeSet F₃.edgeSet :=
        hd₂₃.mono Set.inter_subset_left Set.inter_subset_left
      have hdF₁₃ : Disjoint F₁.edgeSet F₃.edgeSet :=
        hd₁₃.mono Set.inter_subset_left Set.inter_subset_left
      rcases hC'D.2 hF₁ hF₂ hF₃ hFU hdF₁₂ hdF₂₃ hdF₁₃ with ht1 | ht2 | ht3
      · have hU₃ : A₃' ∪ A₁' ∪ A₂' = G' := by
          rw [union_assoc, union_comm A₃', hU']
        exact theorem_8_3_part_ii_step hCD hC'D.1 hV_inter hθ h𝒯 hCD_mem hU₃ h₃ h₁ h₂ ht1
      · exact theorem_8_3_part_ii_step hCD hC'D.1 hV_inter hθ h𝒯 hCD_mem hU' h₁ h₂ h₃ ht2
      · have hU₂ : A₂' ∪ A₃' ∪ A₁' = G' := by
          rw [union_comm (A₂' ∪ A₃'), ← union_assoc, hU']
        exact theorem_8_3_part_ii_step hCD hC'D.1 hV_inter hθ h𝒯 hCD_mem hU₂ h₂ h₃ h₁ ht3
  rw [theorem_2_7_proof h1_le hsep' hord' hax1 hax2]
  intro e heG' hsize'
  have hsep_e' := isSeparation_edgeHypergraph_deleteEdges heG'
  have hord_e' : separationOrder (edgeHypergraph G' e) (G'.deleteEdges {e}) < θ := by
    rwa [separationOrder_edgeHypergraph_deleteEdges]
  have heC'D : e ∈ C'.edgeSet ∪ D.edgeSet := hC'D.1.edgeSet_union.symm ▸ heG'
  rcases heC'D with heC' | heD
  · refine ⟨hsep_e', hord_e', ⟨(C, D), hCD_mem, ?_⟩⟩
    have he_notD : e ∉ D.edgeSet := hC'D.1.notMem_edgeSet_right heC'
    have h1 : (C ∩ D).edgeSet = ∅ := hCD.edgeSet_inter_eq
    have h2 : (edgeHypergraph G' e ∩ D).edgeSet = ∅ := by
      ext f
      simp only [inter_edgeSet, edgeHypergraph, Set.mem_inter_iff, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, hfD⟩
      exact he_notD hfD
    rw [h1, h2]
  · have heG : e ∈ G.edgeSet := hCD.right_le.edgeSet_subset heD
    have hends_eq : G.ends e = G'.ends e :=
      (hCD.right_le.ends_eq e heD).trans (hC'D.1.right_le.ends_eq e heD).symm
    have hsizeG : edgeSize G e < θ := by
      unfold edgeSize at hsize' ⊢
      rwa [hends_eq]
    have hKe_mem : (edgeHypergraph G e, G.deleteEdges {e}) ∈ 𝒯 :=
      (theorem_2_7_proof h1_le (fun _ _ h ↦ h𝒯.isSeparation h)
        (fun _ _ h ↦ h𝒯.order_lt h) h𝒯.axiom1 h𝒯.axiom2).1 h𝒯 e heG hsizeG
    refine ⟨hsep_e', hord_e', ⟨(edgeHypergraph G e, G.deleteEdges {e}), hKe_mem, ?_⟩⟩
    simp [edgeHypergraph]

/-! ## Graph Minors X, (8.4) -/

private lemma isTitanic_of_ncard_le_one {G' C' D : Hypergraph α β}
    (hsep : G'.IsSeparation C' D) (hcard : C'.vertexSet.ncard ≤ 1) :
    IsTitanic G' C' D := by
  refine ⟨hsep, fun {X Y Z} hX hY hZ hU _ _ _ ↦ ?_⟩
  rcases Set.eq_empty_or_nonempty C'.vertexSet with hemp | ⟨v, hvC'⟩
  · left
    have hXY : ((X ∪ Y) ∩ D).vertexSet = ∅ := by
      refine Set.eq_empty_of_subset_empty ?_
      rw [← hemp]
      exact Set.inter_subset_left.trans (union_le hX hY).vertexSet_subset
    rw [hXY, Set.ncard_empty]
    exact Nat.zero_le _
  · have hV_eq : C'.vertexSet = {v} := by
      have hsub : {v} ⊆ C'.vertexSet := Set.singleton_subset_iff.2 hvC'
      exact (Set.eq_of_subset_of_ncard_le hsub (by simpa using hcard) C'.vertexSet_finite).symm
    have hvU : v ∈ X.vertexSet ∪ Y.vertexSet ∪ Z.vertexSet := by
      have hVU : (X ∪ Y ∪ Z).vertexSet = C'.vertexSet := congrArg Hypergraph.vertexSet hU
      rw [← union_vertexSet, ← union_vertexSet, hVU, hV_eq]
      exact Set.mem_singleton v
    by_cases hvX : v ∈ X.vertexSet
    · by_cases hvY : v ∈ Y.vertexSet
      · right; left
        have hsub : ((Y ∪ Z) ∩ D).vertexSet ⊆ ((Y ∪ Z) ∩ X).vertexSet := by
          intro x hx
          have hxC' : x ∈ C'.vertexSet :=
            (union_le hY hZ).vertexSet_subset hx.1
          rcases Set.mem_singleton_iff.1 (hV_eq ▸ hxC') with rfl
          exact ⟨Or.inl hvY, hvX⟩
        exact Set.ncard_le_ncard hsub ((Y ∪ Z) ∩ X).vertexSet_finite
      · by_cases hvZ : v ∈ Z.vertexSet
        · left
          have hsub : ((X ∪ Y) ∩ D).vertexSet ⊆ ((X ∪ Y) ∩ Z).vertexSet := by
            intro x hx
            have hxC' : x ∈ C'.vertexSet :=
              (union_le hX hY).vertexSet_subset hx.1
            rcases Set.mem_singleton_iff.1 (hV_eq ▸ hxC') with rfl
            exact ⟨Or.inl hvX, hvZ⟩
          exact Set.ncard_le_ncard hsub ((X ∪ Y) ∩ Z).vertexSet_finite
        · right; left
          have hempYZ : ((Y ∪ Z) ∩ D).vertexSet = ∅ := by
            ext x
            simp only [inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union,
              Set.mem_empty_iff_false, iff_false]
            rintro ⟨hxY | hxZ, _⟩
            · have hx := Set.mem_singleton_iff.1 (hV_eq ▸ hY.vertexSet_subset hxY)
              exact hvY (hx ▸ hxY)
            · have hx := Set.mem_singleton_iff.1 (hV_eq ▸ hZ.vertexSet_subset hxZ)
              exact hvZ (hx ▸ hxZ)
          rw [hempYZ, Set.ncard_empty]
          exact Nat.zero_le _
    · by_cases hvY : v ∈ Y.vertexSet
      · by_cases hvZ : v ∈ Z.vertexSet
        · left
          have hsub : ((X ∪ Y) ∩ D).vertexSet ⊆ ((X ∪ Y) ∩ Z).vertexSet := by
            intro x hx
            have hxC' : x ∈ C'.vertexSet :=
              (union_le hX hY).vertexSet_subset hx.1
            rcases Set.mem_singleton_iff.1 (hV_eq ▸ hxC') with rfl
            exact ⟨Or.inr hvY, hvZ⟩
          exact Set.ncard_le_ncard hsub ((X ∪ Y) ∩ Z).vertexSet_finite
        · right; right
          have hempZX : ((Z ∪ X) ∩ D).vertexSet = ∅ := by
            ext x
            simp only [inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union,
              Set.mem_empty_iff_false, iff_false]
            rintro ⟨hxZ | hxX, _⟩
            · have hx := Set.mem_singleton_iff.1 (hV_eq ▸ hZ.vertexSet_subset hxZ)
              exact hvZ (hx ▸ hxZ)
            · have hx := Set.mem_singleton_iff.1 (hV_eq ▸ hX.vertexSet_subset hxX)
              exact hvX (hx ▸ hxX)
          rw [hempZX, Set.ncard_empty]
          exact Nat.zero_le _
      · left
        have hempXY : ((X ∪ Y) ∩ D).vertexSet = ∅ := by
          ext x
          simp only [inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union,
            Set.mem_empty_iff_false, iff_false]
          rintro ⟨hxX | hxY, _⟩
          · have hx := Set.mem_singleton_iff.1 (hV_eq ▸ hX.vertexSet_subset hxX)
            exact hvX (hx ▸ hxX)
          · have hx := Set.mem_singleton_iff.1 (hV_eq ▸ hY.vertexSet_subset hxY)
            exact hvY (hx ▸ hxY)
        rw [hempXY, Set.ncard_empty]
        exact Nat.zero_le _

/-- **Graph Minors X, (8.4)** (page 176):
"Let* $\mathscr{T}$ *be a tangle of order* $\theta \ge 2$ *in a hypergraph* $G$, *and let* $e
\in E(G)$ *with at most one end. Let* $\mathscr{T}'$ *be the set of all separations* $(A',
B')$ *of* $G \setminus e$ *of order* $<\theta$ *such that there exists* $(A, B) \in
\mathscr{T}$ *with* $E(A \cap (G \setminus e)) = E(A')$. *Then* $\mathscr{T}'$ *is a tangle
in* $G \setminus e$ *of order* $\theta$." -/
theorem theorem_8_4_proof
    {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 2 ≤ θ)
    {e : β} (he : e ∈ G.edgeSet) (hsize : (G.ends e).ncard ≤ 1) :
    IsTangle (G.deleteEdges {e}) θ (deleteEdgeTangle G e 𝒯 θ) := by
  let C := edgeHypergraph G e
  let D := G.deleteEdges {e}
  let C' := C.deleteEdges {e}
  have hCD : G.IsSeparation C D := isSeparation_edgeHypergraph_deleteEdges he
  have hordCD : separationOrder C D < θ := by
    rw [separationOrder_edgeHypergraph_deleteEdges]
    unfold edgeSize
    omega
  have hCD_mem : (C, D) ∈ 𝒯 :=
    (h𝒯.axiom1 hCD hordCD).resolve_right fun hDC ↦ h𝒯.axiom3 hDC rfl
  have hC'_le_D : C' ≤ D :=
    ⟨fun _ hv ↦ G.vertex_mem_of_inc hv,
     by simp [C', C, edgeHypergraph, deleteEdges],
     fun f hf ↦ by simp [C', C, edgeHypergraph, deleteEdges] at hf⟩
  have hsepC'D : D.IsSeparation C' D := by
    rw [isSeparation_iff_of_le hC'_le_D le_rfl]
    refine ⟨Set.union_eq_right.2 hC'_le_D.vertexSet_subset, ?_, ?_⟩
    · simp [C', C, edgeHypergraph, deleteEdges]
    · simp [C', C, edgeHypergraph, deleteEdges]
  have htit : IsTitanic D C' D := isTitanic_of_ncard_le_one hsepC'D hsize
  have hV_inter : (C ∩ D).vertexSet = (C' ∩ D).vertexSet := rfl
  have h83 := theorem_8_3_proof hCD htit hV_inter hθ h𝒯 hCD_mem
  have h_eq : titanicTransferredTangle D D 𝒯 θ = deleteEdgeTangle G e 𝒯 θ := by
    ext ⟨A', B'⟩
    simp only [titanicTransferredTangle, deleteEdgeTangle, Set.mem_ofPred_eq, D]
    refine and_congr_right fun hsep' ↦ and_congr_right fun _ ↦ ?_
    refine exists_congr fun p ↦ and_congr_right fun _ ↦ ?_
    have hA'_D : (A' ∩ G.deleteEdges {e}).edgeSet = A'.edgeSet :=
      Set.inter_eq_left.2 hsep'.left_le.edgeSet_subset
    rw [hA'_D]
  rwa [h_eq] at h83

/-! ## Graph Minors X, (8.5) -/

private lemma subsingleton_ends_sdiff_of_isGraph {G : Hypergraph α β}
    (hG : G.IsGraph) {W : Set α} {e : β} (he : e ∈ G.edgeSet)
    {w : α} (hwW : w ∈ W) (hw_inc : G.Inc e w) :
    (G.ends e \ W).Subsingleton := by
  intro u hu v hv
  by_contra hne
  have hcard_le : (G.ends e).ncard ≤ 2 := (hG e he).2
  have hsub : {w, u, v} ⊆ G.ends e := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hw_inc
    · exact hu.1
    · exact hv.1
  have hwu : w ≠ u := fun h ↦ hu.2 (h ▸ hwW)
  have hwv : w ≠ v := fun h ↦ hv.2 (h ▸ hwW)
  have h3 : ({w, u, v} : Set α).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_singleton]
    · simpa using hne
    · simp [hwu, hwv]
  have hle := Set.ncard_le_ncard hsub (G.vertexSet_finite.subset fun _ h ↦ G.vertex_mem_of_inc h)
  omega

/-- Canonical lift of a subhypergraph `A'` of `G.deleteVertices W` to a subhypergraph `A_pos` of `G`
by adding `W` to the vertex set and adding all edges incident with `W` whose ends lie in
`V(A') ∪ W`. -/
private def liftDeleteVerticesLeft (G : Hypergraph α β) (W : Set α) (hW : W ⊆ G.vertexSet)
    (A' : Hypergraph α β) (hA' : A' ≤ G.deleteVertices W) : Hypergraph α β where
  vertexSet := A'.vertexSet ∪ W
  edgeSet := A'.edgeSet ∪
    {e ∈ G.edgeSet \ (G.deleteVertices W).edgeSet | G.ends e ⊆ A'.vertexSet ∪ W}
  Inc e v :=
    (e ∈ A'.edgeSet ∪
      {e ∈ G.edgeSet \ (G.deleteVertices W).edgeSet | G.ends e ⊆ A'.vertexSet ∪ W}) ∧
    G.Inc e v
  vertex_mem_of_inc e v h := by
    rcases h.1 with heA' | ⟨_, hsub⟩
    · have hinc_del : (G.deleteVertices W).Inc e v :=
        ⟨h.2, (hA'.edgeSet_subset heA').2⟩
      have hincA' : A'.Inc e v := (inc_iff_of_le hA' heA').2 hinc_del
      exact Or.inl (A'.vertex_mem_of_inc hincA')
    · exact hsub h.2
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := A'.vertexSet_finite.union (G.vertexSet_finite.subset hW)
  edgeSet_finite :=
    A'.edgeSet_finite.union (G.edgeSet_finite.subset fun _ h ↦ h.1.1)

/-- Companion lift of `B'` of `G.deleteVertices W` to a subhypergraph `B_neg` of `G` putting the
remaining `W`-incident edges into `B_neg`. -/
private def liftDeleteVerticesRight (G : Hypergraph α β) (W : Set α) (hW : W ⊆ G.vertexSet)
    (hG : G.IsGraph)
    {A' B' : Hypergraph α β} (hsep' : (G.deleteVertices W).IsSeparation A' B') :
    Hypergraph α β where
  vertexSet := B'.vertexSet ∪ W
  edgeSet := B'.edgeSet ∪
    {e ∈ G.edgeSet \ (G.deleteVertices W).edgeSet | ¬ G.ends e ⊆ A'.vertexSet ∪ W}
  Inc e v :=
    (e ∈ B'.edgeSet ∪
      {e ∈ G.edgeSet \ (G.deleteVertices W).edgeSet | ¬ G.ends e ⊆ A'.vertexSet ∪ W}) ∧
    G.Inc e v
  vertex_mem_of_inc e v h := by
    rcases h.1 with heB' | ⟨⟨heG, he_not_del⟩, hnot_sub⟩
    · have hinc_del : (G.deleteVertices W).Inc e v :=
        ⟨h.2, (hsep'.right_le.edgeSet_subset heB').2⟩
      have hincB' : B'.Inc e v := (inc_iff_of_le hsep'.right_le heB').2 hinc_del
      exact Or.inl (B'.vertex_mem_of_inc hincB')
    · by_cases hvW : v ∈ W
      · exact Or.inr hvW
      · have hw_ex : ∃ w ∈ W, G.Inc e w := by
          by_contra! hno
          exact he_not_del ⟨heG, hno⟩
        obtain ⟨w, hwW, hw_inc⟩ := hw_ex
        obtain ⟨u, hu_inc, hu_not⟩ := Set.not_subset.1 hnot_sub
        have huW : u ∉ W := fun h ↦ hu_not (Or.inr h)
        have hu_eq_v : u = v :=
          subsingleton_ends_sdiff_of_isGraph hG heG hwW hw_inc ⟨hu_inc, huW⟩ ⟨h.2, hvW⟩
        have hv_del : v ∈ (G.deleteVertices W).vertexSet := ⟨G.vertex_mem_of_inc h.2, hvW⟩
        have hvAB : v ∈ A'.vertexSet ∪ B'.vertexSet := hsep'.vertexSet_union.symm ▸ hv_del
        exact Or.inl (hvAB.resolve_left fun hvA' ↦ hu_not (Or.inl (hu_eq_v.symm ▸ hvA')))
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := B'.vertexSet_finite.union (G.vertexSet_finite.subset hW)
  edgeSet_finite :=
    B'.edgeSet_finite.union (G.edgeSet_finite.subset fun _ h ↦ h.1.1)

private lemma deleteVertices_mono {G A : Hypergraph α β} (hA : A ≤ G) (W : Set α) :
    A.deleteVertices W ≤ G.deleteVertices W where
  vertexSet_subset := Set.sdiff_subset_sdiff hA.vertexSet_subset subset_rfl
  edgeSet_subset e he :=
    ⟨hA.edgeSet_subset he.1, fun v hvW hincG ↦
      he.2 v hvW ((inc_iff_of_le hA he.1).2 hincG)⟩
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, Set.mem_ofPred_eq, deleteVertices]
    simp_rw [inc_iff_of_le hA he.1]

private lemma liftDeleteVerticesLeft_le {G : Hypergraph α β} {W : Set α}
    (hW : W ⊆ G.vertexSet) {A' : Hypergraph α β} (hA' : A' ≤ G.deleteVertices W) :
    liftDeleteVerticesLeft G W hW A' hA' ≤ G where
  vertexSet_subset :=
    Set.union_subset (hA'.vertexSet_subset.trans Set.sdiff_subset) hW
  edgeSet_subset :=
    Set.union_subset
      (hA'.edgeSet_subset.trans (deleteVertices_le G W).edgeSet_subset)
      (fun _ h ↦ h.1.1)
  ends_eq _ he := Set.ext fun _ ↦ ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩

private lemma liftDeleteVerticesRight_le {G : Hypergraph α β} {W : Set α}
    (hW : W ⊆ G.vertexSet) (hG : G.IsGraph)
    {A' B' : Hypergraph α β} (hsep' : (G.deleteVertices W).IsSeparation A' B') :
    liftDeleteVerticesRight G W hW hG hsep' ≤ G where
  vertexSet_subset :=
    Set.union_subset (hsep'.right_le.vertexSet_subset.trans Set.sdiff_subset) hW
  edgeSet_subset :=
    Set.union_subset
      (hsep'.right_le.edgeSet_subset.trans (deleteVertices_le G W).edgeSet_subset)
      (fun _ h ↦ h.1.1)
  ends_eq _ he := Set.ext fun _ ↦ ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩

private lemma liftDeleteVertices_isSeparation {G : Hypergraph α β} {W : Set α}
    (hW : W ⊆ G.vertexSet) (hG : G.IsGraph)
    {A' B' : Hypergraph α β} (hsep' : (G.deleteVertices W).IsSeparation A' B') :
    G.IsSeparation
      (liftDeleteVerticesLeft G W hW A' hsep'.left_le)
      (liftDeleteVerticesRight G W hW hG hsep') := by
  let A_pos := liftDeleteVerticesLeft G W hW A' hsep'.left_le
  let B_neg := liftDeleteVerticesRight G W hW hG hsep'
  have hA_le : A_pos ≤ G := liftDeleteVerticesLeft_le hW hsep'.left_le
  have hB_le : B_neg ≤ G := liftDeleteVerticesRight_le hW hG hsep'
  rw [isSeparation_iff_of_le hA_le hB_le]
  refine ⟨?_, ?_, ?_⟩
  · change (A'.vertexSet ∪ W) ∪ (B'.vertexSet ∪ W) = G.vertexSet
    have h1 : (A'.vertexSet ∪ W) ∪ (B'.vertexSet ∪ W) = (A'.vertexSet ∪ B'.vertexSet) ∪ W := by
      ext v; simp only [Set.mem_union]; tauto
    rw [h1, hsep'.vertexSet_union]
    exact Set.sdiff_union_of_subset hW
  · ext e
    simp only [A_pos, B_neg, liftDeleteVerticesLeft, liftDeleteVerticesRight, Set.mem_union,
      Set.mem_ofPred_eq, Set.mem_sdiff]
    constructor
    · rintro ((heA' | ⟨⟨heG, _⟩, _⟩) | (heB' | ⟨⟨heG, _⟩, _⟩))
      · exact (hsep'.left_le.edgeSet_subset heA').1
      · exact heG
      · exact (hsep'.right_le.edgeSet_subset heB').1
      · exact heG
    · intro heG
      by_cases he_del : e ∈ (G.deleteVertices W).edgeSet
      · rcases (hsep'.edgeSet_union.symm ▸ he_del) with heA' | heB'
        · exact Or.inl (Or.inl heA')
        · exact Or.inr (Or.inl heB')
      · by_cases hsub : G.ends e ⊆ A'.vertexSet ∪ W
        · exact Or.inl (Or.inr ⟨⟨heG, he_del⟩, hsub⟩)
        · exact Or.inr (Or.inr ⟨⟨heG, he_del⟩, hsub⟩)
  · ext e
    simp only [A_pos, B_neg, liftDeleteVerticesLeft, liftDeleteVerticesRight, Set.mem_inter_iff,
      Set.mem_union, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨heA' | ⟨⟨_, he_not⟩, hsub⟩, heB' | ⟨⟨_, he_not'⟩, hnot_sub⟩⟩
    · exact hsep'.notMem_edgeSet_right heA' heB'
    · exact he_not' (hsep'.left_le.edgeSet_subset heA')
    · exact he_not (hsep'.right_le.edgeSet_subset heB')
    · exact hnot_sub hsub

private lemma deleteVertices_liftDeleteVerticesLeft {G : Hypergraph α β} {W : Set α}
    (hW : W ⊆ G.vertexSet) {A' : Hypergraph α β} (hA' : A' ≤ G.deleteVertices W) :
    (liftDeleteVerticesLeft G W hW A' hA').deleteVertices W = A' := by
  let A_pos := liftDeleteVerticesLeft G W hW A' hA'
  have hAdel_le : A_pos.deleteVertices W ≤ G.deleteVertices W :=
    deleteVertices_mono (liftDeleteVerticesLeft_le hW hA') W
  have hdisj : Disjoint A'.vertexSet W :=
    Set.disjoint_left.2 fun _ hvA' hvW ↦ (hA'.vertexSet_subset hvA').2 hvW
  have hV : (A'.vertexSet ∪ W) \ W = A'.vertexSet :=
    Set.union_sdiff_cancel_right (Set.disjoint_iff.1 hdisj)
  have hE : (A_pos.deleteVertices W).edgeSet = A'.edgeSet := by
    ext e
    simp only [A_pos, deleteVertices, liftDeleteVerticesLeft, Set.mem_ofPred_eq, Set.mem_union,
      Set.mem_sdiff]
    constructor
    · rintro ⟨heA' | ⟨⟨heG, he_not_del⟩, _⟩, hnoW⟩
      · exact heA'
      · exfalso
        exact he_not_del ⟨heG, fun v hvW hincG ↦
          hnoW v hvW ⟨Or.inr ⟨⟨heG, he_not_del⟩, ‹_›⟩, hincG⟩⟩
    · intro heA'
      exact ⟨Or.inl heA', fun v hvW hinc ↦ (hA'.edgeSet_subset heA').2 v hvW hinc.2⟩
  exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq hAdel_le hA' hV hE

private lemma deleteVertices_liftDeleteVerticesRight {G : Hypergraph α β} {W : Set α}
    (hW : W ⊆ G.vertexSet) (hG : G.IsGraph)
    {A' B' : Hypergraph α β} (hsep' : (G.deleteVertices W).IsSeparation A' B') :
    (liftDeleteVerticesRight G W hW hG hsep').deleteVertices W = B' := by
  let B_neg := liftDeleteVerticesRight G W hW hG hsep'
  have hBdel_le : B_neg.deleteVertices W ≤ G.deleteVertices W :=
    deleteVertices_mono (liftDeleteVerticesRight_le hW hG hsep') W
  have hdisj : Disjoint B'.vertexSet W :=
    Set.disjoint_left.2 fun _ hvB' hvW ↦ (hsep'.right_le.vertexSet_subset hvB').2 hvW
  have hV : (B'.vertexSet ∪ W) \ W = B'.vertexSet :=
    Set.union_sdiff_cancel_right (Set.disjoint_iff.1 hdisj)
  have hE : (B_neg.deleteVertices W).edgeSet = B'.edgeSet := by
    ext e
    simp only [B_neg, deleteVertices, liftDeleteVerticesRight, Set.mem_ofPred_eq, Set.mem_union,
      Set.mem_sdiff]
    constructor
    · rintro ⟨heB' | ⟨⟨heG, he_not_del⟩, _⟩, hnoW⟩
      · exact heB'
      · exfalso
        exact he_not_del ⟨heG, fun v hvW hincG ↦
          hnoW v hvW ⟨Or.inr ⟨⟨heG, he_not_del⟩, ‹_›⟩, hincG⟩⟩
    · intro heB'
      exact ⟨Or.inl heB', fun v hvW hinc ↦ (hsep'.right_le.edgeSet_subset heB').2 v hvW hinc.2⟩
  exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq hBdel_le hsep'.right_le hV hE

private lemma liftDeleteVertices_separationOrder {G : Hypergraph α β} {W : Set α}
    (hW : W ⊆ G.vertexSet) (hG : G.IsGraph)
    {A' B' : Hypergraph α β} (hsep' : (G.deleteVertices W).IsSeparation A' B') :
    separationOrder
      (liftDeleteVerticesLeft G W hW A' hsep'.left_le)
      (liftDeleteVerticesRight G W hW hG hsep') =
      separationOrder A' B' + W.ncard := by
  have h_inter :
      ((liftDeleteVerticesLeft G W hW A' hsep'.left_le) ∩
        (liftDeleteVerticesRight G W hW hG hsep')).vertexSet =
      (A' ∩ B').vertexSet ∪ W := by
    ext v
    simp only [inter_vertexSet, liftDeleteVerticesLeft, liftDeleteVerticesRight,
      Set.mem_inter_iff, Set.mem_union]
    tauto
  have hdisj : Disjoint (A' ∩ B').vertexSet W :=
    Set.disjoint_left.2 fun _ hv hvW ↦ (hsep'.left_le.vertexSet_subset hv.1).2 hvW
  rw [separationOrder, h_inter,
    Set.ncard_union_eq hdisj (A' ∩ B').vertexSet_finite (G.vertexSet_finite.subset hW),
    separationOrder]

/-- **Graph Minors X, (8.5)** (page 177):
"Let $\mathscr{T}$ be a tangle in a graph $G$ of order $\theta \ge 1$. Let $W \subseteq V(G)$
with $|W| < \theta$. Let $\mathscr{T}'$ be the set of all separations $(A', B')$ of $G
\setminus W$ of order $< \theta - |W|$ such that there exists $(A, B) \in \mathscr{T}$ with
$W \subseteq V(A \cap B)$ and $A \setminus W = A'$, $B \setminus W = B'$. Then
$\mathscr{T}'$ is a tangle in $G \setminus W$ of order $\theta - |W|$." -/
theorem theorem_8_5_proof {G : Hypergraph α β} (hG : G.IsGraph) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {W : Set α} (hW : W ⊆ G.vertexSet) (hW_lt : W.ncard < θ) :
    IsTangle (G.deleteVertices W) (θ - W.ncard) (deleteVerticesTangle G W 𝒯 θ) where
  one_le := by omega
  isSeparation _ _ h := h.1
  order_lt _ _ h := h.2.1
  axiom1 A' B' hsep' hord' := by
    let A_pos := liftDeleteVerticesLeft G W hW A' hsep'.left_le
    let B_neg := liftDeleteVerticesRight G W hW hG hsep'
    have hsep := liftDeleteVertices_isSeparation hW hG hsep'
    have hord : separationOrder A_pos B_neg < θ := by
      rw [liftDeleteVertices_separationOrder hW hG hsep']
      omega
    have hW_AB : W ⊆ (A_pos ∩ B_neg).vertexSet :=
      Set.subset_inter Set.subset_union_right Set.subset_union_right
    have hW_BA : W ⊆ (B_neg ∩ A_pos).vertexSet :=
      Set.subset_inter Set.subset_union_right Set.subset_union_right
    have hA_del : A_pos.deleteVertices W = A' :=
      deleteVertices_liftDeleteVerticesLeft hW hsep'.left_le
    have hB_del : B_neg.deleteVertices W = B' :=
      deleteVertices_liftDeleteVerticesRight hW hG hsep'
    rcases h𝒯.axiom1 hsep hord with hm | hm
    · exact Or.inl ⟨hsep', hord', ⟨(A_pos, B_neg), hm, hW_AB, hA_del, hB_del⟩⟩
    · exact Or.inr ⟨hsep'.symm, by rwa [separationOrder_comm],
        ⟨(B_neg, A_pos), hm, hW_BA, hB_del, hA_del⟩⟩
  axiom2 A₁' B₁' A₂' B₂' A₃' B₃' h₁ h₂ h₃ hU' := by
    let A₁_pos := liftDeleteVerticesLeft G W hW A₁' h₁.1.left_le
    let B₁_neg := liftDeleteVerticesRight G W hW hG h₁.1
    let A₂_pos := liftDeleteVerticesLeft G W hW A₂' h₂.1.left_le
    let B₂_neg := liftDeleteVerticesRight G W hW hG h₂.1
    let A₃_pos := liftDeleteVerticesLeft G W hW A₃' h₃.1.left_le
    let B₃_neg := liftDeleteVerticesRight G W hW hG h₃.1
    have lift_mem : ∀ {A' B' : Hypergraph α β} (h : (A', B') ∈ deleteVerticesTangle G W 𝒯 θ),
        (liftDeleteVerticesLeft G W hW A' h.1.left_le,
          liftDeleteVerticesRight G W hW hG h.1) ∈ 𝒯 := by
      intro A' B' h
      rcases h.2.2 with ⟨⟨A, B⟩, hm, hW_sub, hA_eq, hB_eq⟩
      dsimp only at hm hW_sub hA_eq hB_eq
      have hsep := liftDeleteVertices_isSeparation hW hG h.1
      have hord : separationOrder
          (liftDeleteVerticesLeft G W hW A' h.1.left_le)
          (liftDeleteVerticesRight G W hW hG h.1) < θ := by
        rw [liftDeleteVertices_separationOrder hW hG h.1]
        have := h.2.1
        omega
      have hVB : B.vertexSet ⊆ (liftDeleteVerticesRight G W hW hG h.1).vertexSet := by
        have hWB : W ⊆ B.vertexSet := hW_sub.trans Set.inter_subset_right
        have hB'_eq : B.vertexSet \ W = B'.vertexSet := congrArg Hypergraph.vertexSet hB_eq
        change B.vertexSet ⊆ B'.vertexSet ∪ W
        rw [← hB'_eq, Set.sdiff_union_of_subset hWB]
      exact theorem_2_9_case_1 h𝒯 hm hsep hord hVB
    have hm₁ := lift_mem h₁
    have hm₂ := lift_mem h₂
    have hm₃ := lift_mem h₃
    apply h𝒯.axiom2 hm₁ hm₂ hm₃
    have hU_le : A₁_pos ∪ A₂_pos ∪ A₃_pos ≤ G :=
      union_le (union_le (h𝒯.isSeparation hm₁).left_le (h𝒯.isSeparation hm₂).left_le)
        (h𝒯.isSeparation hm₃).left_le
    have hVU' : A₁'.vertexSet ∪ A₂'.vertexSet ∪ A₃'.vertexSet = G.vertexSet \ W :=
      congrArg Hypergraph.vertexSet hU'
    have hEU' : A₁'.edgeSet ∪ A₂'.edgeSet ∪ A₃'.edgeSet = (G.deleteVertices W).edgeSet :=
      congrArg Hypergraph.edgeSet hU'
    refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl ?_ ?_
    · change (A₁'.vertexSet ∪ W) ∪ (A₂'.vertexSet ∪ W) ∪ (A₃'.vertexSet ∪ W) = G.vertexSet
      have h1 : (A₁'.vertexSet ∪ W) ∪ (A₂'.vertexSet ∪ W) ∪ (A₃'.vertexSet ∪ W) =
          (A₁'.vertexSet ∪ A₂'.vertexSet ∪ A₃'.vertexSet) ∪ W := by
        ext v; simp only [Set.mem_union]; tauto
      rw [h1, hVU', Set.sdiff_union_of_subset hW]
    · ext e
      simp only [union_edgeSet, Set.mem_union]
      refine ⟨fun h ↦ hU_le.edgeSet_subset h, fun heG ↦ ?_⟩
      by_cases he_del : e ∈ (G.deleteVertices W).edgeSet
      · rcases (hEU'.symm ▸ he_del) with (he₁' | he₂') | he₃'
        · exact Or.inl (Or.inl (Or.inl he₁'))
        · exact Or.inl (Or.inr (Or.inl he₂'))
        · exact Or.inr (Or.inl he₃')
      · have hw_ex : ∃ w ∈ W, G.Inc e w := by
          by_contra! hno
          exact he_del ⟨heG, hno⟩
        obtain ⟨w, hwW, hw_inc⟩ := hw_ex
        have hsub_sdiff := subsingleton_ends_sdiff_of_isGraph hG heG hwW hw_inc
        rcases Set.eq_empty_or_nonempty (G.ends e \ W) with hemp | ⟨u, hu⟩
        · have hsub₁ : G.ends e ⊆ A₁'.vertexSet ∪ W := by
            intro v hv
            by_cases hvW : v ∈ W
            · exact Or.inr hvW
            · exact (Set.notMem_empty v (hemp ▸ ⟨hv, hvW⟩)).elim
          exact Or.inl (Or.inl (Or.inr ⟨⟨heG, he_del⟩, hsub₁⟩))
        · have hu_del : u ∈ G.vertexSet \ W := ⟨G.vertex_mem_of_inc hu.1, hu.2⟩
          have hu_ends : ∀ {V : Set α}, u ∈ V → G.ends e ⊆ V ∪ W := by
            intro V huV v hv
            by_cases hvW : v ∈ W
            · exact Or.inr hvW
            · have hvu : v = u := hsub_sdiff ⟨hv, hvW⟩ hu
              exact Or.inl (hvu ▸ huV)
          rcases (hVU'.symm ▸ hu_del) with (hu₁ | hu₂) | hu₃
          · exact Or.inl (Or.inl (Or.inr ⟨⟨heG, he_del⟩, hu_ends hu₁⟩))
          · exact Or.inl (Or.inr (Or.inr ⟨⟨heG, he_del⟩, hu_ends hu₂⟩))
          · exact Or.inr (Or.inr ⟨⟨heG, he_del⟩, hu_ends hu₃⟩)
  axiom3 A' B' h hVA' := by
    rcases h.2.2 with ⟨⟨A, B⟩, hm, hW_sub, hA_eq, _⟩
    dsimp only at hm hW_sub hA_eq
    apply h𝒯.axiom3 hm
    have hWA : W ⊆ A.vertexSet := hW_sub.trans Set.inter_subset_left
    have hVA'_eq : A.vertexSet \ W = G.vertexSet \ W :=
      (congrArg Hypergraph.vertexSet hA_eq).trans hVA'
    calc
      A.vertexSet = (A.vertexSet \ W) ∪ W := (Set.sdiff_union_of_subset hWA).symm
      _ = (G.vertexSet \ W) ∪ W := by rw [hVA'_eq]
      _ = G.vertexSet := Set.sdiff_union_of_subset hW

end GraphMinor.GM10
