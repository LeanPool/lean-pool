/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM18.Defs
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM18.Section3

/-!
# Graph Minors XVIII, Section 7: More on Isolation

This file formalizes Section 7 (pages 107–108) of Robertson and Seymour,
*Graph Minors. XVIII. Tree-decompositions and well-quasi-ordering*, J. Combin. Theory Ser. B 89
(2003) 77–108:

* `lemma_7_1_claim_1` (7.1, claim (1), page 108): `(A ∪ C, B ∩ D)` has `λ`-order at least that of
  `(C, D)`.
* `lemma_7_1_claim_2` (7.1, claim (2), page 108): `(A ∩ C, B ∪ D)` has `λ`-order at least that of
  `(A, B)`.
* `theorem_7_1` (7.1, pages 107–108): if `𝒯` is a tangle of order `≥ θ ≥ 1` in a hypergraph `G`
  with a tie-breaker `λ`, and `ℒ ⊆ 𝒯` is a location of order `< θ` every member of which is
  `λ`-linked to `𝒯`, then `ℒ` `θ`-isolates `𝒯`.
-/

public section

namespace GraphMinor.GM18

open Hypergraph

universe u v w

variable {α : Type u} {β : Type v} {Λ : Type w} [LinearOrder Λ]

/-- **Graph Minors XVIII, (7.1), Claim (1)** (page 108):
"$(A \cup C, B \cap D)$ has $\lambda$-order at least that of $(C, D)$." -/
theorem lemma_7_1_claim_1 {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hlam : GM10.IsTieBreaker G lam)
    {θ_𝒯 : ℕ} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : GM10.IsTangle G θ_𝒯 𝒯)
    {A B C D : Hypergraph α β} (hAB_𝒯 : (A, B) ∈ 𝒯)
    (hlink : IsLambdaLinkedTo lam 𝒯 C D) :
    lam (C, D) ≤ lam (A ∪ C, B ∩ D) := by
  by_contra! hlt
  have hCD_𝒯 : (C, D) ∈ 𝒯 := hlink.1
  have hsepAB : G.IsSeparation A B := h𝒯.isSeparation hAB_𝒯
  have hsepCD : G.IsSeparation C D := h𝒯.isSeparation hCD_𝒯
  have hsep_union : G.IsSeparation (A ∪ C) (B ∩ D) := hsepAB.union_inter hsepCD
  have hC_le : C ≤ A ∪ C := GM10.le_union_right hsepAB.left_le hsepCD.left_le
  have hBD_le : B ∩ D ≤ D := GM10.inter_le_right hsepAB.right_le hsepCD.right_le
  have hnot_𝒯 : (A ∪ C, B ∩ D) ∉ 𝒯 := fun hm ↦
    not_lt_of_ge (hlink.2 hm hC_le hBD_le) hlt
  have hord_le : separationOrder (A ∪ C) (B ∩ D) ≤ separationOrder C D := by
    by_contra! hord_gt
    exact not_lt_of_gt hlt (hlam.axiom3 hsepCD hsep_union hord_gt)
  have hord_lt : separationOrder (A ∪ C) (B ∩ D) < θ_𝒯 :=
    hord_le.trans_lt (h𝒯.order_lt hCD_𝒯)
  have hswap_𝒯 : (B ∩ D, A ∪ C) ∈ 𝒯 :=
    (h𝒯.axiom1 hsep_union hord_lt).resolve_left hnot_𝒯
  apply h𝒯.axiom2 hswap_𝒯 hAB_𝒯 hCD_𝒯
  rw [GM10.union_assoc, GM10.union_comm (B ∩ D) (A ∪ C), hsep_union.union_eq]

/-- **Graph Minors XVIII, (7.1), Claim (2)** (page 108):
"$(A \cap C, B \cup D)$ has $\lambda$-order at least that of $(A, B)$." -/
theorem lemma_7_1_claim_2 {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hlam : GM10.IsTieBreaker G lam)
    {θ_𝒯 θ' : ℕ} {𝒯 𝒯' : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : GM10.IsTangle G θ_𝒯 𝒯) (h𝒯' : GM10.IsTangle G θ' 𝒯')
    {A B C D : Hypergraph α β} (hCD_𝒯 : (C, D) ∈ 𝒯) (hDC_𝒯' : (D, C) ∈ 𝒯')
    (hdist : GM10.IsDistinction lam 𝒯 𝒯' A B) :
    lam (A, B) ≤ lam (A ∩ C, B ∪ D) := by
  by_contra! hlt
  have hAB_𝒯 : (A, B) ∈ 𝒯 := hdist.1.1
  have hBA_𝒯' : (B, A) ∈ 𝒯' := hdist.1.2
  have hsepAB : G.IsSeparation A B := h𝒯.isSeparation hAB_𝒯
  have hsepCD : G.IsSeparation C D := h𝒯.isSeparation hCD_𝒯
  have hsep_inter : G.IsSeparation (A ∩ C) (B ∪ D) :=
    (hsepAB.symm.union_inter hsepCD.symm).symm
  have hord_le : separationOrder (A ∩ C) (B ∪ D) ≤ separationOrder A B := by
    by_contra! hord_gt
    exact not_lt_of_gt hlt (hlam.axiom3 hsepAB hsep_inter hord_gt)
  have hord_lt_𝒯 : separationOrder (A ∩ C) (B ∪ D) < θ_𝒯 :=
    hord_le.trans_lt (h𝒯.order_lt hAB_𝒯)
  have hord_lt_𝒯' : separationOrder (A ∩ C) (B ∪ D) < θ' := by
    have hord_BA : separationOrder A B < θ' := by
      rw [GM10.separationOrder_comm]
      exact h𝒯'.order_lt hBA_𝒯'
    exact hord_le.trans_lt hord_BA
  have hAC_𝒯 : (A ∩ C, B ∪ D) ∈ 𝒯 :=
    GM10.theorem_2_9_proof h𝒯 hAB_𝒯 hsep_inter hord_lt_𝒯 (Or.inr (Or.inl Set.inter_subset_left))
  have hAC_not_𝒯' : (A ∩ C, B ∪ D) ∉ 𝒯' := by
    intro hm
    apply h𝒯'.axiom2 hBA_𝒯' hDC_𝒯' hm
    exact hsep_inter.symm.union_eq
  have hBD_𝒯' : (B ∪ D, A ∩ C) ∈ 𝒯' :=
    (h𝒯'.axiom1 hsep_inter hord_lt_𝒯').resolve_left hAC_not_𝒯'
  have hdist_AC : GM10.Distinguishes 𝒯 𝒯' (A ∩ C) (B ∪ D) := ⟨hAC_𝒯, hBD_𝒯'⟩
  exact not_lt_of_ge (hdist.2 hdist_AC) hlt

/-- **Graph Minors XVIII, (7.1)** (pages 107–108):
"Let $\mathscr{T}$ be a tangle of order $\ge \theta \ge 1$ in a hypergraph $G$ with a
tie-breaker $\lambda$, and let $\mathscr{L} \subseteq \mathscr{T}$ be a location of order $<
\theta$, every member of which is $\lambda$-linked to $\mathscr{T}$. Then $\mathscr{L}$
$\theta$-isolates $\mathscr{T}$." -/
theorem theorem_7_1_proof {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hlam : GM10.IsTieBreaker G lam)
    {θ θ_𝒯 : ℕ} {𝒯 ℒ : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : GM10.IsTangle G θ_𝒯 𝒯) (_hθ_le : θ ≤ θ_𝒯)
    (hℒ : GM10.IsLocation G ℒ) (hℒ_sub : ℒ ⊆ 𝒯)
    (hord : locationOrder ℒ < θ)
    (hlink : ∀ ⦃C D : Hypergraph α β⦄, (C, D) ∈ ℒ → IsLambdaLinkedTo lam 𝒯 C D) :
    Isolates G lam θ 𝒯 ℒ where
  isLocation := hℒ
  subset := hℒ_sub
  locationOrder_lt := hord
  order_lt _ _ hp := separationOrder_lt_of_locationOrder_lt hℒ hord hp
  distinction_le C D hCD_ℒ θ' 𝒯' h𝒯' hθ_le' hDC_𝒯' A B hdist := by
    have hAB_𝒯 : (A, B) ∈ 𝒯 := hdist.1.1
    have hBA_𝒯' : (B, A) ∈ 𝒯' := hdist.1.2
    have hCD_𝒯 : (C, D) ∈ 𝒯 := hℒ_sub hCD_ℒ
    have hsepAB : G.IsSeparation A B := h𝒯.isSeparation hAB_𝒯
    have hsepCD : G.IsSeparation C D := h𝒯.isSeparation hCD_𝒯
    have hsep_union : G.IsSeparation (A ∪ C) (B ∩ D) := hsepAB.union_inter hsepCD
    have hclaim1 : lam (C, D) ≤ lam (A ∪ C, B ∩ D) :=
      lemma_7_1_claim_1 hlam h𝒯 hAB_𝒯 (hlink hCD_ℒ)
    have hclaim2 : lam (A, B) ≤ lam (A ∩ C, B ∪ D) :=
      lemma_7_1_claim_2 hlam h𝒯 h𝒯' hCD_𝒯 hDC_𝒯' hdist
    have hax2 := hlam.axiom2 hsepCD hsepAB
    rw [GM10.union_comm C A, GM10.inter_comm D B,
      GM10.inter_comm C A, GM10.union_comm D B] at hax2
    have hle_CD : lam (A ∪ C, B ∩ D) ≤ lam (C, D) :=
      hax2.resolve_right (not_lt_of_ge hclaim2)
    have hlam_eq : lam (A ∪ C, B ∩ D) = lam (C, D) := le_antisymm hle_CD hclaim1
    rcases (hlam.axiom1 hsep_union hsepCD).1 hlam_eq with ⟨hAC, hBD⟩ | ⟨hAD, hBC⟩
    · exact ⟨hAC ▸ GM10.le_union_left hsepAB.left_le hsepCD.left_le,
        hBD.symm ▸ GM10.inter_le_left hsepAB.right_le hsepCD.right_le⟩
    · exfalso
      have hord_CD_lt : separationOrder C D < θ' :=
        (separationOrder_lt_of_locationOrder_lt hℒ hord hCD_ℒ).trans_le hθ_le'
      have hsep_swap : G.IsSeparation (B ∩ D) (A ∪ C) := hsep_union.symm
      have hord_swap_lt : separationOrder (B ∩ D) (A ∪ C) < θ' := by
        rw [hBC, hAD]
        exact hord_CD_lt
      have hswap_𝒯' : (B ∩ D, A ∪ C) ∈ 𝒯' :=
        GM10.theorem_2_9_proof h𝒯' hBA_𝒯' hsep_swap hord_swap_lt
          (Or.inr (Or.inl Set.inter_subset_left))
      rw [hBC, hAD] at hswap_𝒯'
      exact GM10.theorem_2_1_proof h𝒯' hDC_𝒯' hswap_𝒯'

end GraphMinor.GM18
