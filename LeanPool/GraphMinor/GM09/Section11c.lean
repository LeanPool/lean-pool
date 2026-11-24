/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module
public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM09.Section11a
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section3a

/-!
# Graph Minors IX, Section 11 (Part 3): Feasible Segregations and the Claims of (11.11)

This file formalizes Claims (1)–(5) of (11.11) from Section 11 of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77 (pages 74–77). The proof of (11.11) itself is in
`Section11d.lean`.
-/

@[expose] public section

namespace GraphMinor.GM09
open Set Graph GraphMinor.Surface GraphMinor.GM06
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## Finiteness of consolidations and existence of a minimal consolidation -/

/-- The set of subgraphs of `S.G` is finite. -/
theorem Society.finite_subgraphs (S : Society α β) : {H : Graph α β | H ≤ S.G}.Finite := by
  let f : Graph α β → Set α × Set β := fun H => (V(H), E(H))
  have hsub : f '' {H : Graph α β | H ≤ S.G} ⊆ V(S.G).powerset ×ˢ E(S.G).powerset := by
    rintro _ ⟨H, hH, rfl⟩; exact ⟨hH.vertexSet_mono, hH.edgeSet_mono⟩
  exact ((S.finite_V.powerset.prod S.finite_E.powerset).subset hsub).of_finite_image
    fun H₁ h₁ H₂ h₂ heq => (Compatible.of_le_le h₁ h₂).ext (Prod.mk.inj heq).1 (Prod.mk.inj heq).2

/-- Every consolidation of a society `S` is a finite set of separations. -/
theorem IsConsolidation.finite {S : Society α β} {D_set : Set (Graph α β × Graph α β)}
    (hD : IsConsolidation S D_set) : D_set.Finite :=
  (S.finite_subgraphs.prod S.finite_subgraphs).subset fun ⟨_, _⟩ hAB => ⟨hD.left_le hAB,
    hD.right_le hAB⟩

/-- By (11.6), every society `S` has a consolidation `D_set` such that its core has as few vertices
as possible, and subject to that `|D_set|` is minimum (Graph Minors IX, (11.11), page 74). -/
theorem exists_minimal_consolidation (S : Society α β) :
    ∃ D_set : Set (Graph α β × Graph α β),
      IsConsolidation S D_set ∧
      (∀ D_set' : Set (Graph α β × Graph α β), IsConsolidation S D_set' →
        V(consolidationCore S D_set).ncard ≤ V(consolidationCore S D_set').ncard) ∧
      (∀ D_set' : Set (Graph α β × Graph α β), IsConsolidation S D_set' →
        V(consolidationCore S D_set').ncard = V(consolidationCore S D_set).ncard →
        D_set.ncard ≤ D_set'.ncard) := by
  classical
  have hex₁ : ∃ n : ℕ, ∃ D_set : Set (Graph α β × Graph α β),
      IsConsolidation S D_set ∧ V(consolidationCore S D_set).ncard = n := by
    obtain ⟨D₀, hD₀⟩ := theorem_11_6_proof S; exact ⟨_, D₀, hD₀, rfl⟩
  let n₀ := Nat.find hex₁
  have hn₀_spec : ∃ D_set : Set (Graph α β × Graph α β),
      IsConsolidation S D_set ∧ V(consolidationCore S D_set).ncard = n₀ := Nat.find_spec hex₁
  have hex₂ : ∃ m : ℕ, ∃ D_set : Set (Graph α β × Graph α β),
      IsConsolidation S D_set ∧ V(consolidationCore S D_set).ncard = n₀ ∧ D_set.ncard = m := by
    obtain ⟨D₁, hD₁, hn₁⟩ := hn₀_spec; exact ⟨_, D₁, hD₁, hn₁, rfl⟩
  let m₀ := Nat.find hex₂
  obtain ⟨D_set, hD, hn_eq, hm_eq⟩ := Nat.find_spec hex₂
  refine ⟨D_set, hD, fun D_set' hD' => ?_, fun D_set' hD' hn' => ?_⟩
  · rw [hn_eq]; exact Nat.find_min' hex₁ ⟨D_set', hD', rfl⟩
  · rw [hm_eq]; exact Nat.find_min' hex₂ ⟨D_set', hD', hn'.trans hn_eq, rfl⟩

/-! ## Claim (1) of (11.11) -/

/-- **Graph Minors IX, (11.11), Claim (1)** (pages 74–75):
"If $(A, B), (A', B') \in \mathcal{D}$ are distinct then $V(A \cap B) \not\subseteq V(A')$." -/
theorem lemma_11_11_claim_1 {S : Society α β} {D_set : Set (Graph α β × Graph α β)}
    (hD : IsConsolidation S D_set)
    (hmin_card : ∀ D_set' : Set (Graph α β × Graph α β), IsConsolidation S D_set' →
      V(consolidationCore S D_set').ncard = V(consolidationCore S D_set).ncard →
      D_set.ncard ≤ D_set'.ncard)
    {A B A' B' : Graph α β} (hAB : (A, B) ∈ D_set) (hA'B' : (A', B') ∈ D_set)
    (hne : (A, B) ≠ (A', B')) : ¬ (V(A) ∩ V(B) ⊆ V(A')) := by
  intro hsub
  let A_star : Graph α β := subgraphUnion S.G A A'
  let B_star : Graph α β := subgraphInter S.G B B'
  let D_rest : Set (Graph α β × Graph α β) := D_set \ {(A, B), (A', B')}
  let D_set' : Set (Graph α β × Graph α β) := insert (A_star, B_star) D_rest
  have hA_le : A ≤ S.G := hD.left_le hAB
  have hB_le : B ≤ S.G := hD.right_le hAB
  have hA'_le : A' ≤ S.G := hD.left_le hA'B'
  have hB'_le : B' ≤ S.G := hD.right_le hA'B'
  have hA_le_B' : A ≤ B' := hD.left_le_right hAB hA'B' hne
  have hA'_le_B : A' ≤ B := hD.left_le_right hA'B' hAB hne.symm
  have hA_star_le : A_star ≤ S.G := subgraphUnion_le hA_le hA'_le
  have hB_star_le : B_star ≤ S.G := subgraphInter_le hB_le
  have hV_inter_star : V(A_star) ∩ V(B_star) = V(A') ∩ V(B') := by
    ext v; simp only [A_star, B_star, vertexSet_subgraphUnion, vertexSet_subgraphInter,
      mem_inter_iff, mem_union]
    refine ⟨fun ⟨hvAA', hvB, hvB'⟩ => ⟨?_, hvB'⟩,
      fun ⟨hvA', hvB'⟩ => ⟨Or.inr hvA', hA'_le_B.vertexSet_mono hvA', hvB'⟩⟩
    rcases hvAA' with hvA | hvA'
    · exact hsub ⟨hvA, hvB⟩
    · exact hvA'
  have hsep_star : S.IsSocietySeparation A_star B_star := by
    have hsep := (hD.isSocietySeparation hAB).1
    have hsep' := (hD.isSocietySeparation hA'B').1
    refine ⟨⟨hA_star_le, hB_star_le, ?_, ?_, ?_⟩,
      subset_inter (hD.isSocietySeparation hAB).2 (hD.isSocietySeparation hA'B').2⟩
    · refine subset_antisymm (union_subset hA_star_le.vertexSet_mono hB_star_le.vertexSet_mono) fun
      v hv => ?_
      have hv1 : v ∈ V(A) ∪ V(B) := hsep.2.2.1 ▸ hv
      have hv2 : v ∈ V(A') ∪ V(B') := hsep'.2.2.1 ▸ hv
      rcases hv1 with hvA | hvB
      · exact Or.inl (Or.inl hvA)
      · rcases hv2 with hvA' | hvB'
        · exact Or.inl (Or.inr hvA')
        · exact Or.inr ⟨hvB, hvB'⟩
    · rw [edgeSet_subgraphUnion hA_le hA'_le, edgeSet_subgraphInter hB_le hB'_le]
      refine subset_antisymm (union_subset (union_subset hA_le.edgeSet_mono hA'_le.edgeSet_mono)
        (inter_subset_left.trans hB_le.edgeSet_mono)) fun e he => ?_
      have he1 : e ∈ E(A) ∪ E(B) := hsep.2.2.2.1 ▸ he
      have he2 : e ∈ E(A') ∪ E(B') := hsep'.2.2.2.1 ▸ he
      rcases he1 with heA | heB
      · exact Or.inl (Or.inl heA)
      · rcases he2 with heA' | heB'
        · exact Or.inl (Or.inr heA')
        · exact Or.inr ⟨heB, heB'⟩
    · rw [edgeSet_subgraphUnion hA_le hA'_le, edgeSet_subgraphInter hB_le hB'_le,
        disjoint_union_left]
      exact ⟨hsep.2.2.2.2.mono_right inter_subset_left, hsep'.2.2.2.2.mono_right inter_subset_right⟩
  have hD' : IsConsolidation S D_set' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro X Y (h_eq | ⟨hXY, _⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq; exact hsep_star
      · exact hD.isSocietySeparation hXY
    · rintro X Y (h_eq | ⟨hXY, _⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq; rw [hV_inter_star]; exact hD.order_le_three hA'B'
      · exact hD.order_le_three hXY
    · rintro X₁ Y₁ X₂ Y₂ (h1 | ⟨h1_in, h1_not⟩) (h2 | ⟨h2_in, h2_not⟩) hne12
      · exact (hne12 (h1.trans h2.symm)).elim
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
        rw [mem_insert_iff, mem_singleton_iff, not_or] at h2_not
        exact (subgraphUnion_le_iff hA_le hA'_le (hD.right_le h2_in)).mpr
          ⟨hD.left_le_right hAB h2_in (Ne.symm h2_not.1), hD.left_le_right hA'B' h2_in
            (Ne.symm h2_not.2)⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
        rw [mem_insert_iff, mem_singleton_iff, not_or] at h1_not
        exact le_subgraphInter hB_le hB'_le
          (hD.left_le_right h1_in hAB h1_not.1) (hD.left_le_right h1_in hA'B' h1_not.2)
      · exact hD.left_le_right h1_in h2_in hne12
    · have hP' : ∀ P ∈ Prod.fst '' D_set', P ≤ S.G := by
        rintro P ⟨⟨X, Y⟩, h_eq | ⟨hXY, _⟩, rfl⟩
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq; exact hA_star_le
        · exact hD.left_le hXY
      refine (Compatible.of_le_le (subgraphSUnion_le hP') le_rfl).ext
        (subset_antisymm (subgraphSUnion_le hP').vertexSet_mono fun v hv => ?_)
        (subset_antisymm (subgraphSUnion_le hP').edgeSet_mono fun e he => ?_)
      · obtain ⟨X, Y, hXY, hvX⟩ := hD.exists_mem_of_mem_vertexSet hv
        rw [vertexSet_subgraphSUnion, mem_iUnion₂]
        by_cases h_pair : (X, Y) ∈ ({(A, B), (A', B')} : Set (Graph α β × Graph α β))
        · refine ⟨A_star, ⟨(A_star, B_star), Or.inl rfl, rfl⟩, ?_⟩
          rcases h_pair with h_eq | h_eq <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq
          · exact Or.inl hvX
          · exact Or.inr hvX
        · exact ⟨X, ⟨(X, Y), Or.inr ⟨hXY, h_pair⟩, rfl⟩, hvX⟩
      · obtain ⟨X, Y, hXY, heX⟩ := hD.exists_mem_of_mem_edgeSet he
        rw [edgeSet_subgraphSUnion hP', mem_iUnion₂]
        by_cases h_pair : (X, Y) ∈ ({(A, B), (A', B')} : Set (Graph α β × Graph α β))
        · refine ⟨A_star, ⟨(A_star, B_star), Or.inl rfl, rfl⟩, ?_⟩
          rw [edgeSet_subgraphUnion hA_le hA'_le]
          rcases h_pair with h_eq | h_eq <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq
          · exact Or.inl heX
          · exact Or.inr heX
        · exact ⟨X, ⟨(X, Y), Or.inr ⟨hXY, h_pair⟩, rfl⟩, heX⟩
    · rintro X Y (h_eq | ⟨hXY, _⟩) u hu v hv huv
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq
        rw [hV_inter_star] at hu hv
        obtain ⟨P, hP, hdisj⟩ := hD.exists_path hA'B' u hu v hv huv
        exact ⟨P, hP.mono (le_subgraphUnion_right hA_le hA'_le), hdisj.mono_right
          inter_subset_right⟩
      · exact hD.exists_path hXY u hu v hv huv
  have hV_core_eq : V(consolidationCore S D_set') = V(consolidationCore S D_set) := by
    ext v; simp only [vertexSet_consolidationCore, mem_inter_iff, mem_iInter, and_congr_right_iff]
    intro _
    constructor
    · intro h pair hXY
      obtain ⟨X, Y⟩ := pair
      by_cases h_pair : (X, Y) ∈ ({(A, B), (A', B')} : Set (Graph α β × Graph α β))
      · have hv_star : v ∈ V(B) ∩ V(B') := h (A_star, B_star) (Or.inl rfl)
        rcases h_pair with h_eq | h_eq <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq
        · exact hv_star.1
        · exact hv_star.2
      · exact h (X, Y) (Or.inr ⟨hXY, h_pair⟩)
    · intro h pair hXY'
      obtain ⟨X, Y⟩ := pair
      rcases hXY' with h_eq | ⟨hXY, _⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq; exact ⟨h (A, B) hAB, h (A', B') hA'B'⟩
      · exact h (X, Y) hXY
  have hle_card : D_set.ncard ≤ D_set'.ncard := hmin_card D_set' hD' (by rw [hV_core_eq])
  have hfin_rest : D_rest.Finite := hD.finite.subset sdiff_subset
  have hD_eq : D_set = insert (A, B) (insert (A', B') D_rest) := by
    ext p; simp only [D_rest, mem_insert_iff, mem_sdiff, mem_singleton_iff]
    refine ⟨fun hp => ?_, ?_⟩
    · by_cases h1 : p = (A, B)
      · exact Or.inl h1
      · by_cases h2 : p = (A', B')
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨hp, not_or.mpr ⟨h1, h2⟩⟩)
    · rintro (rfl | rfl | ⟨hp, _⟩) <;> assumption
  have hnot1 : (A', B') ∉ D_rest := fun h => h.2 (Or.inr rfl)
  have hnot2 : (A, B) ∉ insert (A', B') D_rest := by
    rw [mem_insert_iff, not_or]; exact ⟨hne, fun h => h.2 (Or.inl rfl)⟩
  have hcard_D : D_set.ncard = D_rest.ncard + 2 := by
    conv_lhs => rw [hD_eq]
    rw [ncard_insert_of_notMem hnot2 (hfin_rest.insert (A', B')),
      ncard_insert_of_notMem hnot1 hfin_rest]
  have hcard_D' : D_set'.ncard ≤ D_rest.ncard + 1 := ncard_insert_le (A_star, B_star) D_rest
  omega

/-- By Claim (1), distinct members of a minimal consolidation have distinct boundary sets
`V(A) ∩ V(B)`. -/
theorem eq_of_inter_eq_of_minimal_consolidation {S : Society α β} {D_set : Set
  (Graph α β × Graph α β)}
    (hD : IsConsolidation S D_set)
    (hmin_card : ∀ D_set' : Set (Graph α β × Graph α β), IsConsolidation S D_set' →
      V(consolidationCore S D_set').ncard = V(consolidationCore S D_set).ncard →
      D_set.ncard ≤ D_set'.ncard)
    {A B A' B' : Graph α β} (hAB : (A, B) ∈ D_set) (hA'B' : (A', B') ∈ D_set)
    (heq : V(A) ∩ V(B) = V(A') ∩ V(B')) : (A, B) = (A', B') := by
  by_contra hne
  exact lemma_11_11_claim_1 hD hmin_card hAB hA'B' hne (heq ▸ inter_subset_left)

/-! ## Pattern invariance of transaction cardinality and crookedness -/

/-- For any transaction `P_set` in a society `S`, the map `P ↦ pathEnds S.G P` is injective on
`P_set`,
so `(S.transactionPattern P_set).ncard = P_set.ncard`. -/
theorem ncard_transactionPattern_eq {S : Society α β} {P_set : Set (Graph α β)}
    (hP : S.IsTransaction P_set) : (S.transactionPattern P_set).ncard = P_set.ncard := by
  rcases hP with ⟨A_f, B_f, hdisj, _, hends⟩
  refine Set.InjOn.ncard_image fun P₁ h₁ P₂ h₂ heq => by_contra fun hne => ?_
  obtain ⟨a₁, _, b₁, _, hP₁_ab⟩ := hends P₁ h₁
  obtain ⟨a₂, _, b₂, _, hP₂_ab⟩ := hends P₂ h₂
  have ha₁_ends : a₁ ∈ pathEnds S.G P₂ := by
    rw [← heq, hP₁_ab.1.pathEnds_eq]; exact Or.inl rfl
  rw [hP₂_ab.1.pathEnds_eq] at ha₁_ends
  have ha₁_P₂ : a₁ ∈ V(P₂) := by
    rcases ha₁_ends with rfl | rfl
    · exact hP₂_ab.1.left_mem
    · exact hP₂_ab.1.right_mem
  exact disjoint_left.mp (hdisj.2 h₁ h₂ hne) hP₁_ab.1.left_mem ha₁_P₂

/-- For any transaction `P_set` in `S`, `S.transactionEnds P_set = ⋃₀ (S.transactionPattern P_set)`.
-/
theorem transactionEnds_eq_sUnion_transactionPattern {S : Society α β} {P_set : Set (Graph α β)}
    (hP : S.IsTransaction P_set) : S.transactionEnds P_set = ⋃₀ (S.transactionPattern P_set) := by
  rcases hP with ⟨A_f, B_f, _, _, hends⟩
  ext v; simp only [Society.transactionEnds, Society.transactionPattern, mem_ofPred_eq, mem_sUnion,
    mem_image, exists_exists_and_eq_and]
  refine ⟨fun ⟨P, hP_in, b, hP_ab⟩ => ⟨P, hP_in, ?_⟩, fun ⟨P, hP_in, hv⟩ => ?_⟩
  · rw [hP_ab.1.pathEnds_eq]; exact Or.inl rfl
  · obtain ⟨a, _, b, _, hP_ab⟩ := hends P hP_in
    rw [hP_ab.1.pathEnds_eq, mem_insert_iff, mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact ⟨P, hP_in, b, hP_ab⟩
    · exact ⟨P, hP_in, a, hP_ab.1.symm, hP_ab.2.1.symm, hP_ab.2.2.2, hP_ab.2.2.1⟩

/-- Whether a transaction `P_set` is crooked depends only on `S.Ω` and `S.transactionPattern P_set`.
-/
theorem isCrookedTransaction_iff_of_transactionPattern_eq {S₁ : Society α β} {S₂ : Society α γ}
    (hΩ : S₁.Ω = S₂.Ω) {P₁ : Set (Graph α β)} {P₂ : Set (Graph α γ)}
    (hT₁ : S₁.IsTransaction P₁) (hT₂ : S₂.IsTransaction P₂)
    (hpat : S₁.transactionPattern P₁ = S₂.transactionPattern P₂) :
    S₁.IsCrookedTransaction P₁ ↔ S₂.IsCrookedTransaction P₂ := by
  have hends_eq : S₁.transactionEnds P₁ = S₂.transactionEnds P₂ := by
    rw [transactionEnds_eq_sUnion_transactionPattern hT₁,
      transactionEnds_eq_sUnion_transactionPattern hT₂, hpat]
  refine ⟨fun ⟨_, hno₁⟩ => ⟨hT₂, fun Q hQ ⟨_, a, b, hQ_ab, hdisj⟩ => ?_⟩,
    fun ⟨_, hno₂⟩ => ⟨hT₁, fun P hP ⟨_, a, b, hP_ab, hdisj⟩ => ?_⟩⟩
  · have h_in_pat : pathEnds S₂.G Q ∈ S₁.transactionPattern P₁ := by
      rw [hpat]; exact ⟨Q, hQ, rfl⟩
    obtain ⟨P, hP, hends_P⟩ := h_in_pat
    dsimp only at hends_P
    rcases hT₁ with ⟨A_f, B_f, _, _, hends₁⟩
    obtain ⟨a', _, b', _, hP_a'b'⟩ := hends₁ P hP
    have hpair : ({a', b'} : Set α) = {a, b} := by
      rw [← hP_a'b'.1.pathEnds_eq, hends_P, hQ_ab.1.pathEnds_eq]
    have ha_in : a ∈ ({a', b'} : Set α) := hpair.symm ▸ Or.inl rfl
    have hb_in : b ∈ ({a', b'} : Set α) := hpair.symm ▸ Or.inr rfl
    have hP_ab : S₁.IsOmegaPathWithEnds P a b := by
      rcases ha_in with rfl | rfl <;> rcases hb_in with rfl | rfl
      · exact (hQ_ab.2.1 rfl).elim
      · exact hP_a'b'
      · exact ⟨hP_a'b'.1.symm, hP_a'b'.2.1.symm, hP_a'b'.2.2.2, hP_a'b'.2.2.1⟩
      · exact (hQ_ab.2.1 rfl).elim
    exact hno₁ P hP ⟨hP, a, b, hP_ab, by rwa [hΩ, hends_eq]⟩
  · have h_in_pat : pathEnds S₁.G P ∈ S₂.transactionPattern P₂ := by
      rw [← hpat]; exact ⟨P, hP, rfl⟩
    obtain ⟨Q, hQ, hends_Q⟩ := h_in_pat
    dsimp only at hends_Q
    rcases hT₂ with ⟨A_f, B_f, _, _, hends₂⟩
    obtain ⟨a', _, b', _, hQ_a'b'⟩ := hends₂ Q hQ
    have hpair : ({a', b'} : Set α) = {a, b} := by
      rw [← hQ_a'b'.1.pathEnds_eq, hends_Q, hP_ab.1.pathEnds_eq]
    have ha_in : a ∈ ({a', b'} : Set α) := hpair.symm ▸ Or.inl rfl
    have hb_in : b ∈ ({a', b'} : Set α) := hpair.symm ▸ Or.inr rfl
    have hQ_ab : S₂.IsOmegaPathWithEnds Q a b := by
      rcases ha_in with rfl | rfl <;> rcases hb_in with rfl | rfl
      · exact (hP_ab.2.1 rfl).elim
      · exact hQ_a'b'
      · exact ⟨hQ_a'b'.1.symm, hQ_a'b'.2.1.symm, hQ_a'b'.2.2.2, hQ_a'b'.2.2.1⟩
      · exact (hP_ab.2.1 rfl).elim
    exact hno₂ Q hQ ⟨hQ, a, b, hQ_ab, by rwa [← hΩ, ← hends_eq]⟩

/-- By (11.10), if `(G, Ω)` has no crooked transaction of cardinality `p`, then its consolidation
core `(C, Ω)` also has no crooked transaction of cardinality `p` (Graph Minors IX, (11.11), page
75). -/
theorem no_crooked_transaction_consolidationCoreSociety {S : Society α β}
    {D_set : Set (Graph α β × Graph α β)} (hD : IsConsolidation S D_set) {p : ℕ}
    (hno_crooked : ∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ p) :
    ∀ Q_set : Set (Graph α (Sym2 α)),
      (consolidationCoreSociety S D_set hD).IsCrookedTransaction Q_set → Q_set.ncard ≠ p := by
  intro Q_set hQ_crooked hcard
  obtain ⟨P_set, hP_trans, hpat⟩ := exists_transaction_of_core_transaction hD hQ_crooked.1
  have hP_crooked : S.IsCrookedTransaction P_set :=
    (isCrookedTransaction_iff_of_transactionPattern_eq
      (consolidationCoreSociety_Ω S D_set hD).symm hP_trans hQ_crooked.1 hpat).mpr hQ_crooked
  have hcard_P : P_set.ncard = p := by
    rw [← ncard_transactionPattern_eq hP_trans, hpat, ncard_transactionPattern_eq hQ_crooked.1,
      hcard]
  exact hno_crooked P_set hP_crooked hcard_P

/-! ## Partitioning `D_set` into `D₁` and `D₂` and Claims (2)–(5) of (11.11) -/

/-- A subset `K ⊆ V(G)` of a simple graph `G : Graph α (Sym2 α)` is a `≤ 3`-clique if `|K| ≤ 3` and
every two distinct vertices of `K` are adjacent in `G` (Graph Minors IX, (11.11), page 76). -/
def IsLeThreeClique (G : Graph α (Sym2 α)) (K : Set α) : Prop :=
  K ⊆ V(G) ∧ K.ncard ≤ 3 ∧ ∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.IsLink s(u, v) u v

/-- A 3-element clique `{x, y, z}` in `C : Graph α (Sym2 α)` forms a triangle `T ≤ C` with
`IsTriangle C T` and `V(T) = {x, y, z}`. -/
theorem exists_triangle_of_three_clique {C : Graph α (Sym2 α)} {x y z : α}
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hl_xy : C.IsLink s(x, y) x y) (hl_yz : C.IsLink s(y, z) y z) (hl_zx : C.IsLink s(z, x) z x) :
    ∃ T : Graph α (Sym2 α), IsTriangle C T ∧ V(T) = {x, y, z} ∧
      T.IsLink s(x, y) x y ∧ T.IsLink s(y, z) y z ∧ T.IsLink s(z, x) z x := by
  let T : Graph α (Sym2 α) := (C.induce {x, y, z}).restrict {s(x, y), s(y, z), s(z, x)}
  have hTC : T ≤ C := restrict_le.trans (C.induce_le (by
    rintro w (rfl | rfl | rfl); exacts [hl_xy.left_mem, hl_yz.left_mem, hl_zx.left_mem]))
  have hl_xy_T : T.IsLink s(x, y) x y :=
    (hTC.isLink_iff (by refine ⟨⟨x, y, hl_xy, by simp, by simp⟩, by simp⟩)).mpr hl_xy
  have hl_yz_T : T.IsLink s(y, z) y z :=
    (hTC.isLink_iff (by refine ⟨⟨y, z, hl_yz, by simp, by simp⟩, by simp⟩)).mpr hl_yz
  have hl_zx_T : T.IsLink s(z, x) z x :=
    (hTC.isLink_iff (by refine ⟨⟨z, x, hl_zx, by simp, by simp⟩, by simp⟩)).mpr hl_zx
  let W : GraphWalk T x x := .cons hl_xy_T (.cons hl_yz_T (.cons hl_zx_T (.nil hl_xy_T.left_mem)))
  have hne_e12 : (s(x, y) : Sym2 α) ≠ s(y, z) := by
    intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hxy h1
    · exact hzx.symm h1
  have hne_e13 : (s(x, y) : Sym2 α) ≠ s(z, x) := by
    intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hzx.symm h1
    · exact hyz h2
  have hne_e23 : (s(y, z) : Sym2 α) ≠ s(z, x) := by
    intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hyz h1
    · exact hxy.symm h1
  have hET : E(T) = {s(x, y), s(y, z), s(z, x)} := by
    ext e; simp only [mem_insert_iff, mem_singleton_iff]
    refine ⟨fun he => he.2, ?_⟩
    rintro (rfl | rfl | rfl)
    · exact hl_xy_T.edge_mem
    · exact hl_yz_T.edge_mem
    · exact hl_zx_T.edge_mem
  have hcard_E : E(T).ncard = 3 := by
    rw [hET, ncard_insert_of_notMem (by simp [hne_e12, hne_e13]) ((finite_singleton _).insert _),
      ncard_pair hne_e23]
  refine ⟨T, ⟨⟨hTC, x, W, ?_, by simp [W], ?_, ?_⟩, hcard_E⟩, rfl, hl_xy_T, hl_yz_T, hl_zx_T⟩
  · refine ⟨?_, ?_⟩
    · simp [W, hyz, hzx, hxy.symm]
    · simp [W, hne_e12, hne_e13, hne_e23]
  · ext w; simp only [T, vertexSet_restrict, vertexSet_induce, mem_insert_iff, mem_singleton_iff,
      mem_ofPred_eq, W, GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false]
    tauto
  · rw [hET]; ext e; simp [W]

/-- Every finite set `X` with `X.ncard ≤ 3` is either empty, a singleton, a pair of distinct
elements, or a triple of pairwise distinct elements. -/
theorem eq_empty_or_singleton_or_pair_or_triple_of_ncard_le_three {X : Set α}
    (hfin : X.Finite) (hcard : X.ncard ≤ 3) :
    X = ∅ ∨ (∃ x, X = {x}) ∨ (∃ x y, x ≠ y ∧ X = {x, y}) ∨
      (∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ X = {x, y, z}) := by
  rcases X.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact Or.inl rfl
  rcases (X \ {x}).eq_empty_or_nonempty with h1 | ⟨y, hy, hyx⟩
  · right; left; refine ⟨x, subset_antisymm (fun w hw => ?_) (singleton_subset_iff.mpr hx)⟩
    by_contra hwx; exact h1.subset ⟨hw, hwx⟩
  have hxy : x ≠ y := Ne.symm (mem_singleton_iff.not.mp hyx)
  rcases (X \ {x, y}).eq_empty_or_nonempty with h2 | ⟨z, hz, hz_xy⟩
  · right; right; left; refine ⟨x, y, hxy, subset_antisymm (fun w hw => ?_) ?_⟩
    · by_contra hw_xy; exact h2.subset ⟨hw, hw_xy⟩
    · rintro w (rfl | rfl) <;> assumption
  rw [mem_insert_iff, mem_singleton_iff, not_or] at hz_xy
  rcases (X \ {x, y, z}).eq_empty_or_nonempty with h3 | ⟨w, hw, hw_xyz⟩
  · right; right; right
    refine ⟨x, y, z, hxy, Ne.symm hz_xy.2, hz_xy.1, subset_antisymm (fun u hu => ?_) ?_⟩
    · by_contra hu_xyz; exact h3.subset ⟨hu, hu_xyz⟩
    · rintro u (rfl | rfl | rfl) <;> assumption
  exfalso
  rw [mem_insert_iff, mem_insert_iff, mem_singleton_iff, not_or, not_or] at hw_xyz
  have hsub4 : ({x, y, z, w} : Set α) ⊆ X := by rintro u (rfl | rfl | rfl | rfl) <;> assumption
  have hcard4 : ({x, y, z, w} : Set α).ncard = 4 := by
    rw [ncard_insert_of_notMem (by simp [hxy, Ne.symm hz_xy.1, Ne.symm hw_xyz.1])
      (((finite_singleton w).insert z).insert y),
      ncard_insert_of_notMem (by simp [Ne.symm hz_xy.2, Ne.symm hw_xyz.2.1])
      ((finite_singleton w).insert z), ncard_pair (Ne.symm hw_xyz.2.2)]
  have hle := ncard_le_ncard hsub4 hfin; omega

/-- If `C₁, C₂ ≤ C` satisfy `C₁ ∪ C₂ = C` and every triangle of `C` is in `C₁` or `C₂`, then every
`≤ 3`-clique `K` of `C` is a `≤ 3`-clique in `C₁` or in `C₂` (Graph Minors IX, (11.11), page 75). -/
theorem isLeThreeClique_left_or_right {C C₁ C₂ : Graph α (Sym2 α)}
    (hC₁ : C₁ ≤ C) (hC₂ : C₂ ≤ C) (hC_union : subgraphUnion C C₁ C₂ = C)
    (htri : ∀ T : Graph α (Sym2 α), IsTriangle C T → T ≤ C₁ ∨ T ≤ C₂)
    {K : Set α} (hfin : K.Finite) (hK : IsLeThreeClique C K) :
    IsLeThreeClique C₁ K ∨ IsLeThreeClique C₂ K := by
  have hV_union : V(C₁) ∪ V(C₂) = V(C) := by
    have h := congrArg Graph.vertexSet hC_union; rwa [vertexSet_subgraphUnion] at h
  rcases eq_empty_or_singleton_or_pair_or_triple_of_ncard_le_three hfin hK.2.1 with
    rfl | ⟨x, rfl⟩ | ⟨x, y, hxy, rfl⟩ | ⟨x, y, z, hxy, hyz, hzx, rfl⟩
  · exact Or.inl ⟨empty_subset _, by simp, fun _ hu => hu.elim⟩
  · have hxC : x ∈ V(C₁) ∪ V(C₂) := hV_union.symm ▸ hK.1 (mem_singleton x)
    rcases hxC with hx₁ | hx₂
    · exact Or.inl ⟨singleton_subset_iff.mpr hx₁, hK.2.1, fun u hu v hv huv =>
        (huv ((mem_singleton_iff.mp hu).trans (mem_singleton_iff.mp hv).symm)).elim⟩
    · exact Or.inr ⟨singleton_subset_iff.mpr hx₂, hK.2.1, fun u hu v hv huv =>
        (huv ((mem_singleton_iff.mp hu).trans (mem_singleton_iff.mp hv).symm)).elim⟩
  · have hl_xy : C.IsLink s(x, y) x y := hK.2.2 x (Or.inl rfl) y (Or.inr rfl) hxy
    have hl_union : (subgraphUnion C C₁ C₂).IsLink s(x, y) x y := hC_union.symm ▸ hl_xy
    rcases (subgraphUnion_isLink hC₁ hC₂).mp hl_union with hl₁ | hl₂
    · left; refine ⟨by rintro u (rfl | rfl); exacts [hl₁.left_mem, hl₁.right_mem], hK.2.1, ?_⟩
      rintro u (rfl | rfl) v (rfl | rfl) huv
      exacts [(huv rfl).elim, hl₁, Sym2.eq_swap ▸ hl₁.symm, (huv rfl).elim]
    · right; refine ⟨by rintro u (rfl | rfl); exacts [hl₂.left_mem, hl₂.right_mem], hK.2.1, ?_⟩
      rintro u (rfl | rfl) v (rfl | rfl) huv
      exacts [(huv rfl).elim, hl₂, Sym2.eq_swap ▸ hl₂.symm, (huv rfl).elim]
  · have hl_xy : C.IsLink s(x, y) x y := hK.2.2 x (by simp) y (by simp) hxy
    have hl_yz : C.IsLink s(y, z) y z := hK.2.2 y (by simp) z (by simp) hyz
    have hl_zx : C.IsLink s(z, x) z x := hK.2.2 z (by simp) x (by simp) hzx
    obtain ⟨T, hT_tri, hVT, hl_xy_T, hl_yz_T, hl_zx_T⟩ :=
      exists_triangle_of_three_clique hxy hyz hzx hl_xy hl_yz hl_zx
    rcases htri T hT_tri with hT₁ | hT₂
    · left; refine ⟨hVT ▸ hT₁.vertexSet_mono, hK.2.1, ?_⟩
      rintro u (rfl | rfl | rfl) v (rfl | rfl | rfl) huv
      exacts [(huv rfl).elim, hl_xy_T.mono hT₁, Sym2.eq_swap ▸ (hl_zx_T.mono hT₁).symm,
        Sym2.eq_swap ▸ (hl_xy_T.mono hT₁).symm, (huv rfl).elim, hl_yz_T.mono hT₁,
        hl_zx_T.mono hT₁, Sym2.eq_swap ▸ (hl_yz_T.mono hT₁).symm, (huv rfl).elim]
    · right; refine ⟨hVT ▸ hT₂.vertexSet_mono, hK.2.1, ?_⟩
      rintro u (rfl | rfl | rfl) v (rfl | rfl | rfl) huv
      exacts [(huv rfl).elim, hl_xy_T.mono hT₂, Sym2.eq_swap ▸ (hl_zx_T.mono hT₂).symm,
        Sym2.eq_swap ▸ (hl_xy_T.mono hT₂).symm, (huv rfl).elim, hl_yz_T.mono hT₂,
        hl_zx_T.mono hT₂, Sym2.eq_swap ▸ (hl_yz_T.mono hT₂).symm, (huv rfl).elim]

/-- **Graph Minors IX, (11.11), Claim (2)** (page 75):
"$(A_0, B_0)$ is a separation of $(G, \Omega)$, and $V(A_0 \cap B_0) = \bar{\Omega}_0$, and
$V(B_0 \cap C) = V(C_2)$." -/
theorem lemma_11_11_claim_2 {S : Society α β} {D_set D₁ D₂ : Set (Graph α β × Graph α β)}
    (hD : IsConsolidation S D_set) {C₁ C₂ : Graph α (Sym2 α)} {Ω₀ : CyclicPerm α}
    (hC₁ : C₁ ≤ consolidationCore S D_set) (hC₂ : C₂ ≤ consolidationCore S D_set)
    (hC_union : subgraphUnion (consolidationCore S D_set) C₁ C₂ = consolidationCore S D_set)
    (hΩ : S.Ω.bar ⊆ V(C₂)) (hΩ₀ : V(C₁) ∩ V(C₂) = Ω₀.bar)
    (hD_union : D₁ ∪ D₂ = D_set) (hD_disj : Disjoint D₁ D₂)
    (hD₁ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ → V(A) ∩ V(B) ⊆ V(C₁))
    (hD₂ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₂ → V(A) ∩ V(B) ⊆ V(C₂)) :
    let C := consolidationCore S D_set
    let C_star : Graph α β := (S.G.induce (V(C₁) ∩ V(C₂))).restrict ∅
    let A₀ : Graph α β := subgraphUnion S.G C_star (subgraphSUnion S.G (Prod.fst '' D₁))
    let B₀ : Graph α β := subgraphUnion S.G C_star (subgraphSUnion S.G (Prod.fst '' D₂))
    S.IsSocietySeparation A₀ B₀ ∧ V(subgraphInter S.G A₀ B₀) = Ω₀.bar ∧
      V(A₀) ∩ V(C) = V(C₁) ∧ V(B₀) ∩ V(C) = V(C₂) := by
  intro C C_star A₀ B₀
  obtain ⟨hsep, hinter, hA₀C, hB₀C⟩ :=
    theorem_11_8_proof hD hC₁ hC₂ hC_union hΩ hD_union hD_disj hD₁ hD₂
  refine ⟨hsep, ?_, hA₀C, hB₀C⟩
  rw [hinter]; exact hΩ₀

/-- **Graph Minors IX, (11.11), Claim (3)** (pages 75–76):
"`D'₁` is a consolidation of `(A₀, Ω₀)`." -/
theorem lemma_11_11_claim_3 {S : Society α β} {D_set D₁ D₂ : Set (Graph α β × Graph α β)}
    (hD : IsConsolidation S D_set) {C₁ C₂ : Graph α (Sym2 α)} {Ω₀ : CyclicPerm α}
    (hC₁ : C₁ ≤ consolidationCore S D_set) (hC₂ : C₂ ≤ consolidationCore S D_set)
    (hC_union : subgraphUnion (consolidationCore S D_set) C₁ C₂ = consolidationCore S D_set)
    (hΩ : S.Ω.bar ⊆ V(C₂)) (hΩ₀ : V(C₁) ∩ V(C₂) = Ω₀.bar)
    (hD_union : D₁ ∪ D₂ = D_set) (hD_disj : Disjoint D₁ D₂)
    (hD₁ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ → V(A) ∩ V(B) ⊆ V(C₁))
    (hD₂ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₂ → V(A) ∩ V(B) ⊆ V(C₂)) :
    let C_star : Graph α β := (S.G.induce (V(C₁) ∩ V(C₂))).restrict ∅
    let A₀ : Graph α β := subgraphUnion S.G C_star (subgraphSUnion S.G (Prod.fst '' D₁))
    have hA₀_le : A₀ ≤ S.G :=
      (lemma_11_11_claim_2 hD hC₁ hC₂ hC_union hΩ hΩ₀ hD_union hD_disj hD₁ hD₂).1.1.1
    let S₀ : Society α β := ⟨A₀, Ω₀, S.finite_V.subset hA₀_le.vertexSet_mono,
      S.finite_E.subset hA₀_le.edgeSet_mono, hΩ₀ ▸ subset_union_left⟩
    let D'₁ : Set (Graph α β × Graph α β) :=
      (fun p => (p.1, subgraphInter S.G A₀ p.2)) '' D₁ ∪
        (fun v => (singleVertexSubgraph A₀ v, A₀)) '' V(C_star)
    IsConsolidation S₀ D'₁ := by
  intro C_star A₀ hA₀_le S₀ D'₁
  have hD₁_sub : D₁ ⊆ D_set := hD_union ▸ subset_union_left
  have hC_star_le_G : C_star ≤ S.G := restrict_le.trans (S.G.induce_le
    (inter_subset_left.trans (hC₁.vertexSet_mono.trans (vertexSet_consolidationCore_subset S
      D_set))))
  have hU₁_all : ∀ P ∈ Prod.fst '' D₁, P ≤ S.G := fun P hP => hD.forall_fst_le P
    (image_mono hD₁_sub hP)
  have hU₁_le_G : subgraphSUnion S.G (Prod.fst '' D₁) ≤ S.G := subgraphSUnion_le hU₁_all
  have hC_star_le_A₀ : C_star ≤ A₀ := le_subgraphUnion_left hC_star_le_G hU₁_le_G
  have hU₁_le_A₀ : subgraphSUnion S.G (Prod.fst '' D₁) ≤ A₀ := le_subgraphUnion_right hC_star_le_G
    hU₁_le_G
  have hA_le_A₀ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ → A ≤ A₀ := fun A B hAB =>
    (le_subgraphSUnion hU₁_all ⟨(A, B), hAB, rfl⟩).trans hU₁_le_A₀
  have hC_star_sub_B : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D_set → V(C_star) ⊆ V(B) := fun A B hAB =>
    (inter_subset_left.trans hC₁.vertexSet_mono).trans (vertexSet_consolidationCore_subset_right
      hAB)
  have hsep_D₁ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ →
      S₀.IsSocietySeparation A (subgraphInter S.G A₀ B) := by
    intro A B hAB
    have hAB_D : (A, B) ∈ D_set := hD₁_sub hAB
    have hsep := (hD.isSocietySeparation hAB_D).1
    have hA_A₀ : A ≤ A₀ := hA_le_A₀ hAB
    have hB_le : B ≤ S.G := hD.right_le hAB_D
    have hB'_A₀ : subgraphInter S.G A₀ B ≤ A₀ := subgraphInter_le_left hA₀_le hB_le
    refine ⟨⟨hA_A₀, hB'_A₀, ?_, ?_, ?_⟩, ?_⟩
    · refine subset_antisymm (union_subset hA_A₀.vertexSet_mono hB'_A₀.vertexSet_mono) fun v hv
      => ?_
      have hvG : v ∈ V(A) ∪ V(B) := hsep.2.2.1 ▸ hA₀_le.vertexSet_mono hv
      rcases hvG with hvA | hvB
      · exact Or.inl hvA
      · exact Or.inr ⟨hv, hvB⟩
    · rw [edgeSet_subgraphInter hA₀_le hB_le]
      refine subset_antisymm (union_subset hA_A₀.edgeSet_mono inter_subset_left) fun e he => ?_
      have heG : e ∈ E(A) ∪ E(B) := hsep.2.2.2.1 ▸ hA₀_le.edgeSet_mono he
      rcases heG with heA | heB
      · exact Or.inl heA
      · exact Or.inr ⟨he, heB⟩
    · rw [edgeSet_subgraphInter hA₀_le hB_le]
      exact hsep.2.2.2.2.mono_right inter_subset_right
    · change Ω₀.bar ⊆ V(A₀) ∩ V(B)
      rw [← hΩ₀]; exact subset_inter subset_union_left (hC_star_sub_B hAB_D)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro X Y (⟨⟨A, B⟩, hAB, hpair⟩ | ⟨v, hv, hpair⟩) <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    · exact hsep_D₁ hAB
    · have hv_A₀ : v ∈ V(A₀) := Or.inl hv
      refine ⟨⟨singleVertexSubgraph_le hv_A₀, le_rfl, ?_, by simp [S₀], ?_⟩, S₀.bar_subset⟩
      · rw [vertexSet_singleVertexSubgraph, singleton_union, insert_eq_of_mem hv_A₀]
      · rw [edgeSet_singleVertexSubgraph]; exact empty_disjoint _
  · rintro X Y (⟨⟨A, B⟩, hAB, hpair⟩ | ⟨v, _, hpair⟩) <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    · have hV_eq : V(A) ∩ V(subgraphInter S.G A₀ B) = V(A) ∩ V(B) := by
        ext u; simp only [vertexSet_subgraphInter, mem_inter_iff]
        exact ⟨fun ⟨huA, _, huB⟩ => ⟨huA, huB⟩, fun ⟨huA, huB⟩ => ⟨huA,
          (hA_le_A₀ hAB).vertexSet_mono huA, huB⟩⟩
      rw [hV_eq]; exact hD.order_le_three (hD₁_sub hAB)
    · exact (ncard_le_ncard inter_subset_left (finite_singleton v)).trans (by simp)
  · rintro X₁ Y₁ X₂ Y₂ h1 h2 hne
    rcases h2 with ⟨⟨A₂, B₂⟩, hA₂B₂, hpair₂⟩ | ⟨v₂, _, hpair₂⟩ <;> obtain ⟨rfl, rfl⟩
      := Prod.mk.inj hpair₂
    · have hB'₂_le : subgraphInter S.G A₀ B₂ ≤ A₀ := subgraphInter_le_left hA₀_le (hD.right_le
      (hD₁_sub hA₂B₂))
      rcases h1 with ⟨⟨A₁, B₁⟩, hA₁B₁, hpair₁⟩ | ⟨v₁, hv₁, hpair₁⟩ <;> obtain ⟨rfl, rfl⟩
        := Prod.mk.inj hpair₁
      · have hne12 : (A₁, B₁) ≠ (A₂, B₂) := fun heq => hne (by rw [heq])
        have hA₁_B₂ : A₁ ≤ B₂ := hD.left_le_right (hD₁_sub hA₁B₁) (hD₁_sub hA₂B₂) hne12
        exact le_subgraphInter hA₀_le (hD.right_le (hD₁_sub hA₂B₂)) (hA_le_A₀ hA₁B₁) hA₁_B₂
      · have hv₁_A₀ : v₁ ∈ V(A₀) := Or.inl hv₁
        rw [(Compatible.of_le_le (singleVertexSubgraph_le hv₁_A₀) hB'₂_le).le_iff]
        refine ⟨singleton_subset_iff.mpr ⟨hv₁_A₀, hC_star_sub_B (hD₁_sub hA₂B₂) hv₁⟩, ?_⟩
        rw [edgeSet_singleVertexSubgraph]; exact empty_subset _
    · rcases h1 with ⟨⟨A₁, B₁⟩, hA₁B₁, hpair₁⟩ | ⟨v₁, hv₁, hpair₁⟩ <;> obtain ⟨rfl, rfl⟩
      := Prod.mk.inj hpair₁
      · exact hA_le_A₀ hA₁B₁
      · exact singleVertexSubgraph_le (Or.inl hv₁)
  · have hP' : ∀ P ∈ Prod.fst '' D'₁, P ≤ A₀ := by
      rintro P ⟨⟨X, Y⟩, ⟨⟨A, B⟩, hAB, hpair⟩ | ⟨v, hv, hpair⟩, rfl⟩ <;>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      · exact hA_le_A₀ hAB
      · exact singleVertexSubgraph_le (Or.inl hv)
    refine (Compatible.of_le_le (subgraphSUnion_le hP') le_rfl).ext
      (subset_antisymm (subgraphSUnion_le hP').vertexSet_mono fun v hv => ?_)
      (subset_antisymm (subgraphSUnion_le hP').edgeSet_mono fun e he => ?_)
    · rw [vertexSet_subgraphSUnion, mem_iUnion₂]
      rcases hv with hv_star | hv_U₁
      · exact ⟨singleVertexSubgraph A₀ v,
          ⟨(singleVertexSubgraph A₀ v, A₀), Or.inr ⟨v, hv_star, rfl⟩, rfl⟩, by simp⟩
      · obtain ⟨A, ⟨⟨A', B'⟩, hAB, rfl⟩, hvA⟩ := mem_iUnion₂.mp hv_U₁
        exact ⟨A', ⟨(A', subgraphInter S.G A₀ B'), Or.inl ⟨(A', B'), hAB, rfl⟩, rfl⟩, hvA⟩
    · rw [edgeSet_subgraphSUnion hP', mem_iUnion₂]
      have he' : e ∈ E(subgraphSUnion S.G (Prod.fst '' D₁)) := by
        have hE_A₀ : E(A₀) = E(C_star) ∪ E(subgraphSUnion S.G (Prod.fst '' D₁)) :=
          edgeSet_subgraphUnion hC_star_le_G hU₁_le_G
        have hE_star : E(C_star) = ∅ := by simp [C_star]
        rwa [hE_A₀, hE_star, empty_union] at he
      rw [edgeSet_subgraphSUnion hU₁_all, mem_iUnion₂] at he'
      obtain ⟨A, ⟨⟨A', B'⟩, hAB, rfl⟩, heA⟩ := he'
      exact ⟨A', ⟨(A', subgraphInter S.G A₀ B'), Or.inl ⟨(A', B'), hAB, rfl⟩, rfl⟩, heA⟩
  · rintro X Y (⟨⟨A, B⟩, hAB, hpair⟩ | ⟨v, _, hpair⟩) u hu w hw huw <;>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    · obtain ⟨P, hP, hdisj⟩ := hD.exists_path (hD₁_sub hAB) u ⟨hu.1, hu.2.2⟩ w ⟨hw.1, hw.2.2⟩ huw
      exact ⟨P, hP, hdisj.mono_right inter_subset_right⟩
    · exact (huw ((mem_singleton_iff.mp hu.1).trans (mem_singleton_iff.mp hw.1).symm)).elim

/-- **Graph Minors IX, (11.11), Claim (4)** (page 76):
"$(A_0, \Omega_0)$ has no transaction of cardinality $> 3p + 9$." -/
theorem lemma_11_11_claim_4 {S : Society α β} {D_set D₁ D₂ : Set (Graph α β × Graph α β)}
    (hD : IsConsolidation S D_set) {S₁ : Society α (Sym2 α)} {C₂ : Graph α (Sym2 α)}
    (hC₁ : S₁.G ≤ consolidationCore S D_set) (hC₂ : C₂ ≤ consolidationCore S D_set)
    (hC_union : subgraphUnion (consolidationCore S D_set) S₁.G C₂ = consolidationCore S D_set)
    (hΩ : S.Ω.bar ⊆ V(C₂)) (hΩ₀ : V(S₁.G) ∩ V(C₂) = S₁.Ω.bar)
    (hD_union : D₁ ∪ D₂ = D_set) (hD_disj : Disjoint D₁ D₂)
    (hD₁_clique : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ → IsLeThreeClique S₁.G (V(A) ∩ V(B)))
    (hD₂ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₂ → V(A) ∩ V(B) ⊆ V(C₂))
    {q : ℕ} (hno_large_C₁ : ∀ Q_set : Set (Graph α (Sym2 α)), S₁.IsTransaction Q_set → Q_set.ncard
      ≤ q) :
    let C_star : Graph α β := (S.G.induce (V(S₁.G) ∩ V(C₂))).restrict ∅
    let A₀ : Graph α β := subgraphUnion S.G C_star (subgraphSUnion S.G (Prod.fst '' D₁))
    have hA₀_le : A₀ ≤ S.G :=
      (lemma_11_11_claim_2 hD hC₁ hC₂ hC_union hΩ hΩ₀ hD_union hD_disj
        (fun _ _ h => (hD₁_clique h).1) hD₂).1.1.1
    let S₀ : Society α β := ⟨A₀, S₁.Ω, S.finite_V.subset hA₀_le.vertexSet_mono,
      S.finite_E.subset hA₀_le.edgeSet_mono, hΩ₀ ▸ subset_union_left⟩
    ∀ P_set : Set (Graph α β), S₀.IsTransaction P_set → P_set.ncard ≤ q := by
  intro C_star A₀ hA₀_le S₀ P_set hP_trans
  have hD₁ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ → V(A) ∩ V(B) ⊆ V(S₁.G) := fun _ _ h =>
    (hD₁_clique h).1
  let D'₁ : Set (Graph α β × Graph α β) :=
    (fun q => (q.1, subgraphInter S.G A₀ q.2)) '' D₁ ∪
      (fun v => (singleVertexSubgraph A₀ v, A₀)) '' V(C_star)
  have hD'₁ : IsConsolidation S₀ D'₁ :=
    lemma_11_11_claim_3 hD hC₁ hC₂ hC_union hΩ hΩ₀ hD_union hD_disj hD₁ hD₂
  let C' := consolidationCore S₀ D'₁
  have hC'_le_C₁ : C' ≤ S₁.G := by
    refine ⟨fun v hv => ?_, fun e x y hlink => ?_⟩
    · rcases hv.1 with hv_star | hv_U₁
      · exact hv_star.1
      · obtain ⟨A, ⟨⟨A', B'⟩, hAB, rfl⟩, hvA⟩ := mem_iUnion₂.mp hv_U₁
        have hvB' : v ∈ V(subgraphInter S.G A₀ B') :=
          mem_iInter₂.mp hv.2 (A', subgraphInter S.G A₀ B') (Or.inl ⟨(A', B'), hAB, rfl⟩)
        exact hD₁ hAB ⟨hvA, hvB'.2⟩
    · rcases hlink with ⟨hxy, rfl, _, _, ⟨X, Y⟩, hq, hxq, hyq⟩
      rcases hq with ⟨⟨A, B⟩, hAB, hpair⟩ | ⟨v, _, hpair⟩ <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      · exact (hD₁_clique hAB).2.2 x ⟨hxq.1, hxq.2.2⟩ y ⟨hyq.1, hyq.2.2⟩ hxy
      · exact (hxy ((mem_singleton_iff.mp hxq.1).trans (mem_singleton_iff.mp hyq.1).symm)).elim
  obtain ⟨Q_set, hQ_trans, hpat⟩ := (theorem_11_10_proof S₀ D'₁ hD'₁ (S₀.transactionPattern
    P_set)).mp
    ⟨P_set, hP_trans, rfl⟩
  have hQ_trans_S₁ : S₁.IsTransaction Q_set := by
    rcases hQ_trans with ⟨A_f, B_f, ⟨hQ_paths, hQ_disj⟩, hfence, hQ_ends⟩
    refine ⟨A_f, B_f, ⟨fun Q hQ => ?_, hQ_disj⟩, hfence, fun Q hQ => ?_⟩
    · obtain ⟨a, b, hQ_ab⟩ := hQ_paths Q hQ
      exact ⟨a, b, hQ_ab.1.mono hC'_le_C₁, hQ_ab.2⟩
    · obtain ⟨a, haA, b, hbB, hQ_ab⟩ := hQ_ends Q hQ
      exact ⟨a, haA, b, hbB, hQ_ab.1.mono hC'_le_C₁, hQ_ab.2⟩
  rw [← ncard_transactionPattern_eq hP_trans, ← hpat, ncard_transactionPattern_eq hQ_trans]
  exact hno_large_C₁ Q_set hQ_trans_S₁

/-- **Graph Minors IX, (11.11), Claim (5)** (pages 76–77):
"{(A_0, \Omega_0), (A_1, \Omega_1), \dots, (A_k, \Omega_k)\}$ is a segregation of $(G, \Omega)$." -/
theorem lemma_11_11_claim_5 {S : Society α β} {D_set D₁ D₂ : Set (Graph α β × Graph α β)}
    (hD : IsConsolidation S D_set) {C₁ C₂ : Graph α (Sym2 α)} {Ω₀ : CyclicPerm α}
    (hC₁ : C₁ ≤ consolidationCore S D_set) (hC₂ : C₂ ≤ consolidationCore S D_set)
    (hC_union : subgraphUnion (consolidationCore S D_set) C₁ C₂ = consolidationCore S D_set)
    (hΩ : S.Ω.bar ⊆ V(C₂)) (hΩ₀ : V(C₁) ∩ V(C₂) = Ω₀.bar)
    (hD_union : D₁ ∪ D₂ = D_set) (hD_disj : Disjoint D₁ D₂)
    (hD₁ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₁ → V(A) ∩ V(B) ⊆ V(C₁))
    (hD₂ : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D₂ → V(A) ∩ V(B) ⊆ V(C₂))
    {k : ℕ} {p_idx : Fin k → Graph α β × Graph α β} (hp_inj : Function.Injective p_idx)
    (hp_range : range p_idx = D₂) {S₀ : Society α β} {S_fam : Fin k → Society α β}
    (hS₀_G : S₀.G = subgraphUnion S.G ((S.G.induce (V(C₁) ∩ V(C₂))).restrict ∅)
      (subgraphSUnion S.G (Prod.fst '' D₁)))
    (hS₀_Ω : S₀.Ω = Ω₀)
    (hS_fam_G : ∀ i : Fin k, (S_fam i).G = (p_idx i).1)
    (hS_fam_bar : ∀ i : Fin k, (S_fam i).Ω.bar = V((p_idx i).1) ∩ V((p_idx i).2)) :
    IsSocietySegregation S S₀ S_fam := by
  let C_star : Graph α β := (S.G.induce (V(C₁) ∩ V(C₂))).restrict ∅
  let A₀ : Graph α β := subgraphUnion S.G C_star (subgraphSUnion S.G (Prod.fst '' D₁))
  let B₀ : Graph α β := subgraphUnion S.G C_star (subgraphSUnion S.G (Prod.fst '' D₂))
  have hD₁_sub : D₁ ⊆ D_set := hD_union ▸ subset_union_left
  have hD₂_sub : D₂ ⊆ D_set := hD_union ▸ subset_union_right
  have hp_mem_D₂ : ∀ i : Fin k, p_idx i ∈ D₂ := fun i => hp_range ▸ mem_range_self i
  have hp_mem_D : ∀ i : Fin k, p_idx i ∈ D_set := fun i => hD₂_sub (hp_mem_D₂ i)
  obtain ⟨hsep₀, _, _, _⟩ :=
    lemma_11_11_claim_2 hD hC₁ hC₂ hC_union hΩ hΩ₀ hD_union hD_disj hD₁ hD₂
  have hC_star_le_G : C_star ≤ S.G := restrict_le.trans (S.G.induce_le
    (inter_subset_left.trans (hC₁.vertexSet_mono.trans (vertexSet_consolidationCore_subset S
      D_set))))
  have hU₁_all : ∀ P ∈ Prod.fst '' D₁, P ≤ S.G := fun P hP => hD.forall_fst_le P
    (image_mono hD₁_sub hP)
  have hU₁_le_G : subgraphSUnion S.G (Prod.fst '' D₁) ≤ S.G := subgraphSUnion_le hU₁_all
  refine ⟨hS₀_G ▸ hsep₀.1.1, fun i => hS_fam_G i ▸ hD.left_le (hp_mem_D i), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · refine subset_antisymm (union_subset (hS₀_G ▸ hsep₀.1.1.vertexSet_mono)
      (iUnion_subset fun i => (hS_fam_G i ▸ hD.left_le (hp_mem_D i)).vertexSet_mono)) fun v hv => ?_
    obtain ⟨A, B, hAB, hvA⟩ := hD.exists_mem_of_mem_vertexSet hv
    rcases (hD_union ▸ hAB : (A, B) ∈ D₁ ∪ D₂) with h1 | h2
    · left; rw [hS₀_G]; exact Or.inr (mem_iUnion₂.mpr ⟨A, ⟨(A, B), h1, rfl⟩, hvA⟩)
    · right; rw [← hp_range] at h2; obtain ⟨i, hi⟩ := h2
      exact mem_iUnion.mpr ⟨i, by rw [hS_fam_G, hi]; exact hvA⟩
  · refine subset_antisymm (union_subset (hS₀_G ▸ hsep₀.1.1.edgeSet_mono)
      (iUnion_subset fun i => (hS_fam_G i ▸ hD.left_le (hp_mem_D i)).edgeSet_mono)) fun e he => ?_
    obtain ⟨A, B, hAB, heA⟩ := hD.exists_mem_of_mem_edgeSet he
    rcases (hD_union ▸ hAB : (A, B) ∈ D₁ ∪ D₂) with h1 | h2
    · left; rw [hS₀_G, edgeSet_subgraphUnion hC_star_le_G hU₁_le_G, edgeSet_subgraphSUnion hU₁_all]
      exact Or.inr (mem_iUnion₂.mpr ⟨A, ⟨(A, B), h1, rfl⟩, heA⟩)
    · right; rw [← hp_range] at h2; obtain ⟨i, hi⟩ := h2
      exact mem_iUnion.mpr ⟨i, by rw [hS_fam_G, hi]; exact heA⟩
  · intro i
    rw [hS₀_G, hS_fam_G, edgeSet_subgraphUnion hC_star_le_G hU₁_le_G,
      edgeSet_subgraphSUnion hU₁_all]
    have hE_star : E(C_star) = ∅ := by simp [C_star]
    rw [hE_star, empty_union, disjoint_iUnion₂_left]
    rintro A ⟨⟨A', B'⟩, h1, rfl⟩
    have hne : (A', B') ≠ p_idx i := fun heq => disjoint_left.mp hD_disj h1 (heq ▸ hp_mem_D₂ i)
    exact hD.disjoint_edges_of_ne (hD₁_sub h1) (hp_mem_D i) hne
  · intro i j hij
    rw [hS_fam_G i, hS_fam_G j]
    exact hD.disjoint_edges_of_ne (hp_mem_D i) (hp_mem_D j) fun heq => hij (hp_inj heq)
  · intro j v ⟨hv₀, hvj⟩
    rw [hS₀_G] at hv₀; rw [hS_fam_G j] at hvj; rw [hS₀_Ω, hS_fam_bar j, ← hΩ₀]
    have hj_D : (p_idx j) ∈ D_set := hp_mem_D j
    rcases hv₀ with hv_star | hv_U₁
    · exact ⟨hv_star, hvj,
        (inter_subset_left.trans hC₁.vertexSet_mono).trans
          (vertexSet_consolidationCore_subset_right hj_D) hv_star⟩
    · obtain ⟨A, ⟨⟨A', B'⟩, h1, rfl⟩, hvA'⟩ := mem_iUnion₂.mp hv_U₁
      have hne : (A', B') ≠ p_idx j := fun heq => disjoint_left.mp hD_disj h1 (heq ▸ hp_mem_D₂ j)
      have hvB' : v ∈ V(B') := (hD.left_le_right hj_D (hD₁_sub h1) hne.symm).vertexSet_mono hvj
      have hvBj : v ∈ V((p_idx j).2) := (hD.left_le_right (hD₁_sub h1) hj_D hne).vertexSet_mono hvA'
      exact ⟨⟨hD₁ h1 ⟨hvA', hvB'⟩, hD₂ (hp_mem_D₂ j) ⟨hvj, hvBj⟩⟩, hvj, hvBj⟩
  · intro i j hij v ⟨hvi, hvj⟩
    rw [hS_fam_G i] at hvi; rw [hS_fam_G j] at hvj; rw [hS_fam_bar i, hS_fam_bar j]
    have hne : p_idx i ≠ p_idx j := fun heq => hij (hp_inj heq)
    exact ⟨⟨hvi, (hD.left_le_right (hp_mem_D j) (hp_mem_D i) hne.symm).vertexSet_mono hvj⟩,
      ⟨hvj, (hD.left_le_right (hp_mem_D i) (hp_mem_D j) hne).vertexSet_mono hvi⟩⟩
  · intro v hvΩ
    have hvB₀ : v ∈ V(B₀) := hsep₀.2 hvΩ
    rcases hvB₀ with hv_star | hv_U₂
    · left; rw [hS₀_Ω, ← hΩ₀]; exact hv_star
    · right; obtain ⟨A, ⟨p, hp₂, rfl⟩, hvA⟩ := mem_iUnion₂.mp hv_U₂
      rw [← hp_range] at hp₂; obtain ⟨i, rfl⟩ := hp₂
      exact mem_iUnion.mpr ⟨i, by
        rw [hS_fam_bar i]; exact ⟨hvA, (hD.isSocietySeparation (hp_mem_D i)).2 hvΩ⟩⟩

end GraphMinor.GM09
