/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM14.Section8a
import LeanPool.GraphMinor.GM14.Section8Core
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2a
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section3c
import LeanPool.GraphMinor.GM09.Section4a
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM09.Section4c
import LeanPool.GraphMinor.GM09.Section5a
import LeanPool.GraphMinor.GM09.Section9
import LeanPool.GraphMinor.GM09.Section10b
import LeanPool.GraphMinor.GM09.Section10d
import LeanPool.GraphMinor.GM09.Section10e
import LeanPool.GraphMinor.GM09.Section10f
import LeanPool.GraphMinor.GM09.Section10g
import Mathlib.Data.Set.Card

/-!
# Graph Minors XIV, (8.3): Numerical Refinement of (8.2) for Crosses (`π = 2`)

This file proves `(8.3)` (`theorem_8_3`, pages 40–41) of N. Robertson and P. D. Seymour,
*Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser. B **65** (1995) 23–50:

- `Society.theorem_5_2_p2` and `Society.theorem_5_2_p2_without_no_internal`: refinement of
  Graph Minors IX, `(5.2)` for `p = 2` using `2` separating paths `Q₀, Q₁` instead of `p + 4 = 6`.
- `theorem_10_3_p2_step` and `theorem_10_3_p2`: refinement of Graph Minors IX, `(10.3)` for
  `p = 2` under breadth `≥ 2` and `4 ≤ X.ncard`.
- `exists_clean_paths_p2` and `theorem_10_4_p2`: refinement of Graph Minors IX, `(10.4)` for
  `p = 2` under breadth `≥ 3` and `4 ≤ X.ncard`.
- `theorem_8_3`: Graph Minors XIV, `(8.3)` (pages 40–41).
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
  GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

/-! ## 1. Refinement of GM09 (5.2) for `p = 2` with `2` Separating Paths -/

/-- A transaction of cardinality `2` has no overpass. -/
private theorem not_isOverpass_of_ncard_eq_two (S : Society α β)
    {P_set : Set (Graph α β)} (hfin : P_set.Finite) (hcard : P_set.ncard = 2) :
    ¬ ∃ P₁ ∈ P_set, S.IsOverpass P_set P₁ := by
  rintro ⟨P₁, hP₁_in, _, _, M₁, hM₁, M₂, hM₂, hM12, _, _⟩
  have hcard_diff : (P_set \ {P₁}).ncard = 1 := by
    have h := ncard_sdiff_singleton_add_one hP₁_in hfin
    omega
  have hsub : ({M₁, M₂} : Set (Graph α β)) ⊆ P_set \ {P₁} := by
    rintro M (rfl | rfl) <;> assumption
  have hle : ({M₁, M₂} : Set (Graph α β)).ncard ≤ (P_set \ {P₁}).ncard :=
    ncard_le_ncard hsub hfin.sdiff
  rw [ncard_pair hM12, hcard_diff] at hle
  omega

/-- Structure of a crooked transaction `P_set` of cardinality `2` when a separating `Ω`-path `Q`
with ends `a_Q, b_Q` is half-covered by `P_set`. -/
private theorem halfCovered_of_ncard_eq_two (S : Society α β)
    {P_set : Set (Graph α β)} (hcr : S.IsCrookedTransaction P_set) (hcard : P_set.ncard = 2)
    {Q : Graph α β} {a_Q b_Q : α}
    (hQ_ends : S.IsOmegaPathWithEnds Q a_Q b_Q)
    (hQ_sep : S.IsSeparatingOmegaPath Q)
    (hcov : S.IsHalfCovered P_set Q) :
    ∃ (P₁ P₂ : Graph α β) (s₁ t₁ s₂ t₂ c : α),
      P_set = {P₁, P₂} ∧ P₁ ≠ P₂ ∧
      S.OmegaPathsCross P₁ P₂ ∧
      Disjoint V(P₂) V(Q) ∧
      S.IsOmegaPathWithEnds P₁ s₁ t₁ ∧
      S.IsOmegaPathWithEnds P₂ s₂ t₂ ∧
      (s₁ = a_Q ∨ s₁ = b_Q) ∧
      IsGraphPathWithEnds S.G (subgraphInter S.G P₁ Q) s₁ c ∧
      S.transactionEnds P_set = {s₁, t₁, s₂, t₂} ∧
      ((t₁ ∈ S.Ω.interval a_Q b_Q ∧ s₂ ∈ S.Ω.interval a_Q b_Q ∧ t₂ ∈ S.Ω.interval a_Q b_Q) ∨
       (t₁ ∈ S.Ω.interval b_Q a_Q ∧ s₂ ∈ S.Ω.interval b_Q a_Q ∧ t₂ ∈ S.Ω.interval b_Q a_Q)) := by
  rcases hcov with ⟨P₁, hP₁_in, _, huniq, s₁, t₁, a', b', c, hP₁_ends, hQ_ends', rfl, _,
    hinter_path⟩
  obtain ⟨A, B, hfence⟩ := hcr.1
  have hfin : P_set.Finite := hfence.1.finite S
  have hcard_diff : (P_set \ {P₁}).ncard = 1 := by
    have h := ncard_sdiff_singleton_add_one hP₁_in hfin
    omega
  obtain ⟨P₂, hP₂_eq⟩ := ncard_eq_one.mp hcard_diff
  have hP₂_in_diff : P₂ ∈ P_set \ {P₁} := hP₂_eq ▸ mem_singleton P₂
  have hP₂_in : P₂ ∈ P_set := hP₂_in_diff.1
  have hP12 : P₁ ≠ P₂ := Ne.symm hP₂_in_diff.2
  have hP_set_eq : P_set = {P₁, P₂} := by
    ext R
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · intro hR
      by_cases hRP₁ : R = P₁
      · exact Or.inl hRP₁
      · have hR_diff : R ∈ P_set \ {P₁} := ⟨hR, hRP₁⟩
        rw [hP₂_eq, mem_singleton_iff] at hR_diff
        exact Or.inr hR_diff
    · rintro (rfl | rfl) <;> assumption
  have hcr_pair : S.IsCrookedTransaction {P₁, P₂} := hP_set_eq ▸ hcr
  have hcross : S.OmegaPathsCross P₁ P₂ :=
    Society.omegaPathsCross_of_isCrookedTransaction_pair S hP12 hcr_pair
  have hdisj_P₂Q : Disjoint V(P₂) V(Q) := by
    by_contra hnot
    rw [not_disjoint_iff_nonempty_inter] at hnot
    exact hP12 (huniq P₂ hP₂_in hnot).symm
  obtain ⟨s₂, _, t₂, _, hP₂_ends⟩ := hfence.2.2 P₂ hP₂_in
  have hs₁_ab : s₁ = a_Q ∨ s₁ = b_Q := by
    rcases hQ_ends.ends_eq S hQ_ends' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hW_eq : S.transactionEnds P_set = {s₁, t₁, s₂, t₂} := by
    rw [hP_set_eq]
    ext v
    simp only [Society.transactionEnds, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨R, rfl | rfl, u, hR_vu⟩
      · rcases hP₁_ends.ends_eq S hR_vu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · rcases hP₂_ends.ends_eq S hR_vu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨P₁, Or.inl rfl, t₁, hP₁_ends⟩
      · exact ⟨P₁, Or.inl rfl, s₁, hP₁_ends.symm S⟩
      · exact ⟨P₂, Or.inr rfl, t₂, hP₂_ends⟩
      · exact ⟨P₂, Or.inr rfl, s₂, hP₂_ends.symm S⟩
  -- Determine the interval containing `s₂, t₂, t₁`.
  have hs₂_ne_a : s₂ ≠ a_Q :=
    fun h => disjoint_left.mp hdisj_P₂Q hP₂_ends.1.left_mem (h ▸ hQ_ends.1.left_mem)
  have hs₂_ne_b : s₂ ≠ b_Q :=
    fun h => disjoint_left.mp hdisj_P₂Q hP₂_ends.1.left_mem (h ▸ hQ_ends.1.right_mem)
  have hcross_ends : S.Ω.Crosses s₁ t₁ s₂ t₂ := by
    rcases hcross with ⟨_, u₁, v₁, u₂, v₂, h₁', h₂', hcr'⟩
    have hcr1 : S.Ω.Crosses s₁ t₁ u₂ v₂ := by
      rcases hP₁_ends.ends_eq S h₁' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcr'
      · exact hcr'.swap_left
    rcases hP₂_ends.ends_eq S h₂' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcr1
    · exact hcr1.swap_right
  have haux_side : ∀ {x_Q y_Q : α},
      S.IsOmegaPathWithEnds Q x_Q y_Q →
      (s₁ = x_Q ∨ s₁ = y_Q) →
      s₂ ∈ S.Ω.interval x_Q y_Q →
      t₁ ∈ S.Ω.interval x_Q y_Q ∧ s₂ ∈ S.Ω.interval x_Q y_Q ∧ t₂ ∈ S.Ω.interval x_Q y_Q := by
    intro x_Q y_Q hQ_xy hs₁_xy hs₂_xy
    have ht₂_xy : t₂ ∈ S.Ω.interval x_Q y_Q :=
      S.both_ends_mem_interval_of_separating hQ_xy hQ_sep hP₂_ends hdisj_P₂Q hs₂_xy
    have hs₁_not_xy : s₁ ∉ S.Ω.interval x_Q y_Q := by
      rcases hs₁_xy with rfl | rfl
      · exact S.Ω.not_mem_interval_left s₁ y_Q
      · exact S.Ω.not_mem_interval_right x_Q s₁
    have ht₁_xy : t₁ ∈ S.Ω.interval x_Q y_Q := by
      rcases S.Ω.interval_subset_interval_or_swap hs₂_xy ht₂_xy hP₂_ends.2.1 with hsub | hsub
      · rcases S.Ω.crosses_iff_interval.mp hcross_ends.symm with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact (hs₁_not_xy (hsub h1)).elim
        · exact hsub h1
      · rcases S.Ω.crosses_iff_interval.mp hcross_ends.symm with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact hsub h2
        · exact (hs₁_not_xy (hsub h2)).elim
    exact ⟨ht₁_xy, hs₂_xy, ht₂_xy⟩
  refine ⟨P₁, P₂, s₁, t₁, s₂, t₂, c, hP_set_eq, hP12, hcross, hdisj_P₂Q,
    hP₁_ends, hP₂_ends, hs₁_ab, hinter_path, hW_eq, ?_⟩
  rcases S.Ω.mem_interval_or_interval_swap hQ_ends.2.2.1 hQ_ends.2.2.2 hP₂_ends.2.2.1
      hQ_ends.2.1 hs₂_ne_a hs₂_ne_b with hs₂_ab | hs₂_ba
  · exact Or.inl (haux_side hQ_ends hs₁_ab hs₂_ab)
  · exact Or.inr (haux_side (hQ_ends.symm S) hs₁_ab.symm hs₂_ba)

/-- If `Q_m` is an `Ω`-path with `Q_m ≤ G₁` where `V(G₁) ∩ V(G₂) = V(Q_m)`, and `P₁` is an
`Ω`-path with ends `s₁, t₁ ∈ V(G₁)` such that `subgraphInter S.G P₁ Q_m` is a path with ends
`s₁, c`, then `P₁ ≤ G₁`. -/
private theorem halfCovered_le_left_of_separation (S : Society α β)
    {Q_m P₁ G₁ G₂ : Graph α β} {s₁ t₁ c : α}
    (hQm_le_G : Q_m ≤ S.G)
    (hQm_le_G₁ : Q_m ≤ G₁)
    (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q_m))
    (hP₁_ends : S.IsOmegaPathWithEnds P₁ s₁ t₁)
    (ht₁_G₁ : t₁ ∈ V(G₁))
    (hinter_path : IsGraphPathWithEnds S.G (subgraphInter S.G P₁ Q_m) s₁ c) :
    P₁ ≤ G₁ := by
  have hP₁_le : P₁ ≤ S.G := hP₁_ends.1.le
  have hc_inter : c ∈ V(subgraphInter S.G P₁ Q_m) := hinter_path.right_mem
  rw [vertexSet_subgraphInter] at hc_inter
  obtain ⟨R₁, R₂, hR₁_P₁, hR₂_P₁, hR₁, hR₂, hP₁_union, hinter_R₁R₂, _⟩ :=
    hP₁_ends.1.exists_split_at hc_inter.1
  have hinter_sub_P₁ : IsGraphPathWithEnds P₁ (subgraphInter S.G P₁ Q_m) s₁ c :=
    hinter_path.of_le (subgraphInter_le_left hP₁_le hQm_le_G)
  have hR₁_eq : R₁ = subgraphInter S.G P₁ Q_m :=
    hP₁_ends.1.subpath_unique_of_left hR₁ hinter_sub_P₁
  have hR₁_le_G₁ : R₁ ≤ G₁ := by
    rw [hR₁_eq]
    exact (subgraphInter_le_right hP₁_le hQm_le_G).trans hQm_le_G₁
  have hVR₂_inter : V(R₂) ∩ (V(G₂) ∩ V(G₁)) ⊆ {c} := by
    rw [inter_comm V(G₂), hinter_G]
    intro z ⟨hzR₂, hzQm⟩
    have hzR₁ : z ∈ V(R₁) := by
      rw [hR₁_eq, vertexSet_subgraphInter]
      exact ⟨hR₂_P₁.vertexSet_mono hzR₂, hzQm⟩
    have hz_both : z ∈ V(R₁) ∩ V(R₂) := ⟨hzR₁, hzR₂⟩
    rwa [hinter_R₁R₂] at hz_both
  have hc_G₁ : c ∈ V(G₁) := hQm_le_G₁.vertexSet_mono hc_inter.2
  have hR₂_le_G₁ : R₂ ≤ G₁ :=
    ((hR₂.mono hP₁_le).symm).le_right_of_inter_subset (IsGraphSeparation.symm hsep_G)
      hVR₂_inter ht₁_G₁ hc_G₁
  refine (Compatible.of_le_le hP₁_le hsep_G.1).le_iff.mpr ⟨?_, ?_⟩
  · intro v hv
    have hv' : v ∈ V(R₁) ∪ V(R₂) := by
      rw [← vertexSet_subgraphUnion, hP₁_union]
      exact hv
    rcases hv' with hv₁ | hv₂
    · exact hR₁_le_G₁.vertexSet_mono hv₁
    · exact hR₂_le_G₁.vertexSet_mono hv₂
  · intro e he
    have he' : e ∈ E(R₁) ∪ E(R₂) := by
      rw [← edgeSet_subgraphUnion hR₁_P₁ hR₂_P₁, hP₁_union]
      exact he
    rcases he' with he₁ | he₂
    · exact hR₁_le_G₁.edgeSet_mono he₁
    · exact hR₂_le_G₁.edgeSet_mono he₂

/-- Refinement of Graph Minors IX, `(5.2)` for `p = 2` with `2` separating paths `Q 0, Q 1`. -/
theorem theorem_5_2_p2 (S : Society α β) [Finite V(S.G)] [Finite E(S.G)]
    (hex_cr : ∃ P₀ : Set (Graph α β), S.IsCrookedTransaction P₀ ∧ 2 ≤ P₀.ncard)
    {Q : Fin 2 → Graph α β} {a b : Fin 2 → α}
    (hinj_Q : Function.Injective Q)
    (htr_Q : S.IsTransaction (range Q))
    (hsep_Q : ∀ i : Fin 2, S.IsSeparatingOmegaPath (Q i))
    (hno_int : ∀ i : Fin 2, Disjoint (pathInternalVerts S.G (Q i)) S.Ω.bar)
    (hends_Q : ∀ i : Fin 2, S.IsOmegaPathWithEnds (Q i) (a i) (b i))
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b))
    {G₁ G₂ : Graph α β} (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q 1))
    (hQ1_le : Q 1 ≤ G₁)
    (hint_G₁ : S.Ω.interval (a 1) (b 1) ⊆ V(G₁))
    (_hint_G₂ : S.Ω.interval (b 1) (a 1) ⊆ V(G₂)) :
    (∃ P₁ P₂ : Graph α β, S.OmegaPathsCross P₁ P₂ ∧ P₁ ≤ G₁ ∧ P₂ ≤ G₁) ∨
    (∃ P_set : Set (Graph α β), S.IsCrookedTransaction P_set ∧ P_set.ncard = 2 ∧
      Disjoint (S.Ω.interval (a 0) (b 0)) (S.transactionEnds P_set)) := by
  let Q_set : Set (Graph α β) := range Q
  have hno_int_Q : ∀ R ∈ Q_set, Disjoint (pathInternalVerts S.G R) S.Ω.bar := by
    rintro _ ⟨i, rfl⟩
    exact hno_int i
  obtain ⟨P_set, A, B, hS⟩ := S.exists_statementS (by decide : 2 ≤ 2) htr_Q hno_int_Q hex_cr
  have hcard_P : P_set.ncard = 2 := hS.card_P_eq S (by decide : (2 : ℕ) ≠ 3)
  by_cases hdisj_0 :
      Disjoint (S.Ω.interval (a 0) (b 0)) (S.transactionEnds P_set)
  · exact Or.inr ⟨P_set, hS.isCrooked_P, hcard_P, hdisj_0⟩
  · left
    have hint_01 := S.Ω.mem_intervals_of_isClockwiseSeq_ofFn hcw (by decide : (0 : Fin 2) < 1)
    have ha0_1 : a 0 ∈ S.Ω.interval (a 1) (b 1) := hint_01.1
    have hb0_1 : b 0 ∈ S.Ω.interval (a 1) (b 1) := hint_01.2.1
    have hsub_01 : S.Ω.interval (a 0) (b 0) ⊆ S.Ω.interval (a 1) (b 1) := hint_01.2.2.1
    have ha1_0 : a 1 ∈ S.Ω.interval (b 0) (a 0) := hint_01.2.2.2.1
    have hb1_0 : b 1 ∈ S.Ω.interval (b 0) (a 0) := hint_01.2.2.2.2
    -- Helper to deduce `P ≤ G₁` when `P` is an `Ω`-path disjoint from `Q j` with ends in `Ω(a j, b
    -- j)`.
    have hle_G₁_of_ends : ∀ (j : Fin 2) {P : Graph α β} {s t : α},
        S.IsOmegaPathWithEnds P s t →
        Disjoint V(P) V(Q j) →
        s ∈ S.Ω.interval (a j) (b j) →
        t ∈ S.Ω.interval (a j) (b j) →
        P ≤ G₁ := by
      intro j P s t hP_ends hdisj_PQj hs_j ht_j
      have hsub_j1 : S.Ω.interval (a j) (b j) ⊆ S.Ω.interval (a 1) (b 1) := by
        fin_cases j
        · exact hsub_01
        · exact Subset.rfl
      have hj_last : Q j = Q 1 ∨
          (Disjoint V(Q j) V(Q 1) ∧
            a 1 ∈ S.Ω.interval (b j) (a j) ∧ b 1 ∈ S.Ω.interval (b j) (a j)) := by
        fin_cases j
        · right
          obtain ⟨_, _, hfence_Q⟩ := htr_Q
          have hne_Q : Q 0 ≠ Q 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (hinj_Q h)
          exact ⟨hfence_Q.1.2 (mem_range_self 0) (mem_range_self 1) hne_Q, ha1_0, hb1_0⟩
        · exact Or.inl rfl
      have hdisj_G₂ : Disjoint V(P) V(G₂) :=
        S.disjoint_right_of_ends_in_interval_of_separating
          (hends_Q j) (hsep_Q j) (hends_Q 1) (hno_int 1)
          hsub_j1 hj_last hsep_G hinter_G hint_G₁ hP_ends hdisj_PQj hs_j ht_j
      exact IsGraphSeparation.le_left_of_disjoint hsep_G hP_ends.1.le hdisj_G₂
    by_cases hex_disj : ∃ j : Fin 2, Disjoint V(Q j) V(S.transactionUnion P_set)
    · rcases hex_disj with ⟨j, hdisj_Qj⟩
      have hsub_0j : S.Ω.interval (a 0) (b 0) ⊆ S.Ω.interval (a j) (b j) := by
        fin_cases j
        · exact Subset.rfl
        · exact hsub_01
      have hne_j : (S.transactionEnds P_set ∩ S.Ω.interval (a j) (b j)).Nonempty := by
        rw [not_disjoint_iff_nonempty_inter] at hdisj_0
        rcases hdisj_0 with ⟨x, hx0, hxP⟩
        exact ⟨x, hxP, hsub_0j hx0⟩
      obtain ⟨P₁, hP₁_in, P₂, hP₂_in, hcr_12, hends₁_j, hends₂_j⟩ :=
        S.theorem_5_1_proof (hends_Q j) (hsep_Q j) hS.isCrooked_P hdisj_Qj hne_j
      have hP_le_G₁ : ∀ P ∈ P_set, pathEnds S.G P ⊆ S.Ω.interval (a j) (b j) → P ≤ G₁ := by
        intro P hP_in hends_P
        obtain ⟨s, t, hP_ends⟩ := hS.isFenceFor_P.1.1 P hP_in
        have hs_j : s ∈ S.Ω.interval (a j) (b j) :=
          hends_P (by rw [hP_ends.1.pathEnds_eq]; exact Or.inl rfl)
        have ht_j : t ∈ S.Ω.interval (a j) (b j) :=
          hends_P (by rw [hP_ends.1.pathEnds_eq]; exact Or.inr rfl)
        have hdisj_PQj : Disjoint V(P) V(Q j) := by
          rw [disjoint_left]
          intro z hzP hzQj
          exact disjoint_left.mp hdisj_Qj hzQj (mem_iUnion₂.mpr ⟨P, hP_in, hzP⟩)
        exact hle_G₁_of_ends j hP_ends hdisj_PQj hs_j ht_j
      exact ⟨P₁, P₂, hcr_12, hP_le_G₁ P₁ hP₁_in hends₁_j, hP_le_G₁ P₂ hP₂_in hends₂_j⟩
    · push Not at hex_disj
      have hfin_P : P_set.Finite := hS.isFenceFor_P.1.finite S
      have hno_over : ¬ ∃ P₁ ∈ P_set, S.IsOverpass P_set P₁ :=
        not_isOverpass_of_ncard_eq_two S hfin_P hcard_P
      have h43 : ∀ j : Fin 2,
          pathEnds S.G (Q j) ⊆ S.transactionEnds P_set ∨ S.IsHalfCovered P_set (Q j) := by
        intro j
        by_contra hnot
        push Not at hnot
        exact hno_over ((S.theorem_4_3_proof hS).2 (Q j) (mem_range_self j)
          (by rintro (hd | hb | hc); exacts [hex_disj j hd, hnot.1 hb, hnot.2 hc]))
      rw [not_disjoint_iff_nonempty_inter] at hdisj_0
      rcases hdisj_0 with ⟨x₀, hx₀_ab, hx₀_W⟩
      -- At least one of `a 1, b 1` is in `S.transactionEnds P_set`, hence in `Ω(b 0, a 0)`.
      have hex_w₁ : ∃ w₁ ∈ S.Ω.interval (b 0) (a 0), w₁ ∈ S.transactionEnds P_set := by
        rcases h43 1 with hboth₁ | hcov₁
        · refine ⟨a 1, ha1_0, hboth₁ ?_⟩
          rw [(hends_Q 1).1.pathEnds_eq]
          exact Or.inl rfl
        · rcases hcov₁ with ⟨P, hP_in, _, _, s, t, a', b', _, hP_ends, hQ₁_ends', rfl, _, _⟩
          have hs_W : s ∈ S.transactionEnds P_set := hP_ends.mem_transactionEnds_left S hP_in
          rcases (hends_Q 1).ends_eq S hQ₁_ends' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨a 1, ha1_0, hs_W⟩
          · exact ⟨b 1, hb1_0, hs_W⟩
      rcases hex_w₁ with ⟨w₁, hw₁_ba, hw₁_W⟩
      -- `Q 0` cannot be half-covered, because `S.transactionEnds P_set` meets both `Ω(a 0, b 0)`
      -- and `Ω(b 0, a 0)`.
      have hnot_cov₀ : ¬ S.IsHalfCovered P_set (Q 0) := by
        intro hcov₀
        obtain ⟨P₁, P₂, s₁, t₁, s₂, t₂, _, _, _, _, _, _, _, hs₁_0, _, hW_eq, hside⟩ :=
          halfCovered_of_ncard_eq_two S hS.isCrooked_P hcard_P (hends_Q 0) (hsep_Q 0) hcov₀
        rcases hside with ⟨ht₁, hs₂, ht₂⟩ | ⟨ht₁, hs₂, ht₂⟩
        · have hw₁_in : w₁ ∈ ({s₁, t₁, s₂, t₂} : Set α) := hW_eq ▸ hw₁_W
          have hw₁_ab : w₁ ∈ S.Ω.interval (a 0) (b 0) := by
            rcases hw₁_in with rfl | rfl | rfl | rfl
            · rcases hs₁_0 with rfl | rfl
              · exact (S.Ω.not_mem_interval_right (b 0) (a 0) hw₁_ba).elim
              · exact (S.Ω.not_mem_interval_left (b 0) (a 0) hw₁_ba).elim
            · exact ht₁
            · exact hs₂
            · exact ht₂
          exact disjoint_left.mp (S.Ω.disjoint_interval_swap (a 0) (b 0)) hw₁_ab hw₁_ba
        · have hx₀_in : x₀ ∈ ({s₁, t₁, s₂, t₂} : Set α) := hW_eq ▸ hx₀_W
          have hx₀_ba : x₀ ∈ S.Ω.interval (b 0) (a 0) := by
            rcases hx₀_in with rfl | rfl | rfl | rfl
            · rcases hs₁_0 with rfl | rfl
              · exact (S.Ω.not_mem_interval_left (a 0) (b 0) hx₀_ab).elim
              · exact (S.Ω.not_mem_interval_right (a 0) (b 0) hx₀_ab).elim
            · exact ht₁
            · exact hs₂
            · exact ht₂
          exact disjoint_left.mp (S.Ω.disjoint_interval_swap (a 0) (b 0)) hx₀_ab hx₀_ba
      have hboth₀ : pathEnds S.G (Q 0) ⊆ S.transactionEnds P_set :=
        (h43 0).resolve_right hnot_cov₀
      have ha0_W : a 0 ∈ S.transactionEnds P_set :=
        hboth₀ (by rw [(hends_Q 0).1.pathEnds_eq]; exact Or.inl rfl)
      have hb0_W : b 0 ∈ S.transactionEnds P_set :=
        hboth₀ (by rw [(hends_Q 0).1.pathEnds_eq]; exact Or.inr rfl)
      -- `Q 1` cannot have both ends in `S.transactionEnds P_set`, so `Q 1` is half-covered.
      have hcov₁ : S.IsHalfCovered P_set (Q 1) := by
        refine (h43 1).resolve_left fun hboth₁ => ?_
        have ha1_W : a 1 ∈ S.transactionEnds P_set :=
          hboth₁ (by rw [(hends_Q 1).1.pathEnds_eq]; exact Or.inl rfl)
        have hb1_W : b 1 ∈ S.transactionEnds P_set :=
          hboth₁ (by rw [(hends_Q 1).1.pathEnds_eq]; exact Or.inr rfl)
        obtain ⟨_, hinj_a, hinj_b, hab_ne, _, _⟩ := CyclicPerm.isClockwise3_of_ofFn hcw
        have ha0_ne_a1 : a 0 ≠ a 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (hinj_a h)
        have hb0_ne_b1 : b 0 ≠ b 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (hinj_b h)
        have hx₀_ne_a0 : x₀ ≠ a 0 := fun h => S.Ω.not_mem_interval_left (a 0) (b 0) (h ▸ hx₀_ab)
        have hx₀_ne_b0 : x₀ ≠ b 0 := fun h => S.Ω.not_mem_interval_right (a 0) (b 0) (h ▸ hx₀_ab)
        have hx₀_ne_a1 : x₀ ≠ a 1 :=
          fun h => disjoint_left.mp (S.Ω.disjoint_interval_swap (a 0) (b 0)) hx₀_ab (h ▸ ha1_0)
        have hx₀_ne_b1 : x₀ ≠ b 1 :=
          fun h => disjoint_left.mp (S.Ω.disjoint_interval_swap (a 0) (b 0)) hx₀_ab (h ▸ hb1_0)
        let Z : Set α := {x₀, a 0, b 0, a 1, b 1}
        have hZ_sub : Z ⊆ S.transactionEnds P_set := by
          rintro z (rfl | rfl | rfl | rfl | rfl) <;> assumption
        have hfin_W : (S.transactionEnds P_set).Finite :=
          S.Ω.finite_bar.subset (S.transactionEnds_subset_bar P_set)
        have hZ_le : Z.ncard ≤ (S.transactionEnds P_set).ncard :=
          ncard_le_ncard hZ_sub hfin_W
        have hW_card : (S.transactionEnds P_set).ncard = 4 := by
          rw [(hS.isFenceFor_P.ncard_transactionEnds S).2.2, hcard_P]
        have hx₀_not : x₀ ∉ ({a 0, b 0, a 1, b 1} : Set α) := by
          simp [hx₀_ne_a0, hx₀_ne_b0, hx₀_ne_a1, hx₀_ne_b1]
        have ha0_not : a 0 ∉ ({b 0, a 1, b 1} : Set α) := by
          simp [hab_ne 0 0, ha0_ne_a1, hab_ne 0 1]
        have hb0_not : b 0 ∉ ({a 1, b 1} : Set α) := by
          simp [(hab_ne 1 0).symm, hb0_ne_b1]
        have hZ_card : Z.ncard = 5 := by
          dsimp [Z]
          rw [ncard_insert_of_notMem hx₀_not (by simp),
            ncard_insert_of_notMem ha0_not (by simp),
            ncard_insert_of_notMem hb0_not (by simp),
            ncard_pair (hab_ne 1 1)]
        omega
      obtain ⟨P₁, P₂, s₁, t₁, s₂, t₂, c, _, _, hcross, hdisj_P₂Q₁,
        hP₁_ends, hP₂_ends, hs₁_1, hinter_path, hW_eq, hside⟩ :=
        halfCovered_of_ncard_eq_two S hS.isCrooked_P hcard_P (hends_Q 1) (hsep_Q 1) hcov₁
      have hx₀_a1b1 : x₀ ∈ S.Ω.interval (a 1) (b 1) := hsub_01 hx₀_ab
      have hside_ab :
          t₁ ∈ S.Ω.interval (a 1) (b 1) ∧
          s₂ ∈ S.Ω.interval (a 1) (b 1) ∧
          t₂ ∈ S.Ω.interval (a 1) (b 1) := by
        refine hside.resolve_right fun ⟨ht₁_ba, hs₂_ba, ht₂_ba⟩ => ?_
        have hx₀_in : x₀ ∈ ({s₁, t₁, s₂, t₂} : Set α) := hW_eq ▸ hx₀_W
        have hx₀_ba : x₀ ∈ S.Ω.interval (b 1) (a 1) := by
          rcases hx₀_in with rfl | rfl | rfl | rfl
          · rcases hs₁_1 with rfl | rfl
            · exact (S.Ω.not_mem_interval_left (a 1) (b 1) hx₀_a1b1).elim
            · exact (S.Ω.not_mem_interval_right (a 1) (b 1) hx₀_a1b1).elim
          · exact ht₁_ba
          · exact hs₂_ba
          · exact ht₂_ba
        exact disjoint_left.mp (S.Ω.disjoint_interval_swap (a 1) (b 1)) hx₀_a1b1 hx₀_ba
      have hP₂_le_G₁ : P₂ ≤ G₁ :=
        hle_G₁_of_ends 1 hP₂_ends hdisj_P₂Q₁ hside_ab.2.1 hside_ab.2.2
      have hP₁_le_G₁ : P₁ ≤ G₁ :=
        halfCovered_le_left_of_separation S (hends_Q 1).1.le hQ1_le hsep_G hinter_G
          hP₁_ends (hint_G₁ hside_ab.1) hinter_path
      exact ⟨P₁, P₂, hcross, hP₁_le_G₁, hP₂_le_G₁⟩

/-- `theorem_5_2_p2` without `hno_int`, deduced by applying `theorem_5_2_p2` to `Society.spiked S`.
-/
theorem theorem_5_2_p2_without_no_internal (S : Society α β)
    (hex_cr : ∃ P₀ : Set (Graph α β), S.IsCrookedTransaction P₀ ∧ 2 ≤ P₀.ncard)
    {Q : Fin 2 → Graph α β} {a b : Fin 2 → α}
    (hinj_Q : Function.Injective Q)
    (htr_Q : S.IsTransaction (range Q))
    (hsep_Q : ∀ i : Fin 2, S.IsSeparatingOmegaPath (Q i))
    (hends_Q : ∀ i : Fin 2, S.IsOmegaPathWithEnds (Q i) (a i) (b i))
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b))
    {G₁ G₂ : Graph α β} (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q 1))
    (hQ1_le : Q 1 ≤ G₁)
    (hint_G₁ : S.Ω.interval (a 1) (b 1) ⊆ V(G₁))
    (hint_G₂ : S.Ω.interval (b 1) (a 1) ⊆ V(G₂)) :
    (∃ P₁ P₂ : Graph α β, S.OmegaPathsCross P₁ P₂ ∧ P₁ ≤ G₁ ∧ P₂ ≤ G₁) ∨
    (∃ P_set : Set (Graph α β), S.IsCrookedTransaction P_set ∧ P_set.ncard = 2 ∧
      Disjoint (S.Ω.interval (a 0) (b 0)) (S.transactionEnds P_set)) := by
  let S' := Society.spiked S
  have : Finite V(S'.G) := S'.finite_V
  have : Finite E(S'.G) := S'.finite_E
  let m : Fin 2 := 1
  let Q' : Fin 2 → Graph (α ⊕ α) (β ⊕ α) := fun i => spikeOmegaPath S (Q i)
  let a' : Fin 2 → α ⊕ α := inrV ∘ a
  let b' : Fin 2 → α ⊕ α := inrV ∘ b
  let G₁' := spikeGraph G₁ ({a m, b m} ∪ S.Ω.interval (a m) (b m))
  let G₂' := spikeGraphWithVerts G₂ (S.Ω.interval (b m) (a m)) {a m, b m}
  obtain ⟨hex_cr', hinj_Q', htr_Q', hsep_Q', hno_int', hends_Q', hcw', hsep_G', hinter_G',
    hint_G₁', hint_G₂', hQ'_le⟩ :=
    S.spikeTransactionAndSeparation m hex_cr hinj_Q htr_Q hsep_Q hends_Q hcw
      hsep_G hinter_G hint_G₁ hint_G₂
  rcases theorem_5_2_p2 S' hex_cr' hinj_Q' htr_Q' hsep_Q' hno_int' hends_Q' hcw'
      hsep_G' hinter_G' (hQ'_le hQ1_le) hint_G₁' hint_G₂' with
    ⟨K₁, K₂, ⟨hdisj_K12, s₁', t₁', s₂', t₂', hK₁_ends, hK₂_ends, hcr_K12⟩, hK₁_le, hK₂_le⟩ |
    ⟨P_set', hcr_P', hcard_P', hdisj_P'⟩
  · left
    rcases hK₁_ends.2.2.1 with ⟨s₁, _, rfl⟩
    rcases hK₁_ends.2.2.2 with ⟨t₁, _, rfl⟩
    rcases hK₂_ends.2.2.1 with ⟨s₂, _, rfl⟩
    rcases hK₂_ends.2.2.2 with ⟨t₂, _, rfl⟩
    obtain ⟨hP₁_ends, hVK₁⟩ := isOmegaPathWithEnds_unspikeGraph S hK₁_ends
    obtain ⟨hP₂_ends, hVK₂⟩ := isOmegaPathWithEnds_unspikeGraph S hK₂_ends
    have hunspike_le : ∀ {K : Graph (α ⊕ α) (β ⊕ α)} {s t : α},
        S.IsOmegaPathWithEnds (unspikeGraph S.G K) s t → K ≤ G₁' → unspikeGraph S.G K ≤ G₁ := by
      intro K s t hP_ends hK_le
      refine (Compatible.of_le_le hP_ends.1.le hsep_G.1).le_iff.mpr ⟨?_, ?_⟩
      · intro u hu
        have hu' : inlV u ∈ V(G₁') := hK_le.vertexSet_mono hu
        rcases hu' with ⟨w, hw, hw_eq⟩ | ⟨w, _, hw_eq⟩
        · exact inlV_injective hw_eq ▸ hw
        · exact (Sum.inl_ne_inr hw_eq.symm).elim
      · intro e he
        have he' : inlE e ∈ E(G₁') := hK_le.edgeSet_mono he.2
        rcases he' with ⟨f, hf, hf_eq⟩ | ⟨w, _, hw_eq⟩
        · exact inlE_injective hf_eq ▸ hf
        · exact (Sum.inl_ne_inr hw_eq.symm).elim
    refine ⟨unspikeGraph S.G K₁, unspikeGraph S.G K₂, ⟨?_, s₁, t₁, s₂, t₂, hP₁_ends, hP₂_ends,
      (S.Ω.mapInr_crosses_iff s₁ t₁ s₂ t₂).mp hcr_K12⟩,
      hunspike_le hP₁_ends hK₁_le, hunspike_le hP₂_ends hK₂_le⟩
    rw [disjoint_left] at hdisj_K12 ⊢
    intro u hu₁ hu₂
    exact hdisj_K12 (by rw [hVK₁]; exact Or.inl ⟨u, hu₁, rfl⟩)
      (by rw [hVK₂]; exact Or.inl ⟨u, hu₂, rfl⟩)
  · right
    obtain ⟨hcr_P, hcard_P, hW_eq⟩ := isCrookedTransaction_unspikeGraph S hcr_P'
    refine ⟨unspikeGraph S.G '' P_set', hcr_P, hcard_P.trans hcard_P', ?_⟩
    change Disjoint (S.Ω.mapInr.interval (inrV (a 0)) (inrV (b 0))) _ at hdisj_P'
    rwa [S.Ω.mapInr_interval, hW_eq, Set.disjoint_image_iff inrV_injective] at hdisj_P'

/-! ## 2. Refinement of GM09 (10.3) and (10.4) for `p = 2` -/

/-- One step of `(10.3)` for `p = 2` under breadth `≥ 2` and `4 ≤ X.ncard`. -/
private theorem theorem_10_3_p2_step {S_comp S₀ : Society α β} {N : Neighborhood α β} {X Y : Set α}
    (hrural : N.IsRural) (hbreadth : N.HasBreadthGe 2)
    (hX : N.IsWeaklyLinked X) (hcard : 4 ≤ X.ncard) (hcomp : S_comp.IsComposition S₀ N)
    (hXY : X ⊆ Y) (hY : Y ⊆ S_comp.Ω.bar) {x : α} (hxY : x ∈ Y) (hxX : x ∉ X)
    {P₀ : Set (Graph α β)} (hP₀ : S_comp.IsCrookedTransaction P₀) (hp : 2 ≤ P₀.ncard)
    (hends : S_comp.transactionEnds P₀ ⊆ Y) :
    ∃ P' : Set (Graph α β), S_comp.IsCrookedTransaction P' ∧ P'.ncard = 2 ∧
      S_comp.transactionEnds P' ⊆ Y \ {x} := by
  classical
  obtain ⟨P_pres, C, hC⟩ := hbreadth
  have hΩ : N.Ω = S_comp.Ω := hcomp.2.1
  have hXb : X ⊆ N.Ω.bar := hX.1
  obtain ⟨a, b, ha, hb, hL⟩ := CyclicPerm.exists_ofFn_around (s := 2) hXb
    (hΩ ▸ hY hxY : x ∈ N.Ω.bar) hxX (by omega)
  have hL₀ : N.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b) :=
    hL.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
  have hW : N.IsWeaklyLinked (range a ∪ range b) := hX.mono <| by
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ha i
    · exact hb i
  let S' := S_comp.restrictOmega Y hY
  have hbarS' : S'.Ω.bar = Y := S_comp.Ω.restrict_bar hY
  obtain ⟨Q, hinj, hcw', hendsQ, htr, hsep_Q, hint, hQs⟩ :=
    exists_restricted_separating_transaction (s := 0) hcomp hY P_pres ⟨C, hC⟩
      (fun i => hXY (ha i)) (fun i => hXY (hb i)) hW hL₀
  obtain ⟨G₁, G₂, hsep, hinter, hQ1_le, h₁, h₂, h₀⟩ := hQs 1
  obtain ⟨hs2, hV2⟩ := hcomp.isGraphSeparation_union hsep h₀
  rcases theorem_5_2_p2_without_no_internal S'
    ⟨P₀, (S_comp.isCrookedTransaction_restrictOmega_iff hY).mpr ⟨hP₀, hends⟩, hp⟩ hinj htr hsep_Q
    hendsQ hcw' hs2 (hV2.trans hinter) hQ1_le ((hint 1).1.trans (hΩ ▸ h₁))
    ((hint 1).2.trans ((hΩ ▸ h₂).trans subset_union_left)) with
    ⟨P₁, P₂, ⟨hdisj, s₁, t₁, s₂, t₂, hP₁, hP₂, hc⟩, hle₁, hle₂⟩ | ⟨P', hcr, hcard', hdis⟩
  · exfalso
    have hlift : ∀ {R : Graph α β} {u w : α}, S'.IsOmegaPathWithEnds R u w →
        R ≤ G₁ → u ≠ w → u ∈ N.Ω.bar → w ∈ N.Ω.bar →
        ({ G := N.G, Ω := N.Ω, finite_V := N.finite_V, finite_E := N.finite_E,
           bar_subset := N.bar_subset } : Society α β).IsOmegaPathWithEnds R u w := by
      intro R u w hR hle hne hu hw
      exact ⟨hR.1.of_le (hle.trans hsep.1), hne, hu, hw⟩
    have hYN : ∀ {v}, v ∈ S'.Ω.bar → v ∈ N.Ω.bar := fun {v} hv => by
      rw [hbarS'] at hv
      exact hΩ ▸ hY hv
    exact not_omegaPathsCross_of_isRural hrural ⟨hdisj, s₁, t₁, s₂, t₂,
      hlift hP₁ hle₁ hP₁.2.1 (hYN hP₁.2.2.1) (hYN hP₁.2.2.2),
      hlift hP₂ hle₂ hP₂.2.1 (hYN hP₂.2.2.1) (hYN hP₂.2.2.2),
      show N.Ω.Crosses s₁ t₁ s₂ t₂ by
        rw [hΩ]
        exact ((S_comp.Ω.crosses_restrict_iff hY).mp hc).2.2.2.2⟩
  · obtain ⟨hcS, hsub⟩ := (S_comp.isCrookedTransaction_restrictOmega_iff hY).mp hcr
    refine ⟨P', hcS, hcard', fun v hv => ⟨hsub hv, ?_⟩⟩
    rintro rfl
    have hx : v ∈ S_comp.Ω.interval (a 0) (b 0) :=
      hΩ ▸ CyclicPerm.mem_interval_of_around (s := 1) hL
    have hx' : v ∈ S'.Ω.interval (a 0) (b 0) := by
      change v ∈ (S_comp.Ω.restrict Y hY).interval _ _
      rw [S_comp.Ω.interval_restrict hY _ _ (hXY (ha _)) (hXY (hb _))]
      exact ⟨hx, hxY⟩
    refine Set.disjoint_left.mp hdis hx' ?_
    rwa [S_comp.transactionEnds_restrictOmega_eq hY hsub]

/-- Refinement of Graph Minors IX, `(10.3)` for `p = 2` under breadth `≥ 2` and `4 ≤ X.ncard`. -/
private theorem theorem_10_3_p2 {S_comp S₀ : Society α β} {N : Neighborhood α β} {X : Set α}
    (hrural : N.IsRural) (hbreadth : N.HasBreadthGe 2)
    (hX : N.IsWeaklyLinked X) (hcard : 4 ≤ X.ncard) (hcomp : S_comp.IsComposition S₀ N)
    {P₀ : Set (Graph α β)} (hP₀ : S_comp.IsCrookedTransaction P₀) (hp : 2 ≤ P₀.ncard) :
    ∃ P' : Set (Graph α β), S_comp.IsCrookedTransaction P' ∧ P'.ncard = 2 ∧
      S_comp.transactionEnds P' ⊆ X := by
  have hΩ : N.Ω = S_comp.Ω := hcomp.2.1
  have hXb : X ⊆ S_comp.Ω.bar := hΩ ▸ hX.1
  have hfin : S_comp.Ω.bar.Finite := S_comp.Ω.finite_bar
  have key : ∀ (n : ℕ) (Y : Set α), (Y \ X).ncard = n → X ⊆ Y → Y ⊆ S_comp.Ω.bar →
      ∀ P₁ : Set (Graph α β), S_comp.IsCrookedTransaction P₁ → 2 ≤ P₁.ncard →
        S_comp.transactionEnds P₁ ⊆ Y →
        ∃ P' : Set (Graph α β), S_comp.IsCrookedTransaction P' ∧ P'.ncard = 2 ∧
          S_comp.transactionEnds P' ⊆ X := by
    intro n
    induction n with
    | zero =>
      intro Y hn _ hY P₁ hP₁ hp₁ hends
      have hYX : Y \ X = ∅ := (ncard_eq_zero (hfin.subset (sdiff_subset.trans hY))).mp hn
      obtain ⟨P', hsub, hcard', hcr'⟩ := S_comp.theorem_3_4_proof (by decide : 2 ≤ 2)
        (by decide : 2 ≠ 3) hP₁ hp₁
      have hends' : S_comp.transactionEnds P' ⊆ S_comp.transactionEnds P₁ :=
        fun v ⟨Q, hQ, u, hQu⟩ => ⟨Q, hsub hQ, u, hQu⟩
      exact ⟨P', hcr', hcard', hends'.trans (hends.trans (sdiff_eq_empty.mp hYX))⟩
    | succ n ih =>
      intro Y hn hXY hY P₁ hP₁ hp₁ hends
      obtain ⟨x, hxY, hxX⟩ : (Y \ X).Nonempty := by
        rw [← Set.ncard_pos (hfin.subset (sdiff_subset.trans hY))]
        omega
      obtain ⟨P₂, hP₂, hp₂_eq, hends₂⟩ := theorem_10_3_p2_step hrural hbreadth hX hcard hcomp hXY
        hY hxY hxX hP₁ hp₁ hends
      refine ih (Y \ {x}) ?_ (fun v hv => ⟨hXY hv, fun e => hxX (e ▸ hv)⟩)
        (sdiff_subset.trans hY) P₂ hP₂ hp₂_eq.symm.le hends₂
      have hsets : (Y \ {x}) \ X = (Y \ X) \ {x} := by
        ext v
        simp only [mem_sdiff, mem_singleton_iff]
        tauto
      rw [hsets, ncard_sdiff_singleton_of_mem (show x ∈ Y \ X from ⟨hxY, hxX⟩), hn]
      rfl
  exact key _ _ rfl hXb Subset.rfl P₀ hP₀ hp fun v hv => by
    obtain ⟨P, _, b, hb⟩ := hv
    exact hb.2.2.1

/-- `exists_clean_paths` for a nest of `3` circuits (giving `2` clean circuits). -/
private theorem exists_clean_paths_p2 {N : Neighborhood α β} (P_pres : Presentation N)
    {C' : Fin 3 → Graph α β} (hC' : N.IsNest P_pres C') {X : Set α} (hX : N.IsLinked X) :
    ∃ (C : Fin 2 → Graph α β) (P : Fin X.ncard → Graph α β) (x t : Fin X.ncard → α),
      N.IsNest P_pres C ∧ (∀ j, Disjoint V(C j) N.Ω.bar) ∧
      (∀ i, IsFromToPathWithEnds N.G (P i) X N.Ω₀.bar (x i) (t i) ∧ V(P i) ∩ N.Ω.bar = {x i}) ∧
      Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
      ∀ i j, ∃ I, IsGraphPath N.G I ∧ I ≤ P i ∧ I ≤ C j ∧ V(I) = V(P i) ∩ V(C j) :=
  GM09.exists_clean_paths_of_nest P_pres (n := 2) (by decide) hC' hX

private theorem paths_split_at_last_circuit
    {α : Type u}
    {β : Type v}
    {N : Neighborhood α β}
    {X : Set α}
    (C : Fin 2 → Graph α β)
    (P : Fin X.ncard → Graph α β)
    (x : Fin X.ncard → α)
    (t : Fin X.ncard → α)
    (hP : ∀ (i : Fin X.ncard), IsFromToPathWithEnds N.G (P i) X N.Ω₀.bar (x i) (t i) ∧ V(P i) ∩
      N.Ω.bar = {x i})
    (hI : ∀ (i : Fin X.ncard) (j : Fin 2), ∃ I, IsGraphPath N.G I ∧ I ≤ P i ∧ I ≤ C j ∧ V(I) = V(P
      i) ∩ V(C j))
    (last : Fin 2)
    (H₁ : Graph α β)
    (H₂ : Graph α β)
    (hsep : IsGraphSeparation N.G H₁ H₂)
    (hcut : V(H₁) ∩ V(H₂) = V(C last))
    (hKH₁ : C last ≤ H₁)
    (hK₂ : V(C last) ⊆ V(H₂))
    (hbarH₂ : N.Ω.bar ⊆ V(H₂))
    (hbar₀H₁ : N.Ω₀.bar ⊆ V(H₁))
    (hPN : ∀ (i : Fin X.ncard), IsGraphPathWithEnds N.G (P i) (x i) (t i)) :
    ∀ (i : Fin X.ncard), ∃ y R W, y ∈ V(C last) ∧ IsGraphPathWithEnds H₂ R (x i) y ∧ V(R) ⊆ V(P i)
      ∧ V(R) ∩ V(C last) = {y} ∧ IsGraphPathWithEnds H₁ W y (t i) ∧ V(W) ⊆ V(P i) := by
  intro i
  obtain ⟨I, ⟨u, w, hIp⟩, hIP, hIK, hVI⟩ := hI i last
  have hne : (V(P i) ∩ V(C last)).Nonempty := ⟨u, hVI ▸ hIp.left_mem⟩
  have hne' := hne
  obtain ⟨y, hy, R, -, hRP, -, hRp, -, -, -, -, hRd⟩ :=
    (hPN i).exists_first_split_at_mem hne
  obtain ⟨z, hz, T, -, hTP, -, hTp, -, -, -, -, hTd⟩ :=
    (hPN i).symm.exists_first_split_at_mem hne'
  have hinter : ∀ {Q : Graph α β} {q : α}, q ∈ V(Q) → q ∈ V(C last) →
      Disjoint (V(Q) \ {q}) V(C last) → V(Q) ∩ V(C last) = {q} := by
    intro Q q hq hqK hd
    apply Subset.antisymm
    · rintro v ⟨hv, hvK⟩
      by_contra hne
      exact Set.disjoint_left.mp hd ⟨hv, hne⟩ hvK
    · rintro _ rfl
      exact ⟨hq, hqK⟩
  have hRV := hinter hRp.right_mem hy.2 hRd
  have hTV := hinter hTp.right_mem hz.2 hTd
  have hRN : IsGraphPathWithEnds N.G R (x i) y := hRp.mono (hPN i).le
  have hTN : IsGraphPathWithEnds N.G T (t i) z := hTp.mono (hPN i).le
  have hxb : x i ∈ N.Ω.bar := by
    have : x i ∈ V(P i) ∩ N.Ω.bar := (hP i).2.symm ▸ mem_singleton _
    exact this.2
  have ht₀ : t i ∈ N.Ω₀.bar := by
    have : t i ∈ V(P i) ∩ N.Ω₀.bar := (hP i).1.2.2.symm ▸ mem_singleton _
    exact this.2
  have hRH₂ : R ≤ H₂ := hRN.le_right_of_inter_subset hsep
    (by rw [hcut, hRV]) (hbarH₂ hxb) (hK₂ hy.2)
  have hTH₁ : T ≤ H₁ := hTN.le_right_of_inter_subset (IsGraphSeparation.symm hsep)
    (by rw [inter_comm V(H₂), hcut, hTV]) (hbar₀H₁ ht₀) (hKH₁.vertexSet_mono hz.2)
  have hyI : y ∈ V(I) := hVI ▸ hy
  have hzI : z ∈ V(I) := hVI ▸ hz
  obtain ⟨M, hMI, hMp, -⟩ := hIp.exists_subpath hyI hzI
  have hMH₁ : IsGraphPathWithEnds H₁ M y z := hMp.mono (hIK.trans hKH₁)
  have hTH : IsGraphPathWithEnds H₁ T z (t i) := (hTN.of_le hTH₁).symm
  have hMT : V(M) ∩ V(T) = {z} := by
    apply Subset.antisymm
    · rintro v ⟨hv, hvT⟩
      have : v ∈ V(T) ∩ V(C last) := ⟨hvT, (hMI.trans hIK).vertexSet_mono hv⟩
      rwa [hTV] at this
    · rintro _ rfl
      exact ⟨hMp.right_mem, hTp.right_mem⟩
  refine ⟨y, R, _, hy.2, hRN.of_le hRH₂, hRP.vertexSet_mono, hRV, hMH₁.subgraphUnion hTH hMT, ?_⟩
  rw [vertexSet_subgraphUnion]
  exact union_subset (hMI.trans hIP).vertexSet_mono hTP.vertexSet_mono

private theorem inner_segments_form_weak_linkage
    {α : Type u}
    {β : Type v}
    {N : Neighborhood α β}
    {X : Set α}
    (P : Fin X.ncard → Graph α β)
    (x : Fin X.ncard → α)
    (t : Fin X.ncard → α)
    (hP : ∀ (i : Fin X.ncard), IsFromToPathWithEnds N.G (P i) X N.Ω₀.bar (x i) (t i) ∧ V(P i) ∩
      N.Ω.bar = {x i})
    (hPd : Pairwise fun i j => Disjoint V(P i) V(P j))
    (N₁ : Neighborhood α β) (hΩ₀ : N₁.Ω₀ = N.Ω₀)
    (y : Fin X.ncard → α)
    (R : Fin X.ncard → Graph α β)
    (W : Fin X.ncard → Graph α β)
    (hyK : ∀ (i : Fin X.ncard), y i ∈ N₁.Ω.bar)
    (hRP : ∀ (i : Fin X.ncard), V(R i) ⊆ V(P i))
    (hW : ∀ (i : Fin X.ncard), IsGraphPathWithEnds N₁.G (W i) (y i) (t i))
    (hWP : ∀ (i : Fin X.ncard), V(W i) ⊆ V(P i))
    (hyR : ∀ (i : Fin X.ncard), y i ∈ V(R i))
    (hYcard : (range y).ncard = X.ncard) :
    N₁.IsWeaklyLinked (range y) := by
  refine ⟨by rintro _ ⟨i, rfl⟩; exact hyK i,
    fun j => W (Fin.cast hYcard j), fun j => ?_, fun i j hij => ?_⟩
  · set i := Fin.cast hYcard j
    refine ⟨y i, t i, hW i, ?_, ?_⟩
    · apply Subset.antisymm
      · rintro v ⟨hv, ⟨k, rfl⟩⟩
        by_cases hik : i = k
        · subst hik
          rfl
        · exact (Set.disjoint_left.mp (hPd hik) (hWP i hv) (hRP k (hyR k))).elim
      · rintro _ rfl
        exact ⟨(hW i).left_mem, mem_range_self i⟩
    · apply Subset.antisymm
      · rintro v ⟨hv, hv₀⟩
        have : v ∈ V(P i) ∩ N.Ω₀.bar := ⟨hWP i hv, hΩ₀ ▸ hv₀⟩
        rwa [(hP i).1.2.2] at this
      · rintro _ rfl
        have : t i ∈ V(P i) ∩ N.Ω₀.bar := (hP i).1.2.2.symm ▸ mem_singleton _
        exact ⟨(hW i).right_mem, hΩ₀.symm ▸ this.2⟩
  · refine (hPd fun e => hij ?_).mono (hWP _) (hWP _)
    exact Fin.cast_injective hYcard e

/-- Refinement of Graph Minors IX, `(10.4)` for `p = 2` under breadth `≥ 3` and `4 ≤ X.ncard`. -/
private theorem theorem_10_4_p2 {S_comp S₀ : Society α β} {N : Neighborhood α β} {X : Set α}
    (hbreadth : N.HasBreadthGe 3)
    (hX : N.IsLinked X) (hcard : 4 ≤ X.ncard) (hcomp : S_comp.IsComposition S₀ N)
    {P₀ : Set (Graph α β)} (hP₀ : S_comp.IsCrookedTransaction P₀) (hp : 2 ≤ P₀.ncard) :
    ∃ P' : Set (Graph α β), S_comp.IsCrookedTransaction P' ∧ P'.ncard = 2 ∧
      S_comp.transactionEnds P' ⊆ X ∧
      ∀ P ∈ P', Disjoint (pathInternalVerts S_comp.G P) S_comp.Ω.bar := by
  classical
  obtain ⟨P_pres, C', hC'⟩ := hbreadth
  have hXb : X ⊆ N.Ω.bar := hX.1
  obtain ⟨C, P, x, t, hC, hCbar, hP, hPd, hI⟩ := exists_clean_paths_p2 P_pres hC' hX
  have hΩ : N.Ω = S_comp.Ω := hcomp.2.1
  have hNG : N.G ≤ S_comp.G := hcomp.1.1.2.1
  let last : Fin 2 := 1
  obtain ⟨hcir, hdisj, D, hDd, hDs, hDm⟩ := hC
  obtain ⟨N₁, N₂, P₁, S₁, hsep, hcut, hKH₁, hΩ₁, hbarH₂, hbar₀H₁, hrural₁, hrural₂,
      hnest₁, hS₁S, hcutU, hcomp₁, hcomp₂⟩ :=
    exists_nested_neighborhood_composition P_pres C D last (fun i => Fin.le_last i)
      hcir hdisj hDd hDs hDm (hCbar last) hcomp
  let H₁ := N₁.G
  let H₂ := N₂.G
  have hK₂ : V(C last) ⊆ V(H₂) := fun v hv =>
    (hcut.symm ▸ hv : v ∈ V(H₁) ∩ V(H₂)).2
  have hPN : ∀ i, IsGraphPathWithEnds N.G (P i) (x i) (t i) := fun i => (hP i).1.1
  have hsplit : ∀ i, ∃ (y : α) (R W : Graph α β), y ∈ V(C last) ∧
      IsGraphPathWithEnds H₂ R (x i) y ∧ V(R) ⊆ V(P i) ∧ V(R) ∩ V(C last) = {y} ∧
      IsGraphPathWithEnds H₁ W y (t i) ∧ V(W) ⊆ V(P i) := by
    exact paths_split_at_last_circuit (α := α) (β := β) (N := N) (X := X) C P x t hP hI last H₁ H₂
      hsep hcut hKH₁ hK₂ hbarH₂ hbar₀H₁ hPN
  choose y R W hyK hR hRP hRK hW hWP using hsplit
  have hyR : ∀ i, y i ∈ V(R i) := fun i => (hR i).right_mem
  have hy_inj : Injective y := by
    intro i j e
    by_contra hne
    exact Set.disjoint_left.mp (hPd hne) (hRP i (hyR i)) (e ▸ hRP j (hyR j))
  have hx_inj : Injective x := by
    intro i j e
    by_contra hne
    exact Set.disjoint_left.mp (hPd hne) (hPN i).left_mem (e ▸ (hPN j).left_mem)
  have hRd : ∀ {i j}, i ≠ j → Disjoint V(R i) V(R j) := fun hne =>
    (hPd hne).mono (hRP _) (hRP _)
  have hYcard : (range y).ncard = X.ncard := by
    rw [← image_univ, ncard_image_of_injective _ hy_inj, ncard_univ, Nat.card_fin]
  have hΩ₀ : N₁.Ω₀ = N.Ω₀ := hcomp₁.2.2.1.trans hcomp.2.2.1.symm
  have hweak_after_split : N₁.IsWeaklyLinked (range y) := by
    exact inner_segments_form_weak_linkage (α := α) (β := β) (N := N) (X := X) P x t hP hPd
      N₁ hΩ₀ y R W (fun i => hΩ₁.symm ▸ hyK i) hRP hW hWP hyR hYcard
  obtain ⟨T₀, hT₀, hpT₀⟩ := GraphMinor.GM09.theorem_9_1_proof hcomp₂ hrural₂ hP₀ hp
  obtain ⟨T, hT, hpT, hTends⟩ := theorem_10_3_p2 hrural₁ ⟨P₁, C, hnest₁⟩ hweak_after_split
    (by rw [hYcard]; exact hcard) hcomp₁ hT₀ hpT₀
  have hxb : ∀ i, x i ∈ S_comp.Ω.bar := by
    intro i
    have hx : x i ∈ V(P i) ∩ N.Ω.bar := (hP i).2.symm ▸ mem_singleton _
    exact hΩ ▸ hx.2
  have hxX : ∀ i, x i ∈ X := fun i =>
    ((hP i).1.2.1.symm ▸ mem_singleton _ : x i ∈ V(P i) ∩ X).2
  have hRbar : ∀ i, V(R i) ∩ S_comp.Ω.bar = {x i} := by
    intro i
    apply Subset.antisymm
    · intro v hv
      have hmem : v ∈ V(P i) ∩ N.Ω.bar := ⟨hRP i hv.1, hΩ ▸ hv.2⟩
      rwa [(hP i).2] at hmem
    · rintro _ rfl
      exact ⟨(hR i).left_mem, hxb i⟩
  obtain ⟨T', hT', hsize, hends, hinternal⟩ :=
    extend_crooked_transaction_across_neighborhood (N₂ := N₂) (K := C last) (by omega)
      hS₁S (hsep.2.1.trans hNG) hcutU hcomp₂.2.1 hcomp₂.2.2.1
      hrural₂ (fun v hv => hbarH₂ (hΩ ▸ hv)) (hΩ ▸ hCbar last)
      hR hRK hy_inj hx_inj hRd (fun i => hcomp₁.2.1 ▸ (hΩ₁.symm ▸ hyK i))
      hxb hxX hRbar hT hTends
  exact ⟨T', hT', hsize.trans hpT, hends, hinternal⟩

/-! ## 3. Proof of Graph Minors XIV, (8.3) (pages 40–41) -/

/-- **Graph Minors XIV, (8.3)** (pages 40–41):
"Let $(G, \Omega_1)$ be the composition of a society $(G_2, \Omega_2)$ with a rural neighbourhood
$(G_1, \Omega_1, \Omega_2)$ of breadth $\ge 3$. Suppose that $X \subseteq \bar{\Omega}_1$ and
there are $4$ mutually disjoint paths in $G_1$, each from $X$ to $\bar{\Omega}_2$ with no vertex
in $\bar{\Omega}_1$ except its initial vertex. If there is a cross $\mathscr{P}$ in $(G, \Omega_1)$
then $\mathscr{P}$ may be chosen so that in addition $V(\mathscr{P}) \subseteq X$ and no member of
$\mathscr{P}$ has any internal vertex in $\bar{\Omega}$." -/
theorem theorem_8_3_proof
    (S_comp S₂ : Society α β) (N : Neighborhood α β) (X : Set α)
    (P : Fin 4 → Graph α β) (x y : Fin 4 → α)
    (P_set : Set (Graph α β))
    (hcomp : S_comp.IsComposition S₂ N)
    (hbreadth : N.HasBreadthGe 3)
    (hX : X ⊆ N.Ω.bar)
    (hP_path : ∀ i, IsFromToPathWithEnds N.G (P i) N.Ω.bar N.Ω₀.bar (x i) (y i) ∧ x i ∈ X)
    (hP_disj : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hCrooked : S_comp.IsCrookedTransaction P_set)
    (hcard : P_set.ncard = 2) :
    ∃ P_set' : Set (Graph α β),
      S_comp.IsCrookedTransaction P_set' ∧
      P_set'.ncard = 2 ∧
      S_comp.transactionEnds P_set' ⊆ X ∧
      ∀ Q ∈ P_set', Disjoint (pathInternalVerts S_comp.G Q) S_comp.Ω.bar := by
  let X' : Set α := range x
  have hX'_sub : X' ⊆ X := by
    rintro _ ⟨i, rfl⟩
    exact (hP_path i).2
  have hx_inj : Injective x := by
    intro i j hxy
    by_contra hne
    have hxi : x i ∈ V(P i) := (hP_path i).1.1.left_mem
    have hxj : x i ∈ V(P j) := hxy ▸ (hP_path j).1.1.left_mem
    exact disjoint_left.mp (hP_disj hne) hxi hxj
  have hX'_card : X'.ncard = 4 := by
    rw [ncard_range_of_injective hx_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hLinked : N.IsLinked X' := by
    refine ⟨hX'_sub.trans hX, fun k => P (Fin.cast hX'_card k), fun k => ?_, fun i j hne => ?_⟩
    · let i := Fin.cast hX'_card k
      have hy_bar : y i ∈ N.Ω₀.bar := by
        have : y i ∈ V(P i) ∩ N.Ω₀.bar := by
          rw [(hP_path i).1.2.2]
          exact mem_singleton (y i)
        exact this.2
      exact ⟨x i, mem_range_self i, y i, hy_bar, (hP_path i).1⟩
    · have hne' : Fin.cast hX'_card i ≠ Fin.cast hX'_card j :=
        fun h => hne ((Fin.cast_injective hX'_card) h)
      exact hP_disj hne'
  obtain ⟨P_set', hCr', hcard', hEnds', hInt'⟩ :=
    theorem_10_4_p2 hbreadth hLinked (Nat.le_of_eq hX'_card.symm) hcomp hCrooked hcard.symm.le
  exact ⟨P_set', hCr', hcard', hEnds'.trans hX'_sub, hInt'⟩

end GraphMinor.GM14
