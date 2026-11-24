/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM14.Section8a
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

/-- A crooked transaction `{P₁, P₂}` with `P₁ ≠ P₂` is a cross: `S.OmegaPathsCross P₁ P₂`. -/
private theorem omegaPathsCross_of_isCrookedTransaction_pair (S : Society α β)
    {P₁ P₂ : Graph α β} (hne : P₁ ≠ P₂) (hcr : S.IsCrookedTransaction {P₁, P₂}) :
    S.OmegaPathsCross P₁ P₂ := by
  obtain ⟨⟨A, B, hF⟩, hnp⟩ := hcr
  obtain ⟨a₁, -, b₁, -, h₁⟩ := hF.2.2 P₁ (Or.inl rfl)
  obtain ⟨a₂, -, b₂, -, h₂⟩ := hF.2.2 P₂ (Or.inr rfl)
  have hdisj : Disjoint V(P₁) V(P₂) := hF.1.2 (Or.inl rfl) (Or.inr rfl) hne
  have hends : ∀ v ∈ S.transactionEnds {P₁, P₂}, (v = a₁ ∨ v = b₁) ∨ (v = a₂ ∨ v = b₂) := by
    rintro v ⟨P, hP, b, hv⟩
    have hmem : v ∈ pathEnds S.G P := by
      rw [hv.1.pathEnds_eq]
      exact Or.inl rfl
    rcases hP with rfl | rfl
    · rw [h₁.1.pathEnds_eq] at hmem
      exact Or.inl hmem
    · rw [h₂.1.pathEnds_eq] at hmem
      exact Or.inr hmem
  have hnd₁ : ¬ Disjoint (S.Ω.interval a₁ b₁) (S.transactionEnds {P₁, P₂}) := fun hd =>
    hnp P₁ (Or.inl rfl) ⟨Or.inl rfl, a₁, b₁, h₁, Or.inl hd⟩
  have hnd₂ : ¬ Disjoint (S.Ω.interval b₁ a₁) (S.transactionEnds {P₁, P₂}) := fun hd =>
    hnp P₁ (Or.inl rfl) ⟨Or.inl rfl, a₁, b₁, h₁, Or.inr hd⟩
  obtain ⟨x, hx, hxe⟩ := Set.not_disjoint_iff.mp hnd₁
  obtain ⟨y, hy, hye⟩ := Set.not_disjoint_iff.mp hnd₂
  have hxe' : x = a₂ ∨ x = b₂ := by
    rcases hends x hxe with (rfl | rfl) | h
    · exact (S.Ω.not_mem_interval_left _ _ hx).elim
    · exact (S.Ω.not_mem_interval_right _ _ hx).elim
    · exact h
  have hye' : y = a₂ ∨ y = b₂ := by
    rcases hends y hye with (rfl | rfl) | h
    · exact (S.Ω.not_mem_interval_right _ _ hy).elim
    · exact (S.Ω.not_mem_interval_left _ _ hy).elim
    · exact h
  have hxy : x ≠ y := fun h =>
    Set.disjoint_left.mp (S.Ω.disjoint_interval_swap a₁ b₁) hx (h ▸ hy)
  refine ⟨hdisj, a₁, b₁, a₂, b₂, h₁, h₂, S.Ω.crosses_iff_interval.mpr ?_⟩
  rcases hxe' with rfl | rfl <;> rcases hye' with rfl | rfl
  · exact (hxy rfl).elim
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact (hxy rfl).elim

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
    omegaPathsCross_of_isCrookedTransaction_pair S hP12 hcr_pair
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
  obtain ⟨P₀, hcr_P₀, hp_P₀⟩ := hex_cr
  obtain ⟨hcr_P₀', hcard_P₀'⟩ := isCrookedTransaction_spikeOmegaPath S hcr_P₀
  have hex_cr' : ∃ P₀' : Set (Graph (α ⊕ α) (β ⊕ α)),
      S'.IsCrookedTransaction P₀' ∧ 2 ≤ P₀'.ncard :=
    ⟨spikeOmegaPath S '' P₀, hcr_P₀', hcard_P₀' ▸ hp_P₀⟩
  let Q' : Fin 2 → Graph (α ⊕ α) (β ⊕ α) := fun i => spikeOmegaPath S (Q i)
  let a' : Fin 2 → α ⊕ α := inrV ∘ a
  let b' : Fin 2 → α ⊕ α := inrV ∘ b
  have hQ'_eq : ∀ i, Q' i = spikeGraph (Q i) {a i, b i} :=
    fun i => spikeOmegaPath_eq S (hends_Q i)
  obtain ⟨A_Q, B_Q, hfence_Q⟩ := htr_Q
  obtain ⟨hfence_Q', hinj_Q_on, _⟩ := isFenceFor_spikeOmegaPath S hfence_Q
  have hrange_Q' : range Q' = spikeOmegaPath S '' range Q :=
    range_comp (spikeOmegaPath S) Q
  have hinj_Q' : Function.Injective Q' :=
    fun i j hij => hinj_Q (hinj_Q_on (mem_range_self i) (mem_range_self j) hij)
  have htr_Q' : S'.IsTransaction (range Q') := by
    rw [hrange_Q']
    exact ⟨inrV '' A_Q, inrV '' B_Q, hfence_Q'⟩
  have hsep_Q' : ∀ i : Fin 2, S'.IsSeparatingOmegaPath (Q' i) := by
    intro i
    rw [hQ'_eq i]
    exact isSeparatingOmegaPath_spikeGraph S (hends_Q i) (hsep_Q i)
  have hno_int' : ∀ i : Fin 2, Disjoint (pathInternalVerts S'.G (Q' i)) S'.Ω.bar := by
    intro i
    rw [hQ'_eq i]
    exact (isOmegaPathWithEnds_spikeGraph S (hends_Q i)).2
  have hends_Q' : ∀ i : Fin 2, S'.IsOmegaPathWithEnds (Q' i) (a' i) (b' i) := by
    intro i
    rw [hQ'_eq i]
    exact (isOmegaPathWithEnds_spikeGraph S (hends_Q i)).1
  have hcw' : S'.Ω.IsClockwiseSeq ((List.ofFn a').reverse ++ List.ofFn b') := by
    have h_list : (List.ofFn a').reverse ++ List.ofFn b' =
        ((List.ofFn a).reverse ++ List.ofFn b).map inrV := by
      rw [List.map_append, List.map_reverse, List.map_ofFn, List.map_ofFn]
    rw [h_list]
    exact (S.Ω.mapInr_isClockwiseSeq_iff _).mpr hcw
  let m : Fin 2 := 1
  have hm_ends := hends_Q m
  have ha_m_Qm : a m ∈ V(Q m) := hm_ends.1.left_mem
  have hb_m_Qm : b m ∈ V(Q m) := hm_ends.1.right_mem
  have ha_m_G₁ : a m ∈ V(G₁) := (hinter_G ▸ ha_m_Qm : a m ∈ V(G₁) ∩ V(G₂)).1
  have hb_m_G₁ : b m ∈ V(G₁) := (hinter_G ▸ hb_m_Qm : b m ∈ V(G₁) ∩ V(G₂)).1
  have ha_m_G₂ : a m ∈ V(G₂) := (hinter_G ▸ ha_m_Qm : a m ∈ V(G₁) ∩ V(G₂)).2
  have hb_m_G₂ : b m ∈ V(G₂) := (hinter_G ▸ hb_m_Qm : b m ∈ V(G₁) ∩ V(G₂)).2
  let X₁ : Set α := {a m, b m} ∪ S.Ω.interval (a m) (b m)
  let X₂ : Set α := S.Ω.interval (b m) (a m)
  have hfence_m : S.Ω.IsFence X₁ X₂ :=
    S.Ω.isFence_interval_compl hm_ends.2.2.1 hm_ends.2.2.2 hm_ends.2.1
  have hX₁_sub_G₁ : X₁ ⊆ V(G₁) := by
    rintro x ((rfl | rfl) | hx)
    · exact ha_m_G₁
    · exact hb_m_G₁
    · exact hint_G₁ hx
  have hX₁_inter : X₁ ∩ V(G₁) = X₁ := inter_eq_left.mpr hX₁_sub_G₁
  have hX₂_inter : X₂ ∩ V(G₂) = X₂ := inter_eq_left.mpr hint_G₂
  have hX₂Z_inter : (X₂ ∪ {a m, b m}) ∩ V(G₂) = X₂ ∪ {a m, b m} := by
    refine inter_eq_left.mpr ?_
    rintro x (hx | rfl | rfl)
    · exact hint_G₂ hx
    · exact ha_m_G₂
    · exact hb_m_G₂
  have hbar_inter : S.Ω.bar ∩ V(S.G) = S.Ω.bar := inter_eq_left.mpr S.bar_subset
  let G₁' := spikeGraph G₁ X₁
  let G₂' := spikeGraphWithVerts G₂ X₂ {a m, b m}
  have hG₁'_le : G₁' ≤ S'.G :=
    spikeGraph_le hsep_G.1 (by rw [hX₁_inter, hbar_inter]; exact hfence_m.1)
  have hG₂'_le : G₂' ≤ S'.G := by
    refine ⟨union_subset_union (image_mono hsep_G.2.1.vertexSet_mono) (image_mono ?_), ?_⟩
    · rw [hX₂Z_inter, hbar_inter]
      rintro x (hx | rfl | rfl)
      · exact hfence_m.2.1 hx
      · exact hm_ends.2.2.1
      · exact hm_ends.2.2.2
    · intro e x y h
      rcases h with ⟨hlink⟩ | ⟨hx⟩ | ⟨hx⟩
      · exact .inl (hlink.mono hsep_G.2.1)
      · exact .inr_lr ⟨hfence_m.2.1 hx.1, hsep_G.2.1.vertexSet_mono hx.2⟩
      · exact .inr_rl ⟨hfence_m.2.1 hx.1, hsep_G.2.1.vertexSet_mono hx.2⟩
  have hsep_G' : IsGraphSeparation S'.G G₁' G₂' := by
    refine ⟨hG₁'_le, hG₂'_le, ?_, ?_, ?_⟩
    · change ((inlV '' V(G₁)) ∪ (inrV '' (X₁ ∩ V(G₁)))) ∪
        ((inlV '' V(G₂)) ∪ (inrV '' ((X₂ ∪ {a m, b m}) ∩ V(G₂)))) =
        (inlV '' V(S.G)) ∪ (inrV '' (S.Ω.bar ∩ V(S.G)))
      rw [hX₁_inter, hX₂Z_inter, hbar_inter, union_union_union_comm, ← image_union, ← image_union,
        hsep_G.2.2.1]
      congr 2
      apply Subset.antisymm
      · rintro x (hx₁ | hx₂ | rfl | rfl)
        · exact hfence_m.1 hx₁
        · exact hfence_m.2.1 hx₂
        · exact hm_ends.2.2.1
        · exact hm_ends.2.2.2
      · intro x hx
        rw [← hfence_m.2.2.2.1] at hx
        rcases hx with hx₁ | hx₂
        · exact Or.inl hx₁
        · exact Or.inr (Or.inl hx₂)
    · change ((inlE '' E(G₁)) ∪ (inrE '' (X₁ ∩ V(G₁)))) ∪
        ((inlE '' E(G₂)) ∪ (inrE '' (X₂ ∩ V(G₂)))) =
        (inlE '' E(S.G)) ∪ (inrE '' (S.Ω.bar ∩ V(S.G)))
      rw [hX₁_inter, hX₂_inter, hbar_inter, union_union_union_comm, ← image_union, ← image_union,
        hsep_G.2.2.2.1, hfence_m.2.2.2.1]
    · change Disjoint ((inlE '' E(G₁)) ∪ (inrE '' (X₁ ∩ V(G₁))))
        ((inlE '' E(G₂)) ∪ (inrE '' (X₂ ∩ V(G₂))))
      rw [hX₁_inter, hX₂_inter]
      rw [disjoint_left]
      rintro e (⟨e₁, he₁, rfl⟩ | ⟨x₁, hx₁, rfl⟩) (⟨e₂, he₂, h_eq⟩ | ⟨x₂, hx₂, h_eq⟩)
      · exact disjoint_left.mp hsep_G.2.2.2.2 he₁ (inlE_injective h_eq ▸ he₂)
      · exact Sum.inl_ne_inr h_eq.symm
      · exact Sum.inl_ne_inr h_eq
      · exact disjoint_left.mp hfence_m.2.2.1 hx₁ (inrE_injective h_eq ▸ hx₂)
  have hinter_G' : V(G₁') ∩ V(G₂') = V(Q' m) := by
    rw [hQ'_eq m, vertexSet_spikeGraph_of_ends S hm_ends]
    change ((inlV '' V(G₁)) ∪ (inrV '' (X₁ ∩ V(G₁)))) ∩
      ((inlV '' V(G₂)) ∪ (inrV '' ((X₂ ∪ {a m, b m}) ∩ V(G₂)))) =
      (inlV '' V(Q m)) ∪ {inrV (a m), inrV (b m)}
    rw [hX₁_inter, hX₂Z_inter]
    ext z
    rcases z with u | v
    · simp only [mem_inter_iff, mem_union, inlV_injective.mem_set_image, mem_image,
        Sum.inr_ne_inl, and_false, exists_false, or_false, mem_insert_iff, mem_singleton_iff,
        Sum.inl_ne_inr]
      rw [← mem_inter_iff, hinter_G]
    · simp only [mem_inter_iff, mem_union, inrV_injective.mem_set_image, mem_image,
        Sum.inl_ne_inr, and_false, exists_false, false_or, mem_insert_iff, mem_singleton_iff,
        inrV_injective.eq_iff]
      constructor
      · rintro ⟨hv₁ | hv₁, hv₂ | hv₂⟩
        · exact hv₁
        · exact hv₁
        · exact (disjoint_left.mp hfence_m.2.2.1 (Or.inr hv₁) hv₂).elim
        · exact hv₂
      · rintro (rfl | rfl)
        · exact ⟨Or.inl (Or.inl rfl), Or.inr (Or.inl rfl)⟩
        · exact ⟨Or.inl (Or.inr rfl), Or.inr (Or.inr rfl)⟩
  have hQ1'_le : Q' m ≤ G₁' := by
    rw [hQ'_eq m]
    refine spikeGraph_le hQ1_le ?_
    rintro x ⟨rfl | rfl, _⟩
    · exact ⟨Or.inl (Or.inl rfl), ha_m_G₁⟩
    · exact ⟨Or.inl (Or.inr rfl), hb_m_G₁⟩
  have hint_G₁' : S'.Ω.interval (a' m) (b' m) ⊆ V(G₁') := by
    change S.Ω.mapInr.interval (inrV (a m)) (inrV (b m)) ⊆
      (inlV '' V(G₁)) ∪ (inrV '' (X₁ ∩ V(G₁)))
    rw [S.Ω.mapInr_interval, hX₁_inter]
    exact subset_union_of_subset_right (image_mono subset_union_right) _
  have hint_G₂' : S'.Ω.interval (b' m) (a' m) ⊆ V(G₂') := by
    change S.Ω.mapInr.interval (inrV (b m)) (inrV (a m)) ⊆
      (inlV '' V(G₂)) ∪ (inrV '' ((X₂ ∪ {a m, b m}) ∩ V(G₂)))
    rw [S.Ω.mapInr_interval, hX₂Z_inter]
    exact subset_union_of_subset_right (image_mono subset_union_left) _
  rcases theorem_5_2_p2 S' hex_cr' hinj_Q' htr_Q' hsep_Q' hno_int' hends_Q' hcw'
      hsep_G' hinter_G' hQ1'_le hint_G₁' hint_G₂' with
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
  have hNG : N.G ≤ S_comp.G := hcomp.1.1.2.1
  have hXb : X ⊆ N.Ω.bar := hX.1
  obtain ⟨a, b, ha, hb, hL⟩ := CyclicPerm.exists_ofFn_around (s := 2) hXb
    (hΩ ▸ hY hxY : x ∈ N.Ω.bar) hxX (by omega)
  have hL₀ : N.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b) :=
    hL.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
  have hW : N.IsWeaklyLinked (range a ∪ range b) := hX.mono <| by
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ha i
    · exact hb i
  obtain ⟨Q, hQ, hQd, hQs⟩ := GraphMinor.GM09.theorem_10_2_proof P_pres ⟨C, hC⟩ hW hL₀
  obtain ⟨-, -, -, hab, -, -⟩ := CyclicPerm.isClockwise3_of_ofFn hL₀
  let S' := S_comp.restrictOmega Y hY
  have hR := S_comp.Ω.isRestriction_restrict hY
  have hbarS' : S'.Ω.bar = Y := S_comp.Ω.restrict_bar hY
  have hcw' : S'.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b) := by
    refine hR.isClockwiseSeq_iff.mpr ⟨?_, hΩ ▸ hL₀⟩
    change _ ⊆ S'.Ω.bar
    rw [hbarS']
    rintro v hv
    simp only [mem_ofPred_eq, List.mem_append, List.mem_reverse, List.mem_ofFn'] at hv
    rcases hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hXY (ha i)
    · exact hXY (hb i)
  have hendsQ : ∀ i, S'.IsOmegaPathWithEnds (Q i) (a i) (b i) := fun i =>
    (S_comp.isOmegaPathWithEnds_restrictOmega_iff hY).mpr
      ⟨⟨(hQ i).mono hNG, hab i i, hY (hXY (ha i)), hY (hXY (hb i))⟩, hXY (ha i), hXY (hb i)⟩
  have hinj : Function.Injective Q := by
    intro i j e
    by_contra hne
    exact Set.disjoint_left.mp (hQd hne) (hQ i).left_mem (e ▸ (hQ i).left_mem)
  have htr : S'.IsTransaction (range Q) := by
    obtain ⟨A, B, hf, hA, hB⟩ := CyclicPerm.exists_isFence_of_ofFn (s := 0) hcw'
    refine ⟨A, B, ⟨?_, ?_⟩, hf, ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨_, _, hendsQ i⟩
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
      exact hQd fun e => hne (congrArg Q e)
    · rintro _ ⟨i, rfl⟩
      exact ⟨_, hA i, _, hB i, hendsQ i⟩
  have hint : ∀ i, S'.Ω.interval (a i) (b i) ⊆ S_comp.Ω.interval (a i) (b i) ∧
      S'.Ω.interval (b i) (a i) ⊆ S_comp.Ω.interval (b i) (a i) := fun i =>
    ⟨(S_comp.Ω.interval_restrict hY _ _ (hXY (ha i)) (hXY (hb i))).subset.trans inter_subset_left,
      (S_comp.Ω.interval_restrict hY _ _ (hXY (hb i)) (hXY (ha i))).subset.trans inter_subset_left⟩
  have hsep_Q : ∀ i, S'.IsSeparatingOmegaPath (Q i) := by
    intro i
    obtain ⟨G₁, G₂, hsep, hinter, -, h₁, h₂, h₀⟩ := hQs i
    obtain ⟨hs2, hV2⟩ := hcomp.isGraphSeparation_union hsep h₀
    exact S'.isSeparatingOmegaPath_of_separation (hendsQ i) hs2 (hV2.trans hinter)
      ((hint i).1.trans (hΩ ▸ h₁)) ((hint i).2.trans ((hΩ ▸ h₂).trans subset_union_left))
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

private theorem inner_neighborhood_weak_linkage
    {α : Type u}
    {β : Type v}
    {N : Neighborhood α β}
    {X : Set α}
    (hXb : X ⊆ N.Ω.bar)
    (P₀ : Fin X.ncard → Graph α β)
    (hd₀ : Pairwise fun i j => Disjoint V(P₀ i) V(P₀ j))
    (x₀ : Fin X.ncard → α)
    (hx₀ : ∀ (i : Fin X.ncard), x₀ i ∈ X)
    (y₀ : Fin X.ncard → α)
    (hP₀' : ∀ (i : Fin X.ncard), IsFromToPathWithEnds N.G (P₀ i) N.Ω.bar N.Ω₀.bar (x₀ i) (y₀ i))
    (hPV : ∀ (i : Fin X.ncard), V(P₀ i) ∩ N.Ω.bar = {x₀ i})
    (N' : Neighborhood α β) (hΩ : N'.Ω = N.Ω) (hΩ₀ : N'.Ω₀ = N.Ω₀)
    (hP₀le : ∀ (i : Fin X.ncard), P₀ i ≤ N'.G) :
    N'.IsWeaklyLinked X := by
  refine ⟨hΩ.symm ▸ hXb, P₀, fun i => ⟨x₀ i, y₀ i, (hP₀' i).1.of_le (hP₀le i), ?_,
    hΩ₀.symm ▸ (hP₀' i).2.2⟩, hd₀⟩
  apply Subset.antisymm
  · rintro v ⟨hv, hvX⟩
    have : v ∈ V(P₀ i) ∩ N.Ω.bar := ⟨hv, hXb hvX⟩
    rwa [hPV] at this
  · rintro _ rfl
    exact ⟨(hP₀' i).1.left_mem, hx₀ i⟩

/-- `exists_clean_paths` for a nest of `3` circuits (giving `2` clean circuits). -/
private theorem exists_clean_paths_p2 {N : Neighborhood α β} (P_pres : Presentation N)
    {C' : Fin 3 → Graph α β} (hC' : N.IsNest P_pres C') {X : Set α} (hX : N.IsLinked X) :
    ∃ (C : Fin 2 → Graph α β) (P : Fin X.ncard → Graph α β) (x t : Fin X.ncard → α),
      N.IsNest P_pres C ∧ (∀ j, Disjoint V(C j) N.Ω.bar) ∧
      (∀ i, IsFromToPathWithEnds N.G (P i) X N.Ω₀.bar (x i) (t i) ∧ V(P i) ∩ N.Ω.bar = {x i}) ∧
      Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
      ∀ i j, ∃ I, IsGraphPath N.G I ∧ I ≤ P i ∧ I ≤ C j ∧ V(I) = V(P i) ∩ V(C j) := by
  classical
  obtain ⟨hXb, P₀, hP₀, hd₀⟩ := hX
  have hd_bar := disjoint_bar_bar₀_of_isNest hC' (by decide : 2 ≤ 3)
  choose x₀ hx₀ y₀ hy₀ hP₀' using hP₀
  have hPV : ∀ i, V(P₀ i) ∩ N.Ω.bar = {x₀ i} := fun i => (hP₀' i).2.1
  let F : Set β := {e | ∀ a b, N.G.IsLink e a b → a ∉ N.Ω.bar ∧ b ∉ N.Ω.bar} ∪ ⋃ i, E(P₀ i)
  let G' := N.G.restrict F
  have hG' : G' ≤ N.G := Graph.restrict_le
  let N' : Neighborhood α β :=
    { G := G', Ω := N.Ω, Ω₀ := N.Ω₀, finite_V := N.finite_V,
      finite_E := N.finite_E.subset hG'.edgeSet_mono, bar_subset := N.bar_subset,
      bar₀_subset := N.bar₀_subset }
  obtain ⟨P', hPΔ, hPΔ₀, _, hPU⟩ := Presentation.exists_of_le (N' := N') P_pres hG'
    P_pres.isClosedDisc_Δ P_pres.Δ₀_subset_Δ
    ((graphDrawingSubgraphU_subset_U P_pres.Γ _).trans P_pres.U_subset) P_pres.mem_bd_Δ_iff
    P_pres.mem_bd_Δ₀_iff P_pres.agrees_Δ P_pres.agrees_Δ₀
  let C₀ : Fin 2 → Graph α β := fun j => C' j.castSucc
  have hC₀d : ∀ j, Disjoint V(C₀ j) N.Ω.bar := fun j =>
    disjoint_vertexSet_bar_of_isNest_lt hC' (Fin.castSucc_lt_last j)
  have hC₀G : ∀ j, C₀ j ≤ N.G := fun j => (hC'.1 _).1
  have hC₀le : ∀ j, C₀ j ≤ G' := by
    intro j
    refine (Compatible.of_le_le (hC₀G j) hG').le_iff.mpr
      ⟨(hC₀G j).vertexSet_mono, fun e he => ⟨(hC₀G j).edgeSet_mono he, Or.inl ?_⟩⟩
    intro a b hab
    obtain ⟨u, w, hl⟩ : ∃ u w, (C₀ j).IsLink e u w := exists_isLink_of_mem_edgeSet he
    have hlG := hl.mono (hC₀G j)
    have hm : ∀ {z}, z = u ∨ z = w → z ∈ V(C₀ j) := by
      rintro z (rfl | rfl)
      · exact hl.left_mem
      · exact hl.right_mem
    exact ⟨Set.disjoint_left.mp (hC₀d j) (hm (hab.left_eq_or_eq hlG)),
      Set.disjoint_left.mp (hC₀d j) (hm (hab.symm.left_eq_or_eq hlG))⟩
  have hP₀le : ∀ i, P₀ i ≤ G' := by
    intro i
    refine (Compatible.of_le_le (hP₀' i).1.le hG').le_iff.mpr
      ⟨(hP₀' i).1.le.vertexSet_mono, fun e he =>
        ⟨(hP₀' i).1.le.edgeSet_mono he, Or.inr (mem_iUnion.mpr ⟨i, he⟩)⟩⟩
  have hnest : N'.IsNest P' C₀ := by
    obtain ⟨hcir, hdisj, D, hDd, hDs, hDm⟩ := hC'
    refine ⟨fun j => ⟨hC₀le j, (hcir _).2⟩, fun i j hij => hdisj fun e => hij
      (Fin.castSucc_injective _ e), fun j => D j.castSucc, fun j => ⟨(hDd _).1, ?_⟩, fun j => ?_,
      fun i j hij => hDm _ _ (Fin.castSucc_le_castSucc_iff.mpr hij)⟩
    · rw [hPU _ (hC₀le j)]
      exact (hDd _).2
    · rw [hPΔ, hPΔ₀]
      exact hDs _
  have hweak : N'.IsWeaklyLinked X := by
    exact inner_neighborhood_weak_linkage (α := α) (β := β) (N := N) (X := X) hXb P₀ hd₀ x₀ hx₀ y₀
      hP₀' hPV N' rfl rfl hP₀le
  obtain ⟨C, P, hC, hP, hPd, hPC⟩ := GraphMinor.GM09.theorem_10_1_proof P' ⟨C₀, hnest⟩ hweak
  choose x t hP₁ using hP
  have hin : ∀ {e v w}, G'.IsLink e v w → v ∈ N.Ω.bar →
      ∃ i, e ∈ E(P₀ i) ∧ v = x₀ i ∧ (P₀ i).Inc e v := by
    intro e v w hl hv
    have he : e ∈ F := (show e ∈ E(G') from hl.edge_mem).2
    rcases he with he | he
    · exact absurd hv (he v w (hl.mono hG')).1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp he
      obtain ⟨a, b, hab⟩ : ∃ a b, (P₀ i).IsLink e a b := exists_isLink_of_mem_edgeSet hi
      have hlG := hl.mono hG'
      have hvP : v ∈ V(P₀ i) ∧ (P₀ i).Inc e v := by
        rcases hlG.left_eq_or_eq (hab.mono (hP₀' i).1.le) with rfl | rfl
        · exact ⟨hab.left_mem, ⟨_, hab⟩⟩
        · exact ⟨hab.right_mem, ⟨_, hab.symm⟩⟩
      have : v ∈ V(P₀ i) ∩ N.Ω.bar := ⟨hvP.1, hv⟩
      rw [hPV] at this
      exact ⟨i, hi, this, hvP.2⟩
  have huniq : ∀ {e₁ e₂ v w₁ w₂}, G'.IsLink e₁ v w₁ → G'.IsLink e₂ v w₂ → v ∈ N.Ω.bar →
      e₁ = e₂ := by
    intro e₁ e₂ v w₁ w₂ h₁ h₂ hv
    obtain ⟨i₁, he₁, hx₁, hi₁⟩ := hin h₁ hv
    obtain ⟨i₂, he₂, hx₂, hi₂⟩ := hin h₂ hv
    have hi : i₁ = i₂ := by
      by_contra hne
      have hm₂ : v ∈ V(P₀ i₂) := hx₂ ▸ (hP₀' i₂).1.left_mem
      have hm₁ : v ∈ V(P₀ i₁) := hx₁ ▸ (hP₀' i₁).1.left_mem
      exact Set.disjoint_left.mp (hd₀ hne) hm₁ hm₂
    subst hi
    rw [hx₁] at hi₁ hi₂
    exact (hP₀' i₁).1.inc_left_unique he₁ he₂ hi₁ hi₂
  have hCbar : ∀ j, Disjoint V(C j) N.Ω.bar := by
    intro j
    rw [Set.disjoint_left]
    intro v hv hvb
    have hc := hC.1 j
    by_cases h : ∃ v' ∈ V(C j), v ≠ v'
    · obtain ⟨v', hv', hne⟩ := h
      obtain ⟨Q₁, Q₂, -, -, hQ₁, hQ₂, -, -, -, hE, -⟩ := hc.exists_two_paths hv hv' hne
      obtain ⟨e₁, he₁, w₁, hl₁⟩ := hQ₁.exists_inc_of_mem_of_ne hne hQ₁.left_mem
      obtain ⟨e₂, he₂, w₂, hl₂⟩ := hQ₂.exists_inc_of_mem_of_ne hne hQ₂.left_mem
      have e' := huniq (hl₁.mono hQ₁.le) (hl₂.mono hQ₂.le) hvb
      exact Set.disjoint_left.mp hE he₁ (e' ▸ he₂)
    · push Not at h
      obtain ⟨e, he⟩ := hc.edgeSet_nonempty
      obtain ⟨u, w, hl⟩ : ∃ u w, (C j).IsLink e u w := exists_isLink_of_mem_edgeSet he
      obtain rfl := (h u hl.left_mem).symm
      obtain rfl := (h w hl.right_mem).symm
      obtain ⟨i, hi, -, -⟩ := hin (hl.mono hc.1) hvb
      exact (hP₀' i).1.not_isLoopAt hi _ ((hl.mono hc.1).mono hG')
  have hPbar : ∀ i, V(P i) ∩ N.Ω.bar = {x i} := by
    intro i
    obtain ⟨hpath, hVX, hV₀⟩ := hP₁ i
    have hxX : x i ∈ X := (hVX.symm ▸ mem_singleton _ : x i ∈ V(P i) ∩ X).2
    have ht₀ : t i ∈ N.Ω₀.bar := (hV₀.symm ▸ mem_singleton _ : t i ∈ V(P i) ∩ N'.Ω₀.bar).2
    apply Subset.antisymm
    · rintro w ⟨hw, hwb⟩
      by_contra hne
      have hne' : x i ≠ w := fun e => hne e.symm
      have hwt : w ≠ t i := fun e =>
        Set.disjoint_left.mp hd_bar hwb (e.symm ▸ ht₀)
      obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hp₁, hp₂, -, -, hE⟩ := hpath.exists_split_at hw
      obtain ⟨e₁, he₁, w₁, hl₁⟩ := hp₁.exists_inc_of_mem_of_ne hne' hp₁.right_mem
      obtain ⟨e₂, he₂, w₂, hl₂⟩ := hp₂.exists_inc_of_mem_of_ne hwt hp₂.left_mem
      have hle₁ : Q₁ ≤ G' := hQ₁.trans hpath.le
      have hle₂ : Q₂ ≤ G' := hQ₂.trans hpath.le
      have e' := huniq (hl₁.mono hle₁) (hl₂.mono hle₂) hwb
      exact Set.disjoint_left.mp hE he₁ (e' ▸ he₂)
    · rintro _ rfl
      exact ⟨hpath.left_mem, hXb hxX⟩
  refine ⟨C, P, x, t, ?_, hCbar, fun i => ⟨?_, hPbar i⟩, hPd, fun i j => ?_⟩
  · obtain ⟨hcir, hdisj, D, hDd, hDs, hDm⟩ := hC
    refine ⟨fun j => ⟨(hcir j).1.trans hG', (hcir j).2⟩, hdisj, D, fun j => ⟨(hDd j).1, ?_⟩,
      fun j => ?_, hDm⟩
    · rw [← hPU _ (hcir j).1]
      exact (hDd j).2
    · rw [← hPΔ, ← hPΔ₀]
      exact hDs j
  · obtain ⟨hpath, hVX, hV₀⟩ := hP₁ i
    exact ⟨hpath.mono hG', hVX, hV₀⟩
  · obtain ⟨u, w, hI⟩ := hPC i j
    have hle₁ : P i ≤ G' := (hP₁ i).1.le
    have hle₂ : C j ≤ G' := (hC.1 j).1
    exact ⟨_, ⟨u, w, hI.mono hG'⟩, subgraphInter_le_left hle₁ hle₂,
      subgraphInter_le_right hle₁ hle₂,
      vertexSet_subgraphInter _ _ _⟩

private theorem outer_perimeter_contains_boundary
    {α : Type u}
    {β : Type v}
    {N : Neighborhood α β}
    (P_pres : Presentation N)
    (C : Fin 2 → Graph α β)
    (hCbar : ∀ (j : Fin 2), Disjoint V(C j) N.Ω.bar)
    (last : Fin 2)
    (D : Fin 2 → Set EuclideanPlane)
    (hDs : ∀ (i : Fin 2), P_pres.Δ₀ ⊆ D i ∧ D i ⊆ P_pres.Δ)
    (H₂ : Graph α β)
    (hY₂ : ∀ v ∈ V(N.G), graphDrawingVertexSet P_pres.Γ v ⊆ P_pres.Δ \ D last → v ∈ V(H₂))
    (hpt : ∀ v ∈ V(N.G), ∃ q, graphDrawingVertexSet P_pres.Γ v = {q})
    (hbdK : ∀ v ∈ V(N.G), graphDrawingVertexSet P_pres.Γ v ⊆ subBd (D last) ↔ v ∈ V(C last)) :
    N.Ω.bar ⊆ V(H₂) := by
  intro v hv
  have hvG := N.bar_subset hv
  obtain ⟨q, hq⟩ := hpt v hvG
  refine hY₂ v hvG ?_
  rw [hq, singleton_subset_iff]
  have hb := (P_pres.mem_bd_Δ_iff v hvG).mpr hv
  have hqm : q ∈ graphDrawingVertexSet P_pres.Γ v := hq ▸ mem_singleton q
  refine ⟨GM09.subBd_subset_of_isClosed (isClosed_of_isClosedDisc P_pres.isClosedDisc_Δ) (hb hqm),
    fun hqD => ?_⟩
  have : graphDrawingVertexSet P_pres.Γ v ⊆ subBd (D last) := by
    rw [hq, singleton_subset_iff]
    refine inter_subBd_subset_subBd (hDs last).2 ⟨hqD, hb hqm⟩
  exact Set.disjoint_left.mp (hCbar last) ((hbdK v hvG).mp this) hv

private theorem inner_perimeter_contains_boundary
    {α : Type u}
    {β : Type v}
    {N : Neighborhood α β}
    (P_pres : Presentation N)
    (C : Fin 2 → Graph α β)
    (last : Fin 2)
    (D : Fin 2 → Set EuclideanPlane)
    (hDs : ∀ (i : Fin 2), P_pres.Δ₀ ⊆ D i ∧ D i ⊆ P_pres.Δ)
    (H₁ : Graph α β)
    (hKH₁ : C last ≤ H₁)
    (hY₁ : ∀ v ∈ V(N.G), graphDrawingVertexSet P_pres.Γ v ⊆ D last \ subBd (D last) → v ∈ V(H₁))
    (hpt : ∀ v ∈ V(N.G), ∃ q, graphDrawingVertexSet P_pres.Γ v = {q})
    (hbdK : ∀ v ∈ V(N.G), graphDrawingVertexSet P_pres.Γ v ⊆ subBd (D last) ↔ v ∈ V(C last)) :
    N.Ω₀.bar ⊆ V(H₁) := by
  intro v hv
  have hvG := N.bar₀_subset hv
  by_cases hvK : v ∈ V(C last)
  · exact hKH₁.vertexSet_mono hvK
  obtain ⟨q, hq⟩ := hpt v hvG
  refine hY₁ v hvG ?_
  rw [hq, singleton_subset_iff]
  have hq' : q = _ :=
    (singleton_injective ((graphDrawingVertexSet_eq_singleton P_pres.Γ hvG).symm.trans hq)).symm
  refine ⟨(hDs last).1 (hq' ▸ (isClosedDisc_Δ₀_and_mem_of_mem_bar₀ P_pres hv).2),
    fun hb => hvK ?_⟩
  exact (hbdK v hvG).mp (by rw [hq, singleton_subset_iff]; exact hb)

private theorem nested_circuits_lie_inside
    {α : Type u}
    {β : Type v}
    {N : Neighborhood α β}
    (P_pres : Presentation N)
    (C : Fin 2 → Graph α β)
    (hcir : ∀ (i : Fin 2), IsGraphCircuit N.G (C i))
    (hdisj : Pairwise fun i j => Disjoint V(C i) V(C j))
    (D : Fin 2 → Set EuclideanPlane)
    (hDd : ∀ (i : Fin 2), IsClosedDisc (D i) ∧ subBd (D i) = graphDrawingSubgraphU P_pres.Γ (C i))
    (hDm : ∀ (i j : Fin 2), i ≤ j → D i ⊆ D j)
    (H₁ : Graph α β)
    (H₂ : Graph α β)
    (hsep : IsGraphSeparation N.G H₁ H₂)
    (hcut : V(H₁) ∩ V(H₂) = V(C (1 : Fin 2)))
    (hKH₁ : C (1 : Fin 2) ≤ H₁)
    (hY₁ : ∀ v ∈ V(N.G),
      graphDrawingVertexSet P_pres.Γ v ⊆ D (1 : Fin 2) \ subBd (D (1 : Fin 2)) → v ∈ V(H₁))
    (hpt : ∀ v ∈ V(N.G), ∃ q, graphDrawingVertexSet P_pres.Γ v = {q})
    (hbdK : ∀ v ∈ V(N.G),
      graphDrawingVertexSet P_pres.Γ v ⊆ subBd (D (1 : Fin 2)) ↔ v ∈ V(C (1 : Fin 2))) :
    ∀ (j : Fin 2), C j ≤ H₁ := by
  let last : Fin 2 := 1
  intro j
  by_cases hj : j = last
  · subst hj
    exact hKH₁
  refine IsGraphSeparation.le_left_of_disjoint hsep (hcir j).1 (Set.disjoint_left.mpr ?_)
  intro v hv hv₂
  have hvG := (hcir j).1.vertexSet_mono hv
  have hnK : v ∉ V(C last) := fun h => Set.disjoint_left.mp (hdisj hj) hv h
  have hv₁ : v ∈ V(H₁) := by
    obtain ⟨q, hq⟩ := hpt v hvG
    refine hY₁ v hvG ?_
    have hqm : q ∈ graphDrawingVertexSet P_pres.Γ v := hq ▸ mem_singleton q
    have hjle : j ≤ last := by
      have hjlt : j.1 < 2 := j.2
      exact Fin.mk_le_mk.mpr (by change j.1 ≤ 1; omega)
    have hqD : q ∈ D last := by
      refine hDm j last hjle (GM09.subBd_subset_of_isClosed (isClosed_of_isClosedDisc
        (hDd j).1) ?_)
      rw [(hDd j).2]
      exact graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hv hqm
    rw [hq, singleton_subset_iff]
    refine ⟨hqD, fun hb => hnK ((hbdK v hvG).mp ?_)⟩
    rw [hq, singleton_subset_iff]
    exact hb
  exact hnK (hcut ▸ ⟨hv₁, hv₂⟩)

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

private theorem transaction_path_extension
    {α : Type u}
    {β : Type v}
    {S_comp : Society α β}
    {X : Set α}
    (x : Fin X.ncard → α)
    (y : Fin X.ncard → α)
    (R : Fin X.ncard → Graph α β)
    (hy_inj : Injective y)
    (hRd : ∀ {i j : Fin X.ncard}, i ≠ j → Disjoint V(R i) V(R j))
    (S₁ : Society α β) (hS₁S : S₁.G ≤ S_comp.G)
    (T : Set (Graph α β))
    (hT : S₁.IsCrookedTransaction T)
    (hS₁T : ∀ Q ∈ T, Q ≤ S₁.G)
    (hRSN : ∀ (i : Fin X.ncard), IsGraphPathWithEnds S_comp.G (R i) (x i) (y i))
    (hRV : ∀ {Q : Graph α β} {i : Fin X.ncard}, Q ≤ S₁.G → y i ∈ V(Q) → V(R i) ∩ V(Q) = {y i})
    (hTY : ∀ {Q : Graph α β} {a b : α}, Q ∈ T → S₁.IsOmegaPathWithEnds Q a b → ∃ i j, a = y i ∧ b
      = y j ∧ i ≠ j) :
    ∀ Q ∈ T, ∃ Qe, ∀ (i j : Fin X.ncard), S₁.IsOmegaPathWithEnds Q (y i) (y j) →
      IsGraphPathWithEnds S_comp.G Qe (x i) (x j) ∧ V(Qe) = V(R i) ∪ V(Q) ∪ V(R j) := by
  intro Q hQ
  obtain ⟨A, B, hf⟩ := hT.1
  obtain ⟨a, -, b, -, hQp⟩ := hf.2.2 Q hQ
  obtain ⟨i₀, j₀, rfl, rfl, hne⟩ := hTY hQ hQp
  have hQS : Q ≤ S₁.G := hS₁T Q hQ
  have hpS : IsGraphPathWithEnds S_comp.G Q (y i₀) (y j₀) :=
    hQp.1.mono hS₁S
  obtain ⟨Qe, hQe, hVQ⟩ := exists_extended_path hpS (hRSN i₀) (hRSN j₀)
    (hRV hQS hQp.1.left_mem) (hRV hQS hQp.1.right_mem) (hRd hne)
  refine ⟨Qe, fun i j hij => ?_⟩
  rcases Society.IsOmegaPathWithEnds.ends_eq S₁ hQp hij with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · obtain rfl := hy_inj e₁
    obtain rfl := hy_inj e₂
    exact ⟨hQe, hVQ⟩
  · obtain rfl := hy_inj e₁
    obtain rfl := hy_inj e₂
    refine ⟨hQe.symm, ?_⟩
    rw [hVQ]
    ext v
    simp only [mem_union]
    tauto

private theorem extensions_pairwise_disjoint
    {α : Type u}
    {β : Type v}
    {S_comp : Society α β}
    {X : Set α}
    (x : Fin X.ncard → α)
    (y : Fin X.ncard → α)
    (R : Fin X.ncard → Graph α β)
    (hRd : ∀ {i j : Fin X.ncard}, i ≠ j → Disjoint V(R i) V(R j))
    (S₁ : Society α β)
    (T : Set (Graph α β))
    (hT : S₁.IsCrookedTransaction T)
    (hTY : ∀ {Q : Graph α β} {a b : α}, Q ∈ T → S₁.IsOmegaPathWithEnds Q a b → ∃ i j, a = y i ∧ b
      = y j ∧ i ≠ j)
    (f : Graph α β → Graph α β)
    (hf : ∀ Q ∈ T, ∀ (i j : Fin X.ncard), S₁.IsOmegaPathWithEnds Q (y i) (y j) →
      IsGraphPathWithEnds S_comp.G (f Q) (x i) (x j) ∧ V(f Q) = V(R i) ∪ V(Q) ∪ V(R j))
    (hTdisj : ∀ {Q Q' : Graph α β}, Q ∈ T → Q' ∈ T → Q ≠ Q' → Disjoint V(Q) V(Q'))
    (hRQ : ∀ {Q Q' : Graph α β} {i j : Fin X.ncard}, Q ∈ T → Q' ∈ T → Q ≠ Q' →
      S₁.IsOmegaPathWithEnds Q (y i) (y j) → Disjoint V(R i) V(Q')) :
    ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → Disjoint V(f Q) V(f Q') := by
  intro Q hQ Q' hQ' hne
  obtain ⟨A, B, hfence⟩ := hT.1
  obtain ⟨a, -, b, -, hQp⟩ := hfence.2.2 Q hQ
  obtain ⟨a', -, b', -, hQ'p⟩ := hfence.2.2 Q' hQ'
  obtain ⟨i, j, rfl, rfl, -⟩ := hTY hQ hQp
  obtain ⟨i', j', rfl, rfl, -⟩ := hTY hQ' hQ'p
  rw [(hf Q hQ i j hQp).2, (hf Q' hQ' i' j' hQ'p).2]
  have hdQ := hTdisj hQ hQ' hne
  have h₁ := hRQ hQ hQ' hne hQp
  have h₂ := hRQ hQ hQ' hne (Society.IsOmegaPathWithEnds.symm S₁ hQp)
  have h₃ := hRQ hQ' hQ hne.symm hQ'p
  have h₄ := hRQ hQ' hQ hne.symm (Society.IsOmegaPathWithEnds.symm S₁ hQ'p)
  have hne' : ∀ {u w}, y u ∈ V(Q) → y w ∈ V(Q') → u ≠ w := by
    rintro u w hu hw rfl
    exact Set.disjoint_left.mp hdQ hu hw
  have hu₁ := hQp.1.left_mem
  have hu₂ := hQp.1.right_mem
  have hw₁ := hQ'p.1.left_mem
  have hw₂ := hQ'p.1.right_mem
  rw [Set.disjoint_left]
  rintro v ((h | h) | h) ((h' | h') | h')
  · exact Set.disjoint_left.mp (hRd (hne' hu₁ hw₁)) h h'
  · exact Set.disjoint_left.mp h₁ h h'
  · exact Set.disjoint_left.mp (hRd (hne' hu₁ hw₂)) h h'
  · exact Set.disjoint_left.mp h₃ h' h
  · exact Set.disjoint_left.mp hdQ h h'
  · exact Set.disjoint_left.mp h₄ h' h
  · exact Set.disjoint_left.mp (hRd (hne' hu₂ hw₁)) h h'
  · exact Set.disjoint_left.mp h₂ h h'
  · exact Set.disjoint_left.mp (hRd (hne' hu₂ hw₂)) h h'

private theorem extended_transaction_is_crooked
    {α : Type u}
    {β : Type v}
    {S_comp : Society α β}
    {X : Set α}
    (x : Fin X.ncard → α)
    (N₂ : Neighborhood α β) (hΩ : N₂.Ω = S_comp.Ω)
    (hrural₂ : N₂.IsRural)
    (y : Fin X.ncard → α)
    (R : Fin X.ncard → Graph α β)
    (hyK : ∀ (i : Fin X.ncard), y i ∈ N₂.Ω₀.bar)
    (hR : ∀ (i : Fin X.ncard), IsGraphPathWithEnds N₂.G (R i) (x i) (y i))
    (hx_inj : Injective x)
    (hRd : ∀ {i j : Fin X.ncard}, i ≠ j → Disjoint V(R i) V(R j))
    (S₁ : Society α β) (hΩ₀ : N₂.Ω₀ = S₁.Ω)
    (T : Set (Graph α β))
    (hT : S₁.IsCrookedTransaction T)
    (hTends : S₁.transactionEnds T ⊆ range y)
    (ψ : α → α)
    (hψ : ∀ (i : Fin X.ncard), ψ (y i) = x i)
    (hTY : ∀ {Q : Graph α β} {a b : α}, Q ∈ T → S₁.IsOmegaPathWithEnds Q a b → ∃ i j, a = y i ∧ b
      = y j ∧ i ≠ j)
    (f : Graph α β → Graph α β)
    (hxb : ∀ (i : Fin X.ncard), x i ∈ S_comp.Ω.bar)
    (hendsT : ∀ Q ∈ T, ∀ (i j : Fin X.ncard), S₁.IsOmegaPathWithEnds Q (y i) (y j) →
      S_comp.IsOmegaPathWithEnds (f Q) (x i) (x j))
    (hd : ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → Disjoint V(f Q) V(f Q')) :
    S_comp.IsCrookedTransaction (f '' T) := by
  refine Society.isCrookedTransaction_image (ψ := ψ) hT ?_ hd ?_ ?_
  · intro Q hQ a b hab
    obtain ⟨i, j, rfl, rfl, -⟩ := hTY hQ hab
    rw [hψ, hψ]
    exact hendsT Q hQ i j hab
  · intro a ha b hb e
    obtain ⟨i, rfl⟩ := hTends ha
    obtain ⟨j, rfl⟩ := hTends hb
    rw [hψ, hψ] at e
    exact congrArg y (hx_inj e)
  · intro a ha b hb c hc d' hd' h12 h13 h14 h23 h24 h34
    obtain ⟨i₁, rfl⟩ := hTends ha
    obtain ⟨i₂, rfl⟩ := hTends hb
    obtain ⟨i₃, rfl⟩ := hTends hc
    obtain ⟨i₄, rfl⟩ := hTends hd'
    have hne : ∀ {u w}, y u ≠ y w → u ≠ w := fun h e => h (congrArg y e)
    have hN (k : Fin X.ncard) : x k ∈ N₂.Ω.bar := hΩ.symm ▸ hxb k
    have h := crosses_outer_iff_crosses_inner_of_disjoint_paths hrural₂ (hR i₁) (hN i₁) (hyK i₁)
      (hR i₃) (hN i₃) (hyK i₃) (hR i₂) (hN i₂) (hyK i₂) (hR i₄) (hN i₄) (hyK i₄)
      (hRd (hne h13)) (hRd (hne h12)) (hRd (hne h14)) (hRd (hne h23.symm)) (hRd (hne h34))
      (hRd (hne h24))
    rw [hψ, hψ, hψ, hψ]
    rw [hΩ, hΩ₀] at h
    exact h.symm

private theorem inner_society_composition
    {α : Type u}
    {β : Type v}
    {S_comp : Society α β}
    {S₀ : Society α β}
    {N : Neighborhood α β}
    (hcomp : S_comp.IsComposition S₀ N)
    (C : Fin 2 → Graph α β)
    (last : Fin 2)
    (H₁ : Graph α β)
    (H₂ : Graph α β)
    (hsep : IsGraphSeparation N.G H₁ H₂)
    (hKH₁ : C last ≤ H₁)
    (hbar₀H₁ : N.Ω₀.bar ⊆ V(H₁))
    (Ω₁ : CyclicPerm α)
    (hΩ₁ : Ω₁.bar = V(C last))
    (N₁ : Neighborhood α β)
    (hH₁S : H₁ ≤ S_comp.G)
    (hS₀S : S₀.G ≤ S_comp.G)
    (S₁ : Society α β) (hG₁ : S₁.G = subgraphUnion S_comp.G H₁ S₀.G)
    (hN₁ : N₁.G = H₁) (hN₁Ω : N₁.Ω = Ω₁) (hN₁Ω₀ : N₁.Ω₀ = N.Ω₀)
    (hS₁Ω : S₁.Ω = Ω₁) :
    S₁.IsComposition S₀ N₁ := by
  obtain ⟨⟨hs₀, -⟩, -, hΩ₀, hbar₀⟩ := hcomp
  have hUle₀ : S₀.G ≤ S₁.G := hG₁.symm ▸ le_subgraphUnion_right hH₁S hS₀S
  have hUle₁ : H₁ ≤ S₁.G := hG₁.symm ▸ le_subgraphUnion_left hH₁S hS₀S
  refine ⟨⟨⟨hUle₀, hN₁.symm ▸ hUle₁, ?_, ?_, ?_⟩, ?_⟩,
    hN₁Ω.trans hS₁Ω.symm, hN₁Ω₀.trans hΩ₀, ?_⟩
  · rw [hG₁, hN₁]
    change V(S₀.G) ∪ V(H₁) = V(H₁) ∪ V(S₀.G)
    exact union_comm _ _
  · rw [hG₁, hN₁, edgeSet_subgraphUnion hH₁S hS₀S]
    exact union_comm _ _
  · rw [hN₁]
    exact hs₀.2.2.2.2.mono_right hsep.1.edgeSet_mono
  · rw [hS₁Ω, hN₁]
    exact hΩ₁.subset.trans hKH₁.vertexSet_mono
  · rw [hN₁]
    apply Subset.antisymm
    · intro v hv
      refine ⟨S₀.bar_subset hv, hbar₀H₁ ?_⟩
      rw [hΩ₀]
      exact hv
    · rintro v ⟨hv₀, hv₁⟩
      rw [hbar₀]
      exact ⟨hv₀, hsep.1.vertexSet_mono hv₁⟩

private theorem perimeter_drawing_agrees_with_circle
    {α : Type u}
    {β : Type v}
    {N : Neighborhood α β}
    (Γ : GraphDrawing N.G EuclideanPlane) (last : Fin 2)
    (D : Fin 2 → Set EuclideanPlane)
    (φ : Circle ≃ₜ ↑(subBd (D last)))
    (ν : α → EuclideanPlane)
    (hν : ∀ v ∈ V(N.G), graphDrawingVertexSet Γ v = {ν v})
    (Ω₁ : CyclicPerm α)
    (hagK : AgreesWithOArcHomeo ν Ω₁ (subBd (D last)) φ)
    (hbarK : ∀ {v : α}, v ∈ Ω₁.bar → v ∈ V(N.G)) :
    DrawingAgreesWithOArcHomeo Γ Ω₁ (subBd (D last)) φ := by
  refine ⟨fun v hv => ?_, fun v₁ v₂ v₃ hc => ?_⟩
  · rw [hν v (hbarK hv), singleton_subset_iff]
    exact hagK.1 v hv
  · have hm := CyclicPerm.isClockwise3_iff.mp hc
    obtain ⟨t₁, t₂, t₃, h₁, h₂, h₃, e₁, e₂, e₃⟩ := hagK.2 v₁ v₂ v₃ hc
    refine ⟨t₁, t₂, t₃, h₁, h₂, h₃, ?_, ?_, ?_⟩
    · rw [hν v₁ (hbarK hm.2.2.2.1), e₁]
      rfl
    · rw [hν v₂ (hbarK hm.2.2.2.2.1), e₂]
      rfl
    · rw [hν v₃ (hbarK hm.2.2.2.2.2.1), e₃]
      rfl

private theorem inner_presentation_has_nested_circuits
    {α : Type u}
    {β : Type v}
    {N : Neighborhood α β}
    (P_pres : Presentation N)
    (C : Fin 2 → Graph α β)
    (hcir : ∀ (i : Fin 2), IsGraphCircuit N.G (C i))
    (hdisj : Pairwise fun i j => Disjoint V(C i) V(C j))
    (D : Fin 2 → Set EuclideanPlane)
    (hDd : ∀ (i : Fin 2), IsClosedDisc (D i) ∧ subBd (D i) = graphDrawingSubgraphU P_pres.Γ (C i))
    (hDs : ∀ (i : Fin 2), P_pres.Δ₀ ⊆ D i ∧ D i ⊆ P_pres.Δ)
    (hDm : ∀ (i j : Fin 2), i ≤ j → D i ⊆ D j)
    (N₁ : Neighborhood α β) (hCH₁ : ∀ j, C j ≤ N₁.G)
    (P₁ : Presentation N₁)
    (hP₁Δ : P₁.Δ = D (1 : Fin 2))
    (hP₁Δ₀ : P₁.Δ₀ = P_pres.Δ₀)
    (hP₁U : ∀ R ≤ N₁.G, graphDrawingSubgraphU P₁.Γ R = graphDrawingSubgraphU P_pres.Γ R) :
    N₁.IsNest P₁ C := by
  refine ⟨fun j => ⟨hCH₁ j, (hcir j).2⟩, hdisj, D, fun j => ⟨(hDd j).1, ?_⟩, fun j => ?_, hDm⟩
  · rw [hP₁U _ (hCH₁ j)]
    exact (hDd j).2
  · rw [hP₁Δ, hP₁Δ₀]
    have hjlt : j.1 < 2 := j.2
    exact ⟨(hDs j).1, hDm j 1 (Fin.mk_le_mk.mpr (by change j.1 ≤ 1; omega))⟩

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

private theorem extended_transaction_preserves_size_and_endpoints
    {α : Type u}
    {β : Type v}
    {S_comp : Society α β}
    {N : Neighborhood α β}
    {X : Set α}
    (C : Fin 2 → Graph α β)
    (P : Fin X.ncard → Graph α β)
    (x : Fin X.ncard → α)
    (t : Fin X.ncard → α)
    (hCbar : ∀ (j : Fin 2), Disjoint V(C j) N.Ω.bar)
    (hP : ∀ (i : Fin X.ncard), IsFromToPathWithEnds N.G (P i) X N.Ω₀.bar (x i) (t i) ∧ V(P i) ∩
      N.Ω.bar = {x i})
    (hΩ : N.Ω = S_comp.Ω)
    (last : Fin 2)
    (H₂ : Graph α β)
    (hbarH₂ : N.Ω.bar ⊆ V(H₂))
    (y : Fin X.ncard → α)
    (R : Fin X.ncard → Graph α β)
    (hRP : ∀ (i : Fin X.ncard), V(R i) ⊆ V(P i))
    (S₁ : Society α β)
    (hcutU : V(H₂) ∩ V(S₁.G) = V(C last))
    (T : Set (Graph α β))
    (hT : S₁.IsCrookedTransaction T)
    (hpT : T.ncard = 2)
    (hS₁T : ∀ Q ∈ T, Q ≤ S₁.G)
    (hTY : ∀ {Q : Graph α β} {a b : α}, Q ∈ T → S₁.IsOmegaPathWithEnds Q a b → ∃ i j, a = y i ∧ b
      = y j ∧ i ≠ j)
    (f : Graph α β → Graph α β)
    (hf : ∀ Q ∈ T, ∀ (i j : Fin X.ncard), S₁.IsOmegaPathWithEnds Q (y i) (y j) →
      IsGraphPathWithEnds S_comp.G (f Q) (x i) (x j) ∧ V(f Q) = V(R i) ∪ V(Q) ∪ V(R j))
    (hendsT : ∀ Q ∈ T, ∀ (i j : Fin X.ncard), S₁.IsOmegaPathWithEnds Q (y i) (y j) →
      S_comp.IsOmegaPathWithEnds (f Q) (x i) (x j))
    (hd : ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → Disjoint V(f Q) V(f Q'))
    (hcrook : S_comp.IsCrookedTransaction (f '' T)) :
    ∃ P', S_comp.IsCrookedTransaction P' ∧ P'.ncard = 2 ∧ S_comp.transactionEnds P' ⊆ X ∧ ∀ P ∈
      P', Disjoint (pathInternalVerts S_comp.G P) S_comp.Ω.bar := by
  have hnonempty : ∀ Q ∈ T, V(f Q).Nonempty := by
    intro Q hQ
    obtain ⟨A, B, hfence⟩ := hT.1
    obtain ⟨a, -, b, -, hQp⟩ := hfence.2.2 Q hQ
    obtain ⟨i, j, rfl, rfl, -⟩ := hTY hQ hQp
    exact ⟨_, (hf Q hQ i j hQp).1.left_mem⟩
  have hinjf : InjOn f T := by
    intro Q hQ Q' hQ' e
    by_contra hne
    obtain ⟨v, hv⟩ := hnonempty Q hQ
    exact Set.disjoint_left.mp (hd Q hQ Q' hQ' hne) hv (e ▸ hv)
  refine ⟨f '' T, hcrook, ?_, ?_, ?_⟩
  · rw [hinjf.ncard_image]
    exact hpT
  · rintro v ⟨_, ⟨Q, hQ, rfl⟩, b, hvb⟩
    obtain ⟨A, B, hfence⟩ := hT.1
    obtain ⟨a', -, b', -, hQp⟩ := hfence.2.2 Q hQ
    obtain ⟨i, j, rfl, rfl, -⟩ := hTY hQ hQp
    have hxX : ∀ k, x k ∈ X := fun k =>
      ((hP k).1.2.1.symm ▸ mem_singleton _ : x k ∈ V(P k) ∩ X).2
    rcases Society.IsOmegaPathWithEnds.ends_eq S_comp (hendsT Q hQ i j hQp) hvb with ⟨e, -⟩ | ⟨e, -⟩
    · exact e ▸ hxX i
    · exact e ▸ hxX j
  · rintro _ ⟨Q, hQ, rfl⟩
    rw [Set.disjoint_left]
    rintro v ⟨hv, hvE⟩ hvb
    obtain ⟨A, B, hfence⟩ := hT.1
    obtain ⟨a', -, b', -, hQp⟩ := hfence.2.2 Q hQ
    obtain ⟨i, j, rfl, rfl, -⟩ := hTY hQ hQp
    obtain ⟨hpath, hVe⟩ := hf Q hQ i j hQp
    have hend : ∀ {k}, v ∈ V(R k) → v = x k := by
      intro k hk
      have : v ∈ V(P k) ∩ N.Ω.bar := ⟨hRP k hk, hΩ ▸ hvb⟩
      rwa [(hP k).2] at this
    rw [hVe] at hv
    rcases hv with (h | h) | h
    · exact hvE ⟨_, hend h ▸ hpath⟩
    · have hK : v ∈ V(H₂) ∩ V(S₁.G) := ⟨hbarH₂ (hΩ ▸ hvb), (hS₁T Q hQ).vertexSet_mono h⟩
      rw [hcutU] at hK
      exact Set.disjoint_left.mp (hCbar last) hK (hΩ ▸ hvb)
    · exact hvE ⟨_, hend h ▸ hpath.symm⟩

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
  let Γ := P_pres.Γ
  have hKG : C last ≤ N.G := (hcir last).1
  have hUΔ : Γ.drawing.U ⊆ P_pres.Δ := P_pres.U_subset.trans sdiff_subset
  obtain ⟨H₁, H₂, hsep, hcut, hKH₁, hY₁, hY₂, hUH₁, hUH₂⟩ := exists_separation_of_disc Γ
    (isClosed_of_isClosedDisc P_pres.isClosedDisc_Δ) hUΔ hKG (hDd last).1 (hDs last).2 (hDd last).2
  have hpt : ∀ v ∈ V(N.G), ∃ q, graphDrawingVertexSet Γ v = {q} := fun v hv =>
    ⟨_, graphDrawingVertexSet_eq_singleton Γ hv⟩
  have hbdK : ∀ v ∈ V(N.G), (graphDrawingVertexSet Γ v ⊆ subBd (D last) ↔ v ∈ V(C last)) := by
    intro v hv
    rw [(hDd last).2]
    exact ⟨mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU Γ hKG hv,
      graphDrawingVertexSet_subset_subgraphU_of_mem Γ⟩
  have hK₂ : V(C last) ⊆ V(H₂) := fun v hv => (hcut.symm ▸ hv : v ∈ V(H₁) ∩ V(H₂)).2
  have hbarH₂ : N.Ω.bar ⊆ V(H₂) := by
    exact outer_perimeter_contains_boundary (α := α) (β := β) (N := N) P_pres C hCbar last D hDs
      H₂ hY₂ hpt hbdK
  have hbar₀H₁ : N.Ω₀.bar ⊆ V(H₁) := by
    exact inner_perimeter_contains_boundary (α := α) (β := β) (N := N) P_pres C last D hDs H₁
      hKH₁ hY₁ hpt hbdK
  have hCH₁ : ∀ j, C j ≤ H₁ := by
    exact nested_circuits_lie_inside (α := α) (β := β) (N := N) P_pres C
      hcir hdisj D hDd hDm H₁ H₂ hsep hcut hKH₁ hY₁ hpt hbdK
  have hKne : V(C last).Nonempty := by
    obtain ⟨e, he⟩ := (hcir last).edgeSet_nonempty
    obtain ⟨u, w, hl⟩ : ∃ u w, (C last).IsLink e u w := exists_isLink_of_mem_edgeSet he
    exact ⟨u, hl.left_mem⟩
  have hKfin : V(C last).Finite := N.finite_V.subset hKG.vertexSet_mono
  obtain ⟨φ, hφ_cw⟩ := exists_isClockwiseDiscHomeo (hDd last).1
  let ν : α → EuclideanPlane := fun v =>
    if h : v ∈ V(N.G) then (Γ.iso.vertexEquiv ⟨v, h⟩).1 else 0
  have hν : ∀ v (h : v ∈ V(N.G)), graphDrawingVertexSet Γ v = {ν v} := by
    intro v h
    rw [graphDrawingVertexSet_eq_singleton Γ h]
    simp only [ν, h, ↓reduceDIte]
  obtain ⟨Ω₁, hΩ₁, hagK⟩ := exists_cyclicPerm_agrees_of_injOn φ ν hKfin hKne
    (fun u hu w hw e => graphDrawingVertexSet_inj Γ (x := ν u)
      (by rw [hν u (hKG.vertexSet_mono hu)]; rfl)
      (by rw [hν w (hKG.vertexSet_mono hw), e]; rfl))
    (fun v hv => by
      have := (hbdK v (hKG.vertexSet_mono hv)).mpr hv
      rw [hν v (hKG.vertexSet_mono hv), singleton_subset_iff] at this
      exact this)
  have hbarK : ∀ {v}, v ∈ Ω₁.bar → v ∈ V(N.G) := fun hv =>
    hKG.vertexSet_mono (hΩ₁ ▸ hv)
  have hag : DrawingAgreesWithOArcHomeo Γ Ω₁ (subBd (D last)) φ := by
    exact perimeter_drawing_agrees_with_circle (α := α) (β := β) (N := N) Γ last D φ ν hν Ω₁ hagK
      hbarK
  let N₁ : Neighborhood α β :=
    { G := H₁, Ω := Ω₁, Ω₀ := N.Ω₀, finite_V := N.finite_V.subset hsep.1.vertexSet_mono,
      finite_E := N.finite_E.subset hsep.1.edgeSet_mono,
      bar_subset := hΩ₁.subset.trans hKH₁.vertexSet_mono, bar₀_subset := hbar₀H₁ }
  let N₂ : Neighborhood α β :=
    { G := H₂, Ω := N.Ω, Ω₀ := Ω₁, finite_V := N.finite_V.subset hsep.2.1.vertexSet_mono,
      finite_E := N.finite_E.subset hsep.2.1.edgeSet_mono, bar_subset := hbarH₂,
      bar₀_subset := hΩ₁.subset.trans hK₂ }
  have hbdΩ₁ : ∀ G' : Graph α β, G' ≤ N.G → ∀ v ∈ V(G'),
      (graphDrawingVertexSet Γ v ⊆ subBd (D last) ↔ v ∈ Ω₁.bar) := by
    intro G' hG' v hv
    rw [hΩ₁]
    exact hbdK v (hG'.vertexSet_mono hv)
  obtain ⟨P₁, hP₁Δ, hP₁Δ₀, -, hP₁U⟩ := Presentation.exists_of_le (N' := N₁) P_pres hsep.1
    (hDd last).1 (hDs last).1
    (fun q hq => ⟨hUH₁ hq, (P_pres.U_subset (graphDrawingSubgraphU_subset_U Γ _ hq)).2⟩)
    (hbdΩ₁ H₁ hsep.1) (fun v hv => P_pres.mem_bd_Δ₀_iff v (hsep.1.vertexSet_mono hv))
    ⟨φ, hφ_cw, hag⟩ P_pres.agrees_Δ₀
  obtain ⟨P₂, -, -, -, -⟩ := Presentation.exists_of_le (N' := N₂) P_pres hsep.2.1
    P_pres.isClosedDisc_Δ (hDs last).2 hUH₂
    (fun v hv => P_pres.mem_bd_Δ_iff v (hsep.2.1.vertexSet_mono hv))
    (hbdΩ₁ H₂ hsep.2.1) P_pres.agrees_Δ (Or.inr ⟨(hDd last).1, φ, hφ_cw, hag⟩)
  have hrural₁ : N₁.IsRural := ⟨P₁.Γ, P₁.Δ, P₁.Δ₀, P₁.isClosedDisc_Δ, P₁.Δ₀_subset_Δ, P₁.U_subset,
    P₁.mem_bd_Δ_iff, P₁.mem_bd_Δ₀_iff, P₁.agrees_Δ, P₁.agrees_Δ₀⟩
  have hrural₂ : N₂.IsRural := ⟨P₂.Γ, P₂.Δ, P₂.Δ₀, P₂.isClosedDisc_Δ, P₂.Δ₀_subset_Δ, P₂.U_subset,
    P₂.mem_bd_Δ_iff, P₂.mem_bd_Δ₀_iff, P₂.agrees_Δ, P₂.agrees_Δ₀⟩
  have hnest₁ : N₁.IsNest P₁ C := by
    exact inner_presentation_has_nested_circuits (α := α) (β := β) (N := N)
      P_pres C hcir hdisj D hDd hDs hDm N₁ hCH₁ P₁ hP₁Δ hP₁Δ₀ hP₁U
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
  have hweak_after_split : N₁.IsWeaklyLinked (range y) := by
    exact inner_segments_form_weak_linkage (α := α) (β := β) (N := N) (X := X) P x t hP hPd
      N₁ rfl y R W (fun i => hΩ₁.symm ▸ hyK i) hRP hW hWP hyR hYcard
  have hH₁S : H₁ ≤ S_comp.G := hsep.1.trans hNG
  obtain ⟨hsU, hVU⟩ := hcomp.isGraphSeparation_union (IsGraphSeparation.symm hsep) hbar₀H₁
  have hsU' : IsGraphSeparation S_comp.G H₂ (subgraphUnion S_comp.G H₁ S₀.G) := hsU
  have hS₀S : S₀.G ≤ S_comp.G := hcomp.1.1.1
  let S₁ : Society α β :=
    { G := subgraphUnion S_comp.G H₁ S₀.G, Ω := Ω₁,
      finite_V := S_comp.finite_V.subset (subgraphUnion_le hH₁S hS₀S).vertexSet_mono,
      finite_E := S_comp.finite_E.subset (subgraphUnion_le hH₁S hS₀S).edgeSet_mono,
      bar_subset := fun v hv => Or.inl (hKH₁.vertexSet_mono (hΩ₁ ▸ hv)) }
  have hcutU : V(H₂) ∩ V(S₁.G) = V(C last) := by
    rw [show V(H₂) ∩ V(S₁.G) = V(H₂) ∩ V(H₁) from hVU, inter_comm, hcut]
  have hcomp₂ : S_comp.IsComposition S₁ N₂ := by
    refine ⟨⟨IsGraphSeparation.symm hsU', hΩ ▸ hbarH₂⟩, hΩ, rfl, ?_⟩
    change Ω₁.bar = V(S₁.G) ∩ V(H₂)
    rw [hΩ₁, inter_comm, hcutU]
  have hcomp₁ : S₁.IsComposition S₀ N₁ := by
    exact inner_society_composition (α := α) (β := β) (S_comp := S_comp) (S₀ := S₀) (N := N) hcomp
      C last H₁ H₂ hsep hKH₁ hbar₀H₁ Ω₁ hΩ₁ N₁ hH₁S hS₀S S₁ rfl rfl rfl rfl rfl
  obtain ⟨T₀, hT₀, hpT₀⟩ := GraphMinor.GM09.theorem_9_1_proof hcomp₂ hrural₂ hP₀ hp
  obtain ⟨T, hT, hpT, hTends⟩ := theorem_10_3_p2 hrural₁ ⟨P₁, C, hnest₁⟩ hweak_after_split
    (by rw [hYcard]; exact hcard) hcomp₁ hT₀ hpT₀
  have hne_idx : Nonempty (Fin X.ncard) := ⟨⟨0, by omega⟩⟩
  let ψ : α → α := fun v => x (invFun y v)
  have hψ : ∀ i, ψ (y i) = x i := fun i => congrArg x (leftInverse_invFun hy_inj i)
  have hS₁T : ∀ Q ∈ T, Q ≤ S₁.G := by
    intro Q hQ
    obtain ⟨A, B, hf⟩ := hT.1
    obtain ⟨a, -, b, -, hQp⟩ := hf.2.2 Q hQ
    exact hQp.1.le
  have hRS : ∀ {i v}, v ∈ V(R i) → v ∈ V(S₁.G) → v = y i := by
    intro i v hv hv₁
    have : v ∈ V(R i) ∩ V(C last) := ⟨hv, hcutU ▸ ⟨(hR i).le.vertexSet_mono hv, hv₁⟩⟩
    rwa [hRK] at this
  have hRSN : ∀ i, IsGraphPathWithEnds S_comp.G (R i) (x i) (y i) := fun i =>
    (hR i).mono (hsep.2.1.trans hNG)
  have hRV : ∀ {Q : Graph α β} {i}, Q ≤ S₁.G → y i ∈ V(Q) → V(R i) ∩ V(Q) = {y i} := by
    intro Q i hQ hyQ
    apply Subset.antisymm
    · rintro v ⟨hv, hvQ⟩
      exact hRS hv (hQ.vertexSet_mono hvQ)
    · rintro _ rfl
      exact ⟨hyR i, hyQ⟩
  have hTY : ∀ {Q a b}, Q ∈ T → S₁.IsOmegaPathWithEnds Q a b → ∃ i j, a = y i ∧ b = y j ∧ i ≠ j
    := by
    intro Q a b hQ hab
    obtain ⟨i, rfl⟩ := hTends ⟨Q, hQ, b, hab⟩
    obtain ⟨j, rfl⟩ := hTends ⟨Q, hQ, _, Society.IsOmegaPathWithEnds.symm S₁ hab⟩
    exact ⟨i, j, rfl, rfl, fun e => hab.2.1 (congrArg y e)⟩
  have hex : ∀ Q ∈ T, ∃ Qe : Graph α β, ∀ i j, S₁.IsOmegaPathWithEnds Q (y i) (y j) →
      IsGraphPathWithEnds S_comp.G Qe (x i) (x j) ∧ V(Qe) = V(R i) ∪ V(Q) ∪ V(R j) := by
    exact transaction_path_extension (α := α) (β := β) (S_comp := S_comp) (X := X) x
      y R hy_inj hRd S₁ (subgraphUnion_le hH₁S hS₀S) T hT hS₁T hRSN hRV hTY
  choose! f hf using hex
  have hTdisj : ∀ {Q Q'}, Q ∈ T → Q' ∈ T → Q ≠ Q' → Disjoint V(Q) V(Q') := by
    intro Q Q' hQ hQ' hne
    obtain ⟨A, B, hfence⟩ := hT.1
    exact hfence.1.2 hQ hQ' hne
  have hxb : ∀ i, x i ∈ S_comp.Ω.bar := fun i => by
    have : x i ∈ V(P i) ∩ N.Ω.bar := (hP i).2.symm ▸ mem_singleton _
    exact hΩ ▸ this.2
  have hendsT : ∀ Q ∈ T, ∀ i j, S₁.IsOmegaPathWithEnds Q (y i) (y j) →
      S_comp.IsOmegaPathWithEnds (f Q) (x i) (x j) := fun Q hQ i j hij =>
    ⟨(hf Q hQ i j hij).1, fun e => hij.2.1 (congrArg y (hx_inj e)), hxb i, hxb j⟩
  have hRQ : ∀ {Q Q' i j}, Q ∈ T → Q' ∈ T → Q ≠ Q' → S₁.IsOmegaPathWithEnds Q (y i) (y j) →
      Disjoint V(R i) V(Q') := by
    intro Q Q' i j hQ hQ' hne hij
    rw [Set.disjoint_left]
    intro v hv hvQ
    have e := hRS hv ((hS₁T Q' hQ').vertexSet_mono hvQ)
    subst e
    exact Set.disjoint_left.mp (hTdisj hQ hQ' hne) hij.1.left_mem hvQ
  have hd : ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → Disjoint V(f Q) V(f Q') := by
    exact extensions_pairwise_disjoint (α := α) (β := β) (S_comp := S_comp) (X := X) x y R hRd S₁
      T hT hTY f hf hTdisj hRQ
  have hcrook : S_comp.IsCrookedTransaction (f '' T) := by
    exact extended_transaction_is_crooked (α := α) (β := β) (S_comp := S_comp) (X := X)
      x N₂ hΩ hrural₂ y R (fun i => hΩ₁.symm ▸ hyK i) hR hx_inj hRd S₁ rfl T hT hTends ψ hψ hTY f
      hxb hendsT hd
  have hDelivered :
      ∃ P' : Set (Graph α β), S_comp.IsCrookedTransaction P' ∧ P'.ncard = 2 ∧
        S_comp.transactionEnds P' ⊆ X ∧
        ∀ P ∈ P', Disjoint (pathInternalVerts S_comp.G P) S_comp.Ω.bar := by
    exact extended_transaction_preserves_size_and_endpoints (α := α) (β := β) (S_comp := S_comp)
      (N := N) (X := X) C P x t hCbar hP hΩ last H₂ hbarH₂ y R hRP S₁ hcutU T hT hpT hS₁T hTY f hf
      hendsT hd hcrook
  exact hDelivered

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
