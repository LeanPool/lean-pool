/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM18.Section2
import LeanPool.GraphMinor.GM10.TangleLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Graph Minors XVIII, Section 3: Tree-Width of a Location

This file formalizes Section 3 (pages 82–84) of Robertson and Seymour,
*Graph Minors. XVIII. Tree-decompositions and well-quasi-ordering*, J. Combin. Theory Ser. B 89
(2003) 77–108:

* `theorem_3_1` (3.1, page 82): invariance of titanicity of `(A, B)` under replacing `B` by `B'`
  with `V(A ∩ B) = V(A ∩ B')` (or `A ∩ B = A ∩ B'`).
* `theorem_3_2` (3.2, page 82): transfer of a tangle across a titanic separation (from Graph
  Minors X, (8.3)).
* `theorem_3_3` (3.3, page 82): if `(B, A) ∈ 𝒯` is linked to a tangle `𝒯` of order `≥ θ` and has
  order `≤ (3/4) θ`, then `(A, B)` is titanic.
* `theorem_3_4` (3.4, page 84): if `ℒ` is a location of titanic separations in `G` of order `< θ`
  (`θ ≥ 2`), then either `ℒ ⊆ 𝒯` for some tangle `𝒯` in `G` of order `θ`, or `ℒ` has tree-width
  `≤ (3/2) θ`.
-/

public section

namespace GraphMinor.GM18

open Hypergraph SimpleGraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## Basic properties of `locationOrder` -/

theorem separationOrder_le_locationOrder {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ)
    {p : Hypergraph α β × Hypergraph α β} (hp : p ∈ ℒ) :
    separationOrder p.1 p.2 ≤ locationOrder ℒ := by
  unfold locationOrder
  exact le_csSup (hℒ.finite.image _).bddAbove ⟨p, hp, rfl⟩

theorem separationOrder_lt_of_locationOrder_lt {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ)
    {θ : ℕ} (hord : locationOrder ℒ < θ)
    {p : Hypergraph α β × Hypergraph α β} (hp : p ∈ ℒ) :
    separationOrder p.1 p.2 < θ :=
  (separationOrder_le_locationOrder hℒ hp).trans_lt hord

theorem locationOrder_lt_iff {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ)
    {θ : ℕ} (hθ : 1 ≤ θ) :
    locationOrder ℒ < θ ↔ ∀ ⦃p⦄, p ∈ ℒ → separationOrder p.1 p.2 < θ := by
  refine ⟨fun h p hp ↦ separationOrder_lt_of_locationOrder_lt hℒ h hp, fun h ↦ ?_⟩
  unfold locationOrder
  rcases Set.eq_empty_or_nonempty ℒ with rfl | hne
  · simp
    omega
  · have himg_ne : ((fun p : Hypergraph α β × Hypergraph α β ↦ separationOrder p.1 p.2) ''
    ℒ).Nonempty :=
      hne.image _
    obtain ⟨p, hp, hmax⟩ := Nat.sSup_mem himg_ne (hℒ.finite.image _).bddAbove
    rw [← hmax]
    exact h hp

/-! ## (3.1) and (3.2) -/

/-- Version of **Graph Minors XVIII, (3.1)** (page 82) assuming only `V(A ∩ B) = V(A ∩ B')`:
if `(A, B)` is a separation of `G` and `(A, B')` is a separation of `G'` with
`V(A ∩ B) = V(A ∩ B')`, then `(A, B)` is titanic in `G` if and only if `(A, B')` is titanic in
`G'`. -/
theorem isTitanic_iff_of_vertexSet_inter_eq {G G' A B B' : Hypergraph α β}
    (hAB : G.IsSeparation A B) (hAB' : G'.IsSeparation A B')
    (hV : (A ∩ B).vertexSet = (A ∩ B').vertexSet) :
    GM10.IsTitanic G A B ↔ GM10.IsTitanic G' A B' := by
  have sub_inter_eq : ∀ {H : Hypergraph α β}, H ≤ A →
      (H ∩ B).vertexSet = (H ∩ B').vertexSet := by
    intro H hH
    have h1 : (H ∩ B).vertexSet = H.vertexSet ∩ (A ∩ B).vertexSet := by
      ext v
      simp only [GM10.inter_vertexSet, Set.mem_inter_iff]
      exact ⟨fun ⟨hvH, hvB⟩ ↦ ⟨hvH, hH.vertexSet_subset hvH, hvB⟩,
        fun ⟨hvH, _, hvB⟩ ↦ ⟨hvH, hvB⟩⟩
    have h2 : (H ∩ B').vertexSet = H.vertexSet ∩ (A ∩ B').vertexSet := by
      ext v
      simp only [GM10.inter_vertexSet, Set.mem_inter_iff]
      exact ⟨fun ⟨hvH, hvB'⟩ ↦ ⟨hvH, hH.vertexSet_subset hvH, hvB'⟩,
        fun ⟨hvH, _, hvB'⟩ ↦ ⟨hvH, hvB'⟩⟩
    rw [h1, hV, ← h2]
  constructor
  · intro h
    refine ⟨hAB', fun X Y Z hX hY hZ hU hdXY hdYZ hdXZ ↦ ?_⟩
    rw [← sub_inter_eq (GM10.union_le hX hY), ← sub_inter_eq (GM10.union_le hY hZ),
      ← sub_inter_eq (GM10.union_le hZ hX)]
    exact h.2 hX hY hZ hU hdXY hdYZ hdXZ
  · intro h
    refine ⟨hAB, fun X Y Z hX hY hZ hU hdXY hdYZ hdXZ ↦ ?_⟩
    rw [sub_inter_eq (GM10.union_le hX hY), sub_inter_eq (GM10.union_le hY hZ),
      sub_inter_eq (GM10.union_le hZ hX)]
    exact h.2 hX hY hZ hU hdXY hdYZ hdXZ

/-- **Graph Minors XVIII, (3.1)** (page 82):
"Let $(A, B)$ be a separation of a hypergraph $G$, and let $(A, B')$ be a separation of a
hypergraph $G'$, with $A \cap B = A \cap B'$. Then $(A, B)$ is titanic if and only if $(A,
B')$ is titanic." -/
theorem theorem_3_1_proof {G G' A B B' : Hypergraph α β}
    (hAB : G.IsSeparation A B) (hAB' : G'.IsSeparation A B')
    (hinter : A ∩ B = A ∩ B') :
    GM10.IsTitanic G A B ↔ GM10.IsTitanic G' A B' :=
  isTitanic_iff_of_vertexSet_inter_eq hAB hAB' (congrArg Hypergraph.vertexSet hinter)

/-- **Graph Minors XVIII, (3.2)** (page 82):
"Let $(C, D)$ be a separation of a hypergraph $G$, and let $(C', D)$ be a titanic separation
of a hypergraph $G'$, with $V(C \cap D) = V(C' \cap D)$. Let $\mathscr{T}$ be a tangle in
$G$ of order $\theta \ge 2$ with $(C, D) \in \mathscr{T}$. Let $\mathscr{T}'$ be the set of
all separations $(A', B')$ of $G'$ of order $< \theta$ such that there exists $(A, B) \in
\mathscr{T}$ with $E(A \cap D) = E(A' \cap D)$. Then $\mathscr{T}'$ is a tangle in $G'$ of
order $\theta$." -/
theorem theorem_3_2_proof
    {G G' C C' D : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (hCD : G.IsSeparation C D)
    (hC'D : GM10.IsTitanic G' C' D)
    (hV : (C ∩ D).vertexSet = (C' ∩ D).vertexSet)
    (h𝒯 : GM10.IsTangle G θ 𝒯)
    (hθ : 2 ≤ θ)
    (hmem : (C, D) ∈ 𝒯) :
    GM10.IsTangle G' θ (GM10.titanicTransferredTangle G' D 𝒯 θ) :=
  gm10Theorem83 G G' C C' D 𝒯 θ hCD hC'D hV h𝒯 hθ hmem

/-! ## (3.3): Linked Separations of Order `≤ (3/4) θ` are Titanic -/

private theorem separation_of_triple_union {G A B X₁ X₂ X₃ : Hypergraph α β}
    (hAB : G.IsSeparation A B)
    (hX₁ : X₁ ≤ A) (hX₂ : X₂ ≤ A) (hX₃ : X₃ ≤ A)
    (hU : X₁ ∪ X₂ ∪ X₃ = A)
    (hd12 : Disjoint X₁.edgeSet X₂.edgeSet)
    (_hd23 : Disjoint X₂.edgeSet X₃.edgeSet)
    (hd13 : Disjoint X₁.edgeSet X₃.edgeSet) :
    A.IsSeparation X₁ (X₂ ∪ X₃) ∧
    G.IsSeparation X₁ (B ∪ (X₂ ∪ X₃)) ∧
    G.IsSeparation (X₁ ∪ B) (X₂ ∪ X₃) := by
  have hsepA : A.IsSeparation X₁ (X₂ ∪ X₃) := by
    rw [GM10.isSeparation_iff_of_le hX₁ (GM10.union_le hX₂ hX₃)]
    refine ⟨?_, ?_, ?_⟩
    · rw [← GM10.union_vertexSet, ← GM10.union_assoc, hU]
    · rw [← GM10.union_edgeSet, ← GM10.union_assoc, hU]
    · rw [GM10.union_edgeSet, ← Set.disjoint_iff_inter_eq_empty]
      exact hd12.union_right hd13
  have hsepG₁ : G.IsSeparation X₁ (B ∪ (X₂ ∪ X₃)) :=
    isSeparation_left_split hAB hsepA
  have hsepG₂ : G.IsSeparation (X₁ ∪ B) (X₂ ∪ X₃) := by
    have h := (isSeparation_left_split hAB hsepA.symm).symm
    rwa [GM10.union_comm B X₁] at h
  exact ⟨hsepA, hsepG₁, hsepG₂⟩

private theorem finset_card_triple_bound [DecidableEq α] (W₁ W₂ W₃ : Finset α) :
    2 * ((W₂ ∪ W₃) \ W₁).card + ((W₂ ∪ W₃) ∩ W₁).card +
    (2 * ((W₃ ∪ W₁) \ W₂).card + ((W₃ ∪ W₁) ∩ W₂).card) +
    (2 * ((W₁ ∪ W₂) \ W₃).card + ((W₁ ∪ W₂) ∩ W₃).card) ≤
    4 * (W₁ ∪ W₂ ∪ W₃).card := by
  let S := W₁ ∪ W₂ ∪ W₃
  have hsub : ∀ A : Finset α, A ⊆ S → A.card = ∑ x ∈ S, if x ∈ A then 1 else 0 := by
    intro A hA
    rw [Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.2 hA]
  have hs1 : (W₂ ∪ W₃) \ W₁ ⊆ S :=
    Finset.sdiff_subset.trans (Finset.union_subset
      (Finset.subset_union_right.trans Finset.subset_union_left) Finset.subset_union_right)
  have hi1 : (W₂ ∪ W₃) ∩ W₁ ⊆ S :=
    Finset.inter_subset_right.trans
      (Finset.subset_union_left.trans Finset.subset_union_left)
  have hs2 : (W₃ ∪ W₁) \ W₂ ⊆ S :=
    Finset.sdiff_subset.trans (Finset.union_subset Finset.subset_union_right
      (Finset.subset_union_left.trans Finset.subset_union_left))
  have hi2 : (W₃ ∪ W₁) ∩ W₂ ⊆ S :=
    Finset.inter_subset_right.trans
      (Finset.subset_union_right.trans Finset.subset_union_left)
  have hs3 : (W₁ ∪ W₂) \ W₃ ⊆ S :=
    Finset.sdiff_subset.trans Finset.subset_union_left
  have hi3 : (W₁ ∪ W₂) ∩ W₃ ⊆ S :=
    Finset.inter_subset_right.trans Finset.subset_union_right
  rw [hsub _ hs1, hsub _ hi1, hsub _ hs2, hsub _ hi2, hsub _ hs3, hsub _ hi3,
    hsub S Finset.Subset.rfl]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  by_cases h1 : x ∈ W₁ <;> by_cases h2 : x ∈ W₂ <;> by_cases h3 : x ∈ W₃ <;> simp [S, h1, h2, h3]

/-- **Graph Minors XVIII, (3.3)** (page 82):
"**3.3.** *Let $\mathscr{T}$ be a tangle of order $\ge \theta$ in a hypergraph $G$ and let
$(B, A) \in \mathscr{T}$ be linked to $\mathscr{T}$ and have order $\le \frac{3}{4}\theta$.
Then $(A, B)$ is titanic.*"

This is the case where the tangle has order exactly `θ`. The printed form, with a tangle of order
`≥ θ`, is `GM18.theorem_3_3`. -/
theorem theorem_3_3_proof {G A B : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : GM10.IsTangle G θ 𝒯)
    (hlink : IsLinkedTo 𝒯 B A)
    (hord : 4 * separationOrder B A ≤ 3 * θ) :
    GM10.IsTitanic G A B := by
  classical
  have hBA : (B, A) ∈ 𝒯 := hlink.1
  have hsepAB : G.IsSeparation A B := (h𝒯.isSeparation hBA).symm
  refine ⟨hsepAB, fun X₁ X₂ X₃ hX₁ hX₂ hX₃ hU hd12 hd23 hd13 ↦ ?_⟩
  by_contra! hnot
  rcases hnot with ⟨hlt3, hlt1, hlt2⟩
  -- For any cyclic permutation (Y₁, Y₂, Y₃) of (X₁, X₂, X₃) satisfying
  -- `|((Y₂ ∪ Y₃) ∩ Y₁).vertexSet| < |((Y₂ ∪ Y₃) ∩ B).vertexSet|`,
  -- we show `(Y₁, B ∪ (Y₂ ∪ Y₃)) ∈ 𝒯` and then `θ < 2 * |((Y₂ ∪ Y₃) ∩ B) \ (Y₁ ∩ B)| + |((Y₂ ∪ Y₃)
  -- ∩ B) ∩ (Y₁ ∩ B)|`.
  have step_in_tangle : ∀ {Y₁ Y₂ Y₃ : Hypergraph α β},
      Y₁ ≤ A → Y₂ ≤ A → Y₃ ≤ A → Y₁ ∪ Y₂ ∪ Y₃ = A →
      Disjoint Y₁.edgeSet Y₂.edgeSet →
      Disjoint Y₂.edgeSet Y₃.edgeSet →
      Disjoint Y₁.edgeSet Y₃.edgeSet →
      ((Y₂ ∪ Y₃) ∩ Y₁).vertexSet.ncard < ((Y₂ ∪ Y₃) ∩ B).vertexSet.ncard →
      (Y₁, B ∪ (Y₂ ∪ Y₃)) ∈ 𝒯 := by
    intro Y₁ Y₂ Y₃ hY₁ hY₂ hY₃ hUY hd1 hd2 hd3 hltY
    have ⟨_, hsepG₁, _⟩ := separation_of_triple_union hsepAB hY₁ hY₂ hY₃ hUY hd1 hd2 hd3
    by_contra hnot_mem
    have hord_ge : separationOrder B A ≤ separationOrder Y₁ (B ∪ (Y₂ ∪ Y₃)) := by
      by_cases hlt_θ : separationOrder Y₁ (B ∪ (Y₂ ∪ Y₃)) < θ
      · have hswap : (B ∪ (Y₂ ∪ Y₃), Y₁) ∈ 𝒯 :=
          (h𝒯.axiom1 hsepG₁ hlt_θ).resolve_left hnot_mem
        have hB_le : B ≤ B ∪ (Y₂ ∪ Y₃) :=
          GM10.le_union_left hsepAB.right_le
            ((GM10.union_le hY₂ hY₃).trans hsepAB.left_le)
        have hle := hlink.2 hswap hB_le hY₁
        rwa [GM10.separationOrder_comm _ Y₁] at hle
      · exact (h𝒯.order_lt hBA).le.trans (not_lt.1 hlt_θ)
    -- Now compare `separationOrder Y₁ (B ∪ (Y₂ ∪ Y₃))` and `separationOrder B A`:
    have hsub1 : (Y₁ ∩ (B ∪ (Y₂ ∪ Y₃))).vertexSet ⊆
        ((Y₂ ∪ Y₃) ∩ Y₁).vertexSet ∪ ((Y₁ ∩ B).vertexSet \ ((Y₂ ∪ Y₃) ∩ B).vertexSet) := by
      intro v ⟨hv₁, hvB23⟩
      simp only [GM10.union_vertexSet, Set.mem_union] at hvB23
      rcases hvB23 with hvB | hv23
      · by_cases hv23' : v ∈ (Y₂ ∪ Y₃).vertexSet
        · exact Or.inl ⟨hv23', hv₁⟩
        · exact Or.inr ⟨⟨hv₁, hvB⟩, fun h ↦ hv23' h.1⟩
      · exact Or.inl ⟨hv23, hv₁⟩
    have hfin1 : ((Y₂ ∪ Y₃) ∩ Y₁).vertexSet.Finite := ((Y₂ ∪ Y₃) ∩ Y₁).vertexSet_finite
    have hfin2 : ((Y₁ ∩ B).vertexSet \ ((Y₂ ∪ Y₃) ∩ B).vertexSet).Finite :=
      (Y₁ ∩ B).vertexSet_finite.sdiff
    have hcard_upper : separationOrder Y₁ (B ∪ (Y₂ ∪ Y₃)) ≤
        ((Y₂ ∪ Y₃) ∩ Y₁).vertexSet.ncard +
          ((Y₁ ∩ B).vertexSet \ ((Y₂ ∪ Y₃) ∩ B).vertexSet).ncard :=
      (Set.ncard_le_ncard hsub1 (hfin1.union hfin2)).trans (Set.ncard_union_le _ _)
    have hAB_eq : (B ∩ A).vertexSet =
        ((Y₂ ∪ Y₃) ∩ B).vertexSet ∪ ((Y₁ ∩ B).vertexSet \ ((Y₂ ∪ Y₃) ∩ B).vertexSet) := by
      have hVA : A.vertexSet = (Y₁ ∪ (Y₂ ∪ Y₃)).vertexSet := by
        rw [← GM10.union_assoc, hUY]
      ext v
      simp only [GM10.inter_vertexSet, GM10.union_vertexSet, Set.mem_inter_iff, Set.mem_union,
        Set.mem_sdiff]
      rw [hVA]
      simp only [GM10.union_vertexSet, Set.mem_union]
      tauto
    have hdisj_W : Disjoint ((Y₂ ∪ Y₃) ∩ B).vertexSet
        ((Y₁ ∩ B).vertexSet \ ((Y₂ ∪ Y₃) ∩ B).vertexSet) :=
      disjoint_sdiff_self_right
    have hcard_AB : separationOrder B A =
        ((Y₂ ∪ Y₃) ∩ B).vertexSet.ncard +
          ((Y₁ ∩ B).vertexSet \ ((Y₂ ∪ Y₃) ∩ B).vertexSet).ncard := by
      unfold separationOrder
      rw [hAB_eq, Set.ncard_union_eq hdisj_W ((Y₂ ∪ Y₃) ∩ B).vertexSet_finite hfin2]
    omega
  have hU231 : X₂ ∪ X₃ ∪ X₁ = A := by
    rw [GM10.union_assoc, GM10.union_comm X₃ X₁, ← GM10.union_assoc,
      GM10.union_comm X₂ X₁, hU]
  have hU312 : X₃ ∪ X₁ ∪ X₂ = A := by
    rw [GM10.union_comm (X₃ ∪ X₁) X₂, ← GM10.union_assoc, hU231]
  have hm1 : (X₁, B ∪ (X₂ ∪ X₃)) ∈ 𝒯 :=
    step_in_tangle hX₁ hX₂ hX₃ hU hd12 hd23 hd13 hlt1
  have hm2 : (X₂, B ∪ (X₃ ∪ X₁)) ∈ 𝒯 :=
    step_in_tangle hX₂ hX₃ hX₁ hU231 hd23 hd13.symm hd12.symm hlt2
  have hm3 : (X₃, B ∪ (X₁ ∪ X₂)) ∈ 𝒯 :=
    step_in_tangle hX₃ hX₁ hX₂ hU312 hd13.symm hd12 hd23.symm hlt3
  -- Next, for each cyclic permutation, `θ ≤ separationOrder (Y₁ ∪ B) (Y₂ ∪ Y₃)`
  have step_theta_lt : ∀ {Y₁ Y₂ Y₃ : Hypergraph α β},
      Y₁ ≤ A → Y₂ ≤ A → Y₃ ≤ A → Y₁ ∪ Y₂ ∪ Y₃ = A →
      Disjoint Y₁.edgeSet Y₂.edgeSet →
      Disjoint Y₂.edgeSet Y₃.edgeSet →
      Disjoint Y₁.edgeSet Y₃.edgeSet →
      (Y₁, B ∪ (Y₂ ∪ Y₃)) ∈ 𝒯 →
      (Y₂, B ∪ (Y₃ ∪ Y₁)) ∈ 𝒯 →
      (Y₃, B ∪ (Y₁ ∪ Y₂)) ∈ 𝒯 →
      ((Y₂ ∪ Y₃) ∩ Y₁).vertexSet.ncard < ((Y₂ ∪ Y₃) ∩ B).vertexSet.ncard →
      θ < 2 * (((Y₂ ∪ Y₃) ∩ B).vertexSet \ (Y₁ ∩ B).vertexSet).ncard +
        (((Y₂ ∪ Y₃) ∩ B).vertexSet ∩ (Y₁ ∩ B).vertexSet).ncard := by
    intro Y₁ Y₂ Y₃ hY₁ hY₂ hY₃ hUY hd1 hd2 hd3 hY1_T hY2_T hY3_T hltY
    have ⟨_, _, hsepG₂⟩ := separation_of_triple_union hsepAB hY₁ hY₂ hY₃ hUY hd1 hd2 hd3
    have hnot1 : (Y₁ ∪ B, Y₂ ∪ Y₃) ∉ 𝒯 := by
      intro hm
      apply h𝒯.axiom2 hm hY2_T hY3_T
      have hle : Y₁ ∪ B ∪ Y₂ ∪ Y₃ ≤ G :=
        GM10.union_le
          (GM10.union_le (GM10.union_le (hY₁.trans hsepAB.left_le) hsepAB.right_le)
            (hY₂.trans hsepAB.left_le))
          (hY₃.trans hsepAB.left_le)
      have h_eq : Y₁ ∪ B ∪ Y₂ ∪ Y₃ = (Y₁ ∪ Y₂ ∪ Y₃) ∪ B := by
        ext <;> simp [Set.union_comm, Set.union_left_comm, or_assoc, or_comm]
      rw [h_eq, hUY, hsepAB.union_eq]
    have hnot2 : (Y₂ ∪ Y₃, Y₁ ∪ B) ∉ 𝒯 := by
      intro hm
      apply h𝒯.axiom2 hm hY1_T hBA
      have h_eq : (Y₂ ∪ Y₃) ∪ Y₁ ∪ B = (Y₁ ∪ Y₂ ∪ Y₃) ∪ B := by
        ext <;> simp [Set.union_comm, Set.union_left_comm, or_assoc, or_comm]
      rw [h_eq, hUY, hsepAB.union_eq]
    have hge_θ : θ ≤ separationOrder (Y₁ ∪ B) (Y₂ ∪ Y₃) := by
      by_contra! hlt_θ
      exact (h𝒯.axiom1 hsepG₂ hlt_θ).elim hnot1 hnot2
    have hsub2 : ((Y₁ ∪ B) ∩ (Y₂ ∪ Y₃)).vertexSet ⊆
        ((Y₂ ∪ Y₃) ∩ Y₁).vertexSet ∪ (((Y₂ ∪ Y₃) ∩ B).vertexSet \ (Y₁ ∩ B).vertexSet) := by
      intro v ⟨hv1B, hv23⟩
      simp only [GM10.union_vertexSet, Set.mem_union] at hv1B
      rcases hv1B with hv1 | hvB
      · exact Or.inl ⟨hv23, hv1⟩
      · by_cases hv1 : v ∈ Y₁.vertexSet
        · exact Or.inl ⟨hv23, hv1⟩
        · exact Or.inr ⟨⟨hv23, hvB⟩, fun h ↦ hv1 h.1⟩
    have hfinA : ((Y₂ ∪ Y₃) ∩ Y₁).vertexSet.Finite := ((Y₂ ∪ Y₃) ∩ Y₁).vertexSet_finite
    have hfinB : (((Y₂ ∪ Y₃) ∩ B).vertexSet \ (Y₁ ∩ B).vertexSet).Finite :=
      ((Y₂ ∪ Y₃) ∩ B).vertexSet_finite.sdiff
    have hcard_sep : separationOrder (Y₁ ∪ B) (Y₂ ∪ Y₃) ≤
        ((Y₂ ∪ Y₃) ∩ Y₁).vertexSet.ncard +
          (((Y₂ ∪ Y₃) ∩ B).vertexSet \ (Y₁ ∩ B).vertexSet).ncard :=
      (Set.ncard_le_ncard hsub2 (hfinA.union hfinB)).trans (Set.ncard_union_le _ _)
    have hsplit : ((Y₂ ∪ Y₃) ∩ B).vertexSet.ncard =
        (((Y₂ ∪ Y₃) ∩ B).vertexSet \ (Y₁ ∩ B).vertexSet).ncard +
          (((Y₂ ∪ Y₃) ∩ B).vertexSet ∩ (Y₁ ∩ B).vertexSet).ncard := by
      have hdisj_si : Disjoint (((Y₂ ∪ Y₃) ∩ B).vertexSet \ (Y₁ ∩ B).vertexSet)
          (((Y₂ ∪ Y₃) ∩ B).vertexSet ∩ (Y₁ ∩ B).vertexSet) :=
        Set.disjoint_iff.2 fun v ⟨⟨_, hnot⟩, ⟨_, hin⟩⟩ ↦ hnot hin
      rw [← Set.ncard_union_eq hdisj_si hfinB
        (((Y₂ ∪ Y₃) ∩ B).vertexSet_finite.inter_of_left _),
        Set.sdiff_union_inter]
    omega
  have hb1 := step_theta_lt hX₁ hX₂ hX₃ hU hd12 hd23 hd13 hm1 hm2 hm3 hlt1
  have hb2 := step_theta_lt hX₂ hX₃ hX₁ hU231 hd23 hd13.symm hd12.symm hm2 hm3 hm1 hlt2
  have hb3 := step_theta_lt hX₃ hX₁ hX₂ hU312 hd13.symm hd12 hd23.symm hm3 hm1 hm2 hlt3
  -- Convert the sets `(Xᵢ ∩ B).vertexSet` to `Finset α` and apply `finset_card_triple_bound`
  let fW₁ := (X₁ ∩ B).vertexSet_finite.toFinset
  let fW₂ := (X₂ ∩ B).vertexSet_finite.toFinset
  let fW₃ := (X₃ ∩ B).vertexSet_finite.toFinset
  have toFinset_union_inter : ∀ {Y₂ Y₃ : Hypergraph α β},
      ((Y₂ ∪ Y₃) ∩ B).vertexSet = (Y₂ ∩ B).vertexSet ∪ (Y₃ ∩ B).vertexSet := by
    intro Y₂ Y₃
    ext v
    simp only [GM10.inter_vertexSet, GM10.union_vertexSet, Set.mem_inter_iff, Set.mem_union]
    exact or_and_right
  have ncard_sdiff_eq : ∀ {Y₁ Y₂ Y₃ : Hypergraph α β} (f1 f2 f3 : Finset α),
      (f1 : Set α) = (Y₁ ∩ B).vertexSet →
      (f2 : Set α) = (Y₂ ∩ B).vertexSet →
      (f3 : Set α) = (Y₃ ∩ B).vertexSet →
      (((Y₂ ∪ Y₃) ∩ B).vertexSet \ (Y₁ ∩ B).vertexSet).ncard = ((f2 ∪ f3) \ f1).card ∧
      (((Y₂ ∪ Y₃) ∩ B).vertexSet ∩ (Y₁ ∩ B).vertexSet).ncard = ((f2 ∩ f1) ∪ (f3 ∩ f1)).card := by
    intro Y₁ Y₂ Y₃ f1 f2 f3 hf1 hf2 hf3
    rw [toFinset_union_inter, ← hf1, ← hf2, ← hf3]
    constructor
    · rw [← Finset.coe_union, ← Finset.coe_sdiff, Set.ncard_coe_finset]
    · rw [← Finset.coe_union, ← Finset.coe_inter, Set.ncard_coe_finset,
        Finset.union_inter_distrib_right]
  have ⟨hs1_eq, hi1_eq⟩ := ncard_sdiff_eq fW₁ fW₂ fW₃
    (Set.Finite.coe_toFinset _) (Set.Finite.coe_toFinset _) (Set.Finite.coe_toFinset _)
  have ⟨hs2_eq, hi2_eq⟩ := ncard_sdiff_eq fW₂ fW₃ fW₁
    (Set.Finite.coe_toFinset _) (Set.Finite.coe_toFinset _) (Set.Finite.coe_toFinset _)
  have ⟨hs3_eq, hi3_eq⟩ := ncard_sdiff_eq fW₃ fW₁ fW₂
    (Set.Finite.coe_toFinset _) (Set.Finite.coe_toFinset _) (Set.Finite.coe_toFinset _)
  rw [ ← Finset.union_inter_distrib_right] at hi1_eq hi2_eq hi3_eq
  have hfin_bound := finset_card_triple_bound fW₁ fW₂ fW₃
  have hW_union_eq : (fW₁ ∪ fW₂ ∪ fW₃).card = separationOrder B A := by
    have hset : ((fW₁ ∪ fW₂ ∪ fW₃ : Finset α) : Set α) = (B ∩ A).vertexSet := by
      rw [Finset.coe_union, Finset.coe_union, Set.Finite.coe_toFinset,
        Set.Finite.coe_toFinset, Set.Finite.coe_toFinset]
      have hVA : A.vertexSet = (X₁ ∪ X₂ ∪ X₃).vertexSet := hU.symm ▸ rfl
      ext v
      simp only [GM10.inter_vertexSet, Set.mem_union, Set.mem_inter_iff, hVA,
        GM10.union_vertexSet]
      tauto
    unfold separationOrder
    rw [← hset, Set.ncard_coe_finset]
  omega

/-! ## (3.4): Titanic Locations and Tree-Width -/

/-- Embeds a `Hypergraph α β` into `Hypergraph α (β ⊕ γ)` via `Sum.inl`. -/
def mapInl (γ : Type*) (G : Hypergraph α β) : Hypergraph α (β ⊕ γ) where
  vertexSet := G.vertexSet
  edgeSet := Sum.inl '' G.edgeSet
  Inc e v :=
    match e with
    | Sum.inl e₀ => G.Inc e₀ v
    | Sum.inr _ => False
  vertex_mem_of_inc e v h := by
    cases e with
    | inl e₀ => exact G.vertex_mem_of_inc h
    | inr _ => exact h.elim
  edge_mem_of_inc e v h := by
    cases e with
    | inl e₀ => exact ⟨e₀, G.edge_mem_of_inc h, rfl⟩
    | inr _ => exact h.elim
  vertexSet_finite := G.vertexSet_finite
  edgeSet_finite := G.edgeSet_finite.image Sum.inl

/-- Pulls back a `Hypergraph α (β ⊕ γ)` along `Sum.inl`. -/
def comapInl {γ : Type*} (H : Hypergraph α (β ⊕ γ)) : Hypergraph α β where
  vertexSet := H.vertexSet
  edgeSet := Sum.inl ⁻¹' H.edgeSet
  Inc e v := H.Inc (Sum.inl e) v
  vertex_mem_of_inc _ _ h := H.vertex_mem_of_inc h
  edge_mem_of_inc _ _ h := H.edge_mem_of_inc h
  vertexSet_finite := H.vertexSet_finite
  edgeSet_finite := H.edgeSet_finite.preimage Sum.inl_injective.injOn

@[simp]
theorem comapInl_mapInl (γ : Type*) (G : Hypergraph α β) :
    comapInl (mapInl γ G) = G := by
  ext v e
  · rfl
  · simp [comapInl, mapInl]
  · rfl

theorem mapInl_comapInl_of_le {γ : Type*} {G : Hypergraph α β}
    {H : Hypergraph α (β ⊕ γ)} (h : H ≤ mapInl γ G) :
    mapInl γ (comapInl H) = H := by
  have hle : mapInl γ (comapInl H) ≤ mapInl γ G := by
    refine ⟨h.vertexSet_subset, ?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      exact h.edgeSet_subset he
    · rintro _ ⟨e, he, rfl⟩
      exact h.ends_eq (Sum.inl e) he
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle h rfl ?_
  ext x
  cases x with
  | inl e => simp [mapInl, comapInl]
  | inr c =>
    simp only [mapInl, Set.mem_image, reduceCtorEq, and_false, exists_false, false_iff]
    intro hc
    rcases h.edgeSet_subset hc with ⟨e, _, hce⟩
    cases hce

theorem mapInl_mono (γ : Type*) {H₁ H₂ : Hypergraph α β} (h : H₁ ≤ H₂) :
    mapInl γ H₁ ≤ mapInl γ H₂ where
  vertexSet_subset := h.vertexSet_subset
  edgeSet_subset := Set.image_mono h.edgeSet_subset
  ends_eq e he := by
    rcases he with ⟨e₀, he₀, rfl⟩
    exact h.ends_eq e₀ he₀

theorem mapInl_union (γ : Type*) (H₁ H₂ : Hypergraph α β) :
    mapInl γ (H₁ ∪ H₂) = mapInl γ H₁ ∪ mapInl γ H₂ := by
  ext v e
  · rfl
  · simp [mapInl, Set.image_union]
  · cases v <;> simp [mapInl]

@[simp]
theorem comapInl_union {γ : Type*} (H₁ H₂ : Hypergraph α (β ⊕ γ)) :
    comapInl (H₁ ∪ H₂) = comapInl H₁ ∪ comapInl H₂ := by
  ext <;> rfl

theorem mapInl_inter (γ : Type*) (H₁ H₂ : Hypergraph α β) :
    mapInl γ (H₁ ∩ H₂) = mapInl γ H₁ ∩ mapInl γ H₂ := by
  ext v e
  · rfl
  · simp [mapInl, Set.image_inter Sum.inl_injective]
  · cases v <;> simp [mapInl]

/-- The subhypergraph `C_i` of `locationHeart G ℒ` for `p = (A_i, B_i) ∈ ℒ`, with vertex set
`V(A_i ∩ B_i)` and single edge `Sum.inr p` (Graph Minors XVIII, Section 3, proof of (3.4),
page 84). -/
def locationHeartEdge (p : Hypergraph α β × Hypergraph α β) :
    Hypergraph α (β ⊕ (Hypergraph α β × Hypergraph α β)) where
  vertexSet := (p.1 ∩ p.2).vertexSet
  edgeSet := {Sum.inr p}
  Inc e v := e = Sum.inr p ∧ v ∈ (p.1 ∩ p.2).vertexSet
  vertex_mem_of_inc _ _ h := h.2
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := (p.1 ∩ p.2).vertexSet_finite
  edgeSet_finite := Set.finite_singleton _

/-- The ambient hypergraph containing both `mapInl _ G` and `locationHeart G ℒ`. -/
def locationAmbient (G : Hypergraph α β)
    (ℒ : Set (Hypergraph α β × Hypergraph α β)) :
    Hypergraph α (β ⊕ (Hypergraph α β × Hypergraph α β)) :=
  mapInl (Hypergraph α β × Hypergraph α β) G ∪ locationHeart G ℒ

theorem mapInl_le_locationAmbient {G H : Hypergraph α β}
    (ℒ : Set (Hypergraph α β × Hypergraph α β)) (hH : H ≤ G) :
    mapInl (Hypergraph α β × Hypergraph α β) H ≤ locationAmbient G ℒ where
  vertexSet_subset := hH.vertexSet_subset.trans Set.subset_union_left
  edgeSet_subset := (Set.image_mono hH.edgeSet_subset).trans Set.subset_union_left
  ends_eq e he := by
    rcases he with ⟨e₀, he₀, rfl⟩
    ext v
    change (G.Inc e₀ v ∨ (GM10.locationCore G ℒ).Inc e₀ v) ↔ H.Inc e₀ v
    have hcore_imp : (GM10.locationCore G ℒ).Inc e₀ v → G.Inc e₀ v := fun hc ↦ hc.1
    rw [or_iff_left_of_imp hcore_imp]
    exact Set.ext_iff.1 (hH.ends_eq e₀ he₀) v

theorem locationHeartEdge_le_locationAmbient {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ)
    {p : Hypergraph α β × Hypergraph α β} (hp : p ∈ ℒ) :
    locationHeartEdge p ≤ locationAmbient G ℒ where
  vertexSet_subset := by
    have hsub : (p.1 ∩ p.2).vertexSet ⊆ G.vertexSet :=
      Set.inter_subset_left.trans (hℒ.isSeparation hp).left_le.vertexSet_subset
    exact hsub.trans Set.subset_union_left
  edgeSet_subset := by
    rintro _ rfl
    refine Or.inr (Or.inr ⟨p, ⟨hp, hℒ.isSeparation hp, ?_⟩, rfl⟩)
    rw [← (theorem_2_3_2 hℒ hp).2]
    exact Set.inter_subset_right
  ends_eq e he := by
    rcases Set.mem_singleton_iff.1 he with rfl
    ext v
    have hsub : (p.1 ∩ p.2).vertexSet ⊆ (GM10.locationCore G ℒ).vertexSet := by
      rw [← (theorem_2_3_2 hℒ hp).2]
      exact Set.inter_subset_right
    change (False ∨ (p ∈ ℒ ∧ G.IsSeparation p.1 p.2 ∧
      (p.1 ∩ p.2).vertexSet ⊆ (GM10.locationCore G ℒ).vertexSet ∧
      v ∈ (p.1 ∩ p.2).vertexSet)) ↔
      (Sum.inr p = Sum.inr p ∧ v ∈ (p.1 ∩ p.2).vertexSet)
    exact ⟨fun h ↦ ⟨rfl, (h.resolve_left id).2.2.2⟩,
      fun h ↦ Or.inr ⟨hp, hℒ.isSeparation hp, hsub, h.2⟩⟩

open Classical in
/-- The intermediate hypergraph `H_S` in the proof of (3.4) (page 84): for `S ⊆ ℒ`, the elements
of `S` have `A_p` (via `mapInl`) and the elements of `ℒ \ S` have `C_p` (`locationHeartEdge p`). -/
noncomputable def locationStepHypergraph (G : Hypergraph α β)
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ)
    (S : Finset (Hypergraph α β × Hypergraph α β)) :
    Hypergraph α (β ⊕ (Hypergraph α β × Hypergraph α β)) :=
  mapInl _ (GM10.locationCore G ℒ) ∪
    Hypergraph.biUnion S (fun p ↦ mapInl _ p.1) ∪
    Hypergraph.biUnion (hℒ.finite.toFinset \ S) locationHeartEdge

open Classical in
/-- The side hypergraph `B_{p, S}` in the proof of (3.4) (page 84). -/
noncomputable def locationStepSide (G : Hypergraph α β)
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ)
    (S : Finset (Hypergraph α β × Hypergraph α β))
    (p : Hypergraph α β × Hypergraph α β) :
    Hypergraph α (β ⊕ (Hypergraph α β × Hypergraph α β)) :=
  mapInl _ (GM10.locationCore G ℒ) ∪
    Hypergraph.biUnion (S.erase p) (fun q ↦ mapInl _ q.1) ∪
    Hypergraph.biUnion ((hℒ.finite.toFinset \ S).erase p) locationHeartEdge

open Classical in
theorem locationStepHypergraph_le_ambient {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ)
    {S : Finset (Hypergraph α β × Hypergraph α β)} (hS : S ⊆ hℒ.finite.toFinset) :
    locationStepHypergraph G hℒ S ≤ locationAmbient G ℒ := by
  refine GM10.union_le (GM10.union_le (mapInl_le_locationAmbient ℒ (locationCore_le hℒ)) ?_) ?_
  · refine biUnion_le fun q hq ↦ ?_
    have hq_mem : q ∈ ℒ := hℒ.finite.mem_toFinset.1 (hS hq)
    exact mapInl_le_locationAmbient ℒ (hℒ.isSeparation hq_mem).left_le
  · refine biUnion_le fun q hq ↦ ?_
    have hq_mem : q ∈ ℒ := hℒ.finite.mem_toFinset.1 (Finset.sdiff_subset hq)
    exact locationHeartEdge_le_locationAmbient hℒ hq_mem

open Classical in
theorem locationStepSide_le_ambient {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ)
    {S : Finset (Hypergraph α β × Hypergraph α β)} (hS : S ⊆ hℒ.finite.toFinset)
    (p : Hypergraph α β × Hypergraph α β) :
    locationStepSide G hℒ S p ≤ locationAmbient G ℒ := by
  refine GM10.union_le (GM10.union_le (mapInl_le_locationAmbient ℒ (locationCore_le hℒ)) ?_) ?_
  · refine biUnion_le fun q hq ↦ ?_
    have hq_mem : q ∈ ℒ := hℒ.finite.mem_toFinset.1 (hS (Finset.mem_of_mem_erase hq))
    exact mapInl_le_locationAmbient ℒ (hℒ.isSeparation hq_mem).left_le
  · refine biUnion_le fun q hq ↦ ?_
    have hq_mem : q ∈ ℒ := hℒ.finite.mem_toFinset.1 (Finset.sdiff_subset
      (Finset.mem_of_mem_erase hq))
    exact locationHeartEdge_le_locationAmbient hℒ hq_mem

open Classical in
theorem locationStepHypergraph_empty {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ) :
    locationStepHypergraph G hℒ ∅ = locationHeart G ℒ := by
  have h1 : locationStepHypergraph G hℒ ∅ ≤ locationAmbient G ℒ :=
    locationStepHypergraph_le_ambient hℒ (Finset.empty_subset _)
  have h2 : locationHeart G ℒ ≤ locationAmbient G ℒ := by
    refine ⟨Set.subset_union_right, Set.subset_union_right, fun e he ↦ ?_⟩
    ext v
    cases e with
    | inl e₀ =>
      change (G.Inc e₀ v ∨ (GM10.locationCore G ℒ).Inc e₀ v) ↔
        (GM10.locationCore G ℒ).Inc e₀ v
      rcases he with ⟨e₁, he₁, heq⟩ | ⟨p, _, heq⟩
      · cases heq
        exact ⟨fun h ↦ h.elim
          (fun hG ↦ (GM10.inc_iff_of_le (locationCore_le hℒ) he₁).2 hG) id, Or.inr⟩
      · cases heq
    | inr p =>
      change (False ∨ (locationHeart G ℒ).Inc (Sum.inr p) v) ↔
        (locationHeart G ℒ).Inc (Sum.inr p) v
      exact or_iff_right False.elim
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq h1 h2 ?_ ?_
  · ext v
    simp only [locationStepHypergraph, GM10.union_vertexSet, mapInl, biUnion,
      Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty,
      Finset.sdiff_empty, Set.mem_union, Set.mem_iUnion, Set.Finite.mem_toFinset,
      locationHeartEdge, locationHeart]
    refine or_iff_left_of_imp ?_
    rintro ⟨p, hp, hvp⟩
    have hsub : (p.1 ∩ p.2).vertexSet ⊆ (GM10.locationCore G ℒ).vertexSet := by
      rw [← (theorem_2_3_2 hℒ hp).2]
      exact Set.inter_subset_right
    exact hsub hvp
  · ext e
    cases e with
    | inl e₀ =>
      simp [locationStepHypergraph, mapInl, biUnion, locationHeartEdge, locationHeart]
    | inr p =>
      simp only [locationStepHypergraph, GM10.union_edgeSet, mapInl, biUnion,
        Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty,
        Finset.sdiff_empty, Set.mem_union, Set.mem_image, reduceCtorEq, and_false,
        exists_false, Set.mem_iUnion, Set.Finite.mem_toFinset, locationHeartEdge,
        Set.mem_singleton_iff, Sum.inr.injEq, false_or, locationHeart,
        Set.mem_sep_iff]
      constructor
      · rintro ⟨q, hq, hpq⟩
        exact hpq ▸ ⟨q, ⟨hq, hℒ.isSeparation hq, by
          rw [← (theorem_2_3_2 hℒ hq).2]
          exact Set.inter_subset_right⟩, rfl⟩
      · rintro ⟨q, ⟨hq, _, _⟩, hqp⟩
        exact hqp ▸ ⟨q, hq, rfl⟩

open Classical in
theorem locationStepHypergraph_full {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ) :
    locationStepHypergraph G hℒ hℒ.finite.toFinset =
      mapInl (Hypergraph α β × Hypergraph α β) G := by
  have h1 : locationStepHypergraph G hℒ hℒ.finite.toFinset ≤ locationAmbient G ℒ :=
    locationStepHypergraph_le_ambient hℒ Finset.Subset.rfl
  have h2 : mapInl _ G ≤ locationAmbient G ℒ := mapInl_le_locationAmbient ℒ le_rfl
  have hU := (theorem_2_3_1 hℒ).2.2
  have hVG : (GM10.locationCore G ℒ ∪ Hypergraph.biUnion hℒ.finite.toFinset Prod.fst).vertexSet =
      G.vertexSet := congrArg Hypergraph.vertexSet hU
  have hEG : (GM10.locationCore G ℒ ∪ Hypergraph.biUnion hℒ.finite.toFinset Prod.fst).edgeSet =
      G.edgeSet := congrArg Hypergraph.edgeSet hU
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq h1 h2 ?_ ?_
  · change (locationStepHypergraph G hℒ hℒ.finite.toFinset).vertexSet = G.vertexSet
    rw [← hVG]
    ext v
    simp [locationStepHypergraph, mapInl, biUnion]
  · ext e
    cases e with
    | inl e₀ =>
      simp only [locationStepHypergraph, GM10.union_edgeSet, mapInl, biUnion,
        Finset.sdiff_self, Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty,
        Set.union_empty, Set.mem_union, Set.mem_image, Sum.inl.injEq, exists_eq_right,
        Set.mem_iUnion]
      rw [← hEG]
      simp [biUnion]
    | inr p =>
      simp [locationStepHypergraph, mapInl, biUnion]

open Classical in
theorem locationStepSide_insert_self {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ)
    {S : Finset (Hypergraph α β × Hypergraph α β)}
    {p : Hypergraph α β × Hypergraph α β} (hpS : p ∉ S) :
    locationStepSide G hℒ (insert p S) p = locationStepSide G hℒ S p := by
  unfold locationStepSide
  rw [Finset.erase_insert hpS, Finset.erase_eq_of_notMem hpS]
  have hsdiff : hℒ.finite.toFinset \ insert p S = (hℒ.finite.toFinset \ S).erase p := by
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or, Finset.mem_erase]
    tauto
  rw [hsdiff, Finset.erase_idem]

open Classical in
theorem locationStepSide_full {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ)
    {p : Hypergraph α β × Hypergraph α β} (hp : p ∈ ℒ) :
    locationStepSide G hℒ hℒ.finite.toFinset p =
      mapInl (Hypergraph α β × Hypergraph α β) p.2 := by
  have h1 : locationStepSide G hℒ hℒ.finite.toFinset p ≤ locationAmbient G ℒ :=
    locationStepSide_le_ambient hℒ Finset.Subset.rfl p
  have h2 : mapInl _ p.2 ≤ locationAmbient G ℒ :=
    mapInl_le_locationAmbient ℒ (hℒ.isSeparation hp).right_le
  have hB := (theorem_2_3_2 hℒ hp).1
  have hVB : p.2.vertexSet = (GM10.locationCore G ℒ ∪
      Hypergraph.biUnion (hℒ.finite.toFinset.filter (· ≠ p)) Prod.fst).vertexSet :=
    congrArg Hypergraph.vertexSet hB
  have hEB : p.2.edgeSet = (GM10.locationCore G ℒ ∪
      Hypergraph.biUnion (hℒ.finite.toFinset.filter (· ≠ p)) Prod.fst).edgeSet :=
    congrArg Hypergraph.edgeSet hB
  have herase : hℒ.finite.toFinset.erase p = hℒ.finite.toFinset.filter (· ≠ p) :=
    Finset.filter_ne' hℒ.finite.toFinset p |>.symm
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq h1 h2 ?_ ?_
  · change (locationStepSide G hℒ hℒ.finite.toFinset p).vertexSet = p.2.vertexSet
    rw [hVB, ← herase]
    ext v
    simp [locationStepSide, mapInl, biUnion]
  · ext e
    cases e with
    | inl e₀ =>
      simp only [locationStepSide, GM10.union_edgeSet, mapInl, biUnion,
        Finset.sdiff_self, Finset.erase_empty, Finset.notMem_empty, Set.iUnion_of_empty,
        Set.iUnion_empty, Set.union_empty, Set.mem_union, Set.mem_image, Sum.inl.injEq,
        exists_eq_right, Set.mem_iUnion, herase]
      rw [hEB]
      simp [biUnion]
    | inr q =>
      simp [locationStepSide, mapInl, biUnion]

open Classical in
theorem isSeparation_locationStep_of_mem {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ)
    {S : Finset (Hypergraph α β × Hypergraph α β)} (hS : S ⊆ hℒ.finite.toFinset)
    {p : Hypergraph α β × Hypergraph α β} (hpS : p ∈ S) :
    (locationStepHypergraph G hℒ S).IsSeparation
      (mapInl _ p.1) (locationStepSide G hℒ S p) ∧
    (mapInl (Hypergraph α β × Hypergraph α β) p.1 ∩ locationStepSide G hℒ S p).vertexSet =
      (p.1 ∩ p.2).vertexSet := by
  have hp : p ∈ ℒ := hℒ.finite.mem_toFinset.1 (hS hpS)
  have hHp_amb := mapInl_le_locationAmbient ℒ (hℒ.isSeparation hp).left_le
  have hSide_amb := locationStepSide_le_ambient hℒ hS p
  have hStep_amb := locationStepHypergraph_le_ambient hℒ hS
  have hp_not_sdiff : p ∉ hℒ.finite.toFinset \ S := fun h ↦ (Finset.mem_sdiff.1 h).2 hpS
  have herase_sdiff : (hℒ.finite.toFinset \ S).erase p = hℒ.finite.toFinset \ S :=
    Finset.erase_eq_of_notMem hp_not_sdiff
  have hV_union : (mapInl (Hypergraph α β × Hypergraph α β) p.1).vertexSet ∪
      (locationStepSide G hℒ S p).vertexSet =
      (locationStepHypergraph G hℒ S).vertexSet := by
    ext v
    simp only [locationStepSide, locationStepHypergraph, GM10.union_vertexSet, mapInl, biUnion,
      herase_sdiff, Set.mem_union, Set.mem_iUnion, Finset.mem_erase]
    constructor
    · rintro (hvp | (hvc | ⟨q, ⟨hq_ne, hqS⟩, hvq⟩) | hrest)
      · exact Or.inl (Or.inr ⟨p, hpS, hvp⟩)
      · exact Or.inl (Or.inl hvc)
      · exact Or.inl (Or.inr ⟨q, hqS, hvq⟩)
      · exact Or.inr hrest
    · rintro ((hvc | ⟨q, hqS, hvq⟩) | hrest)
      · exact Or.inr (Or.inl (Or.inl hvc))
      · by_cases hqp : q = p
        · exact Or.inl (hqp ▸ hvq)
        · exact Or.inr (Or.inl (Or.inr ⟨q, ⟨hqp, hqS⟩, hvq⟩))
      · exact Or.inr (Or.inr hrest)
  have hE_union : (mapInl (Hypergraph α β × Hypergraph α β) p.1).edgeSet ∪
      (locationStepSide G hℒ S p).edgeSet =
      (locationStepHypergraph G hℒ S).edgeSet := by
    ext e
    simp only [locationStepSide, locationStepHypergraph, GM10.union_edgeSet, biUnion,
      herase_sdiff, Set.mem_union, Set.mem_iUnion, Finset.mem_erase]
    constructor
    · rintro (hep | (hec | ⟨q, ⟨hq_ne, hqS⟩, heq⟩) | hrest)
      · exact Or.inl (Or.inr ⟨p, hpS, hep⟩)
      · exact Or.inl (Or.inl hec)
      · exact Or.inl (Or.inr ⟨q, hqS, heq⟩)
      · exact Or.inr hrest
    · rintro ((hec | ⟨q, hqS, heq⟩) | hrest)
      · exact Or.inr (Or.inl (Or.inl hec))
      · by_cases hqp : q = p
        · exact Or.inl (hqp ▸ heq)
        · exact Or.inr (Or.inl (Or.inr ⟨q, ⟨hqp, hqS⟩, heq⟩))
      · exact Or.inr (Or.inr hrest)
  have hle_left : mapInl _ p.1 ≤ locationStepHypergraph G hℒ S :=
    (GM10.le_iff_of_le hHp_amb hStep_amb).2
      ⟨hV_union ▸ Set.subset_union_left, hE_union ▸ Set.subset_union_left⟩
  have hle_right : locationStepSide G hℒ S p ≤ locationStepHypergraph G hℒ S :=
    (GM10.le_iff_of_le hSide_amb hStep_amb).2
      ⟨hV_union ▸ Set.subset_union_right, hE_union ▸ Set.subset_union_right⟩
  have hE_inter : (mapInl (Hypergraph α β × Hypergraph α β) p.1).edgeSet ∩
      (locationStepSide G hℒ S p).edgeSet = ∅ := by
    ext e
    simp only [locationStepSide, GM10.union_edgeSet, mapInl, biUnion, locationHeartEdge,
      Set.mem_inter_iff, Set.mem_image, Set.mem_union, Set.mem_iUnion, Finset.mem_erase,
      Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨e₀, he₀, rfl⟩, (⟨_, hec, heq⟩ | ⟨q, ⟨hq_ne, hqS⟩, _, heq_mem, heq⟩) | ⟨q, _, heq⟩⟩
    · cases heq
      exact Set.disjoint_left.1 ((theorem_2_3_1 hℒ).2.1 hp) he₀ hec
    · cases heq
      have hq_ℒ : q ∈ ℒ := hℒ.finite.mem_toFinset.1 (hS hqS)
      exact Set.disjoint_left.1 ((theorem_2_3_1 hℒ).1 hp hq_ℒ (Ne.symm hq_ne)) he₀ heq_mem
    · cases heq
  have hsep : (locationStepHypergraph G hℒ S).IsSeparation
      (mapInl _ p.1) (locationStepSide G hℒ S p) :=
    (GM10.isSeparation_iff_of_le hle_left hle_right).2 ⟨hV_union, hE_union, hE_inter⟩
  refine ⟨hsep, ?_⟩
  ext v
  simp only [GM10.inter_vertexSet, locationStepSide, GM10.union_vertexSet, mapInl, biUnion,
    locationHeartEdge, Set.mem_inter_iff, Set.mem_union, Set.mem_iUnion, Finset.mem_erase]
  constructor
  · rintro ⟨hvp₁, (hvc | ⟨q, ⟨hq_ne, hqS⟩, hvq⟩) | ⟨q, ⟨_, hq_sdiff⟩, hvq⟩⟩
    · have hv_inter : v ∈ (p.1 ∩ GM10.locationCore G ℒ).vertexSet := ⟨hvp₁, hvc⟩
      rw [(theorem_2_3_2 hℒ hp).2] at hv_inter
      exact hv_inter
    · have hq_ℒ : q ∈ ℒ := hℒ.finite.mem_toFinset.1 (hS hqS)
      have hv_core : v ∈ (GM10.locationCore G ℒ).vertexSet :=
        (theorem_2_3_3 hℒ hp hq_ℒ (Ne.symm hq_ne)).1.vertexSet_subset ⟨hvp₁, hvq⟩
      have hv_inter : v ∈ (p.1 ∩ GM10.locationCore G ℒ).vertexSet := ⟨hvp₁, hv_core⟩
      rw [(theorem_2_3_2 hℒ hp).2] at hv_inter
      exact hv_inter
    · have hq_ℒ : q ∈ ℒ := hℒ.finite.mem_toFinset.1 (Finset.sdiff_subset hq_sdiff)
      have hv_core : v ∈ (GM10.locationCore G ℒ).vertexSet := by
        have h := (theorem_2_3_2 hℒ hq_ℒ).2
        have hsub : (q.1 ∩ q.2).vertexSet ⊆ (GM10.locationCore G ℒ).vertexSet := by
          rw [← h]
          exact Set.inter_subset_right
        exact hsub hvq
      have hv_inter : v ∈ (p.1 ∩ GM10.locationCore G ℒ).vertexSet := ⟨hvp₁, hv_core⟩
      rw [(theorem_2_3_2 hℒ hp).2] at hv_inter
      exact hv_inter
  · intro hv_inter
    have hv_core : v ∈ (p.1 ∩ GM10.locationCore G ℒ).vertexSet := by
      rwa [(theorem_2_3_2 hℒ hp).2]
    exact ⟨hv_inter.1, Or.inl (Or.inl hv_core.2)⟩

open Classical in
theorem isSeparation_locationStep_of_notMem {G : Hypergraph α β}
    {ℒ : Set (Hypergraph α β × Hypergraph α β)} (hℒ : GM10.IsLocation G ℒ)
    {S : Finset (Hypergraph α β × Hypergraph α β)} (hS : S ⊆ hℒ.finite.toFinset)
    {p : Hypergraph α β × Hypergraph α β} (hp : p ∈ ℒ) (hpS : p ∉ S) :
    (locationStepHypergraph G hℒ S).IsSeparation
      (locationHeartEdge p) (locationStepSide G hℒ S p) ∧
    (locationHeartEdge p ∩ locationStepSide G hℒ S p).vertexSet =
      (p.1 ∩ p.2).vertexSet ∧
    (locationStepSide G hℒ S p).vertexSet =
      (locationStepHypergraph G hℒ S).vertexSet := by
  have hp_sdiff : p ∈ hℒ.finite.toFinset \ S :=
    Finset.mem_sdiff.2 ⟨hℒ.finite.mem_toFinset.2 hp, hpS⟩
  have hCp_amb := locationHeartEdge_le_locationAmbient hℒ hp
  have hSide_amb := locationStepSide_le_ambient hℒ hS p
  have hStep_amb := locationStepHypergraph_le_ambient hℒ hS
  have herase_S : S.erase p = S := Finset.erase_eq_of_notMem hpS
  have hsub_core : (p.1 ∩ p.2).vertexSet ⊆ (GM10.locationCore G ℒ).vertexSet := by
    rw [← (theorem_2_3_2 hℒ hp).2]
    exact Set.inter_subset_right
  have hV_side_eq : (locationStepSide G hℒ S p).vertexSet =
      (locationStepHypergraph G hℒ S).vertexSet := by
    ext v
    simp only [locationStepSide, locationStepHypergraph, GM10.union_vertexSet, mapInl, biUnion,
      herase_S, Set.mem_union, Set.mem_iUnion, Finset.mem_erase, locationHeartEdge]
    constructor
    · rintro (hleft | ⟨q, ⟨_, hq_sdiff⟩, hvq⟩)
      · exact Or.inl hleft
      · exact Or.inr ⟨q, hq_sdiff, hvq⟩
    · rintro (hleft | ⟨q, hq_sdiff, hvq⟩)
      · exact Or.inl hleft
      · by_cases hqp : q = p
        · subst hqp
          exact Or.inl (Or.inl (hsub_core hvq))
        · exact Or.inr ⟨q, ⟨hqp, hq_sdiff⟩, hvq⟩
  have hV_union : (locationHeartEdge p).vertexSet ∪
      (locationStepSide G hℒ S p).vertexSet =
      (locationStepHypergraph G hℒ S).vertexSet := by
    rw [hV_side_eq, Set.union_eq_right]
    exact fun v hv ↦ Or.inl (Or.inl (hsub_core hv))
  have hE_union : (locationHeartEdge p).edgeSet ∪
      (locationStepSide G hℒ S p).edgeSet =
      (locationStepHypergraph G hℒ S).edgeSet := by
    ext e
    simp only [locationStepSide, locationStepHypergraph, GM10.union_edgeSet, biUnion,
      herase_S, Set.mem_union, Set.mem_iUnion, Finset.mem_erase, locationHeartEdge,
      Set.mem_singleton_iff]
    constructor
    · rintro (rfl | hleft | ⟨q, ⟨_, hq_sdiff⟩, rfl⟩)
      · exact Or.inr ⟨p, hp_sdiff, rfl⟩
      · exact Or.inl hleft
      · exact Or.inr ⟨q, hq_sdiff, rfl⟩
    · rintro (hleft | ⟨q, hq_sdiff, rfl⟩)
      · exact Or.inr (Or.inl hleft)
      · by_cases hqp : q = p
        · exact Or.inl (hqp ▸ rfl)
        · exact Or.inr (Or.inr ⟨q, ⟨hqp, hq_sdiff⟩, rfl⟩)
  have hle_left : locationHeartEdge p ≤ locationStepHypergraph G hℒ S :=
    (GM10.le_iff_of_le hCp_amb hStep_amb).2
      ⟨hV_union ▸ Set.subset_union_left, hE_union ▸ Set.subset_union_left⟩
  have hle_right : locationStepSide G hℒ S p ≤ locationStepHypergraph G hℒ S :=
    (GM10.le_iff_of_le hSide_amb hStep_amb).2
      ⟨hV_union ▸ Set.subset_union_right, hE_union ▸ Set.subset_union_right⟩
  have hE_inter : (locationHeartEdge p).edgeSet ∩
      (locationStepSide G hℒ S p).edgeSet = ∅ := by
    ext e
    simp only [locationStepSide, GM10.union_edgeSet, mapInl, biUnion, locationHeartEdge,
      Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_image,
      Set.mem_iUnion, Finset.mem_erase, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, (⟨_, _, heq⟩ | ⟨_, _, _, _, heq⟩) | ⟨q, ⟨hq_ne, _⟩, heq⟩⟩
    · cases heq
    · cases heq
    · exact hq_ne (Sum.inr.inj heq).symm
  have hsep : (locationStepHypergraph G hℒ S).IsSeparation
      (locationHeartEdge p) (locationStepSide G hℒ S p) :=
    (GM10.isSeparation_iff_of_le hle_left hle_right).2 ⟨hV_union, hE_union, hE_inter⟩
  have hV_inter : (locationHeartEdge p ∩ locationStepSide G hℒ S p).vertexSet =
      (p.1 ∩ p.2).vertexSet := by
    change (p.1 ∩ p.2).vertexSet ∩ (locationStepSide G hℒ S p).vertexSet = (p.1 ∩ p.2).vertexSet
    exact Set.inter_eq_left.2 fun v hv ↦ Or.inl (Or.inl (hsub_core hv))
  exact ⟨hsep, hV_inter, hV_side_eq⟩

open Classical in
/-- **Claim (1)** in the proof of Graph Minors XVIII, (3.4) (page 84):
For every `S ⊆ ℒ`, if `locationHeart G ℒ` has a tangle `𝒯₀` of order `θ ≥ 2`, then there is a
tangle `𝒯_S` in `locationStepHypergraph G hℒ S` of order `θ` such that
`(mapInl _ p.1, locationStepSide G hℒ S p) ∈ 𝒯_S` for all `p ∈ S`. -/
theorem lemma_3_4_claim_1
    {G : Hypergraph α β} {ℒ : Set (Hypergraph α β × Hypergraph α β)}
    (hℒ : GM10.IsLocation G ℒ)
    (htitanic : ∀ ⦃p⦄, p ∈ ℒ → GM10.IsTitanic G p.1 p.2)
    {θ : ℕ} (hθ : 2 ≤ θ) (hord : locationOrder ℒ < θ)
    {𝒯₀ : Set (Hypergraph α (β ⊕ (Hypergraph α β × Hypergraph α β)) ×
      Hypergraph α (β ⊕ (Hypergraph α β × Hypergraph α β)))}
    (h𝒯₀ : GM10.IsTangle (locationHeart G ℒ) θ 𝒯₀)
    (S : Finset (Hypergraph α β × Hypergraph α β)) (hS : S ⊆ hℒ.finite.toFinset) :
    ∃ 𝒯_S, GM10.IsTangle (locationStepHypergraph G hℒ S) θ 𝒯_S ∧
      ∀ p ∈ S, (mapInl _ p.1, locationStepSide G hℒ S p) ∈ 𝒯_S := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨𝒯₀, ?_, fun _ h ↦ (Finset.notMem_empty _ h).elim⟩
    rwa [locationStepHypergraph_empty hℒ]
  | @insert p S hpS ih =>
    have hS_sub : S ⊆ hℒ.finite.toFinset := (Finset.subset_insert p S).trans hS
    have hp_ℒ : p ∈ ℒ := hℒ.finite.mem_toFinset.1 (hS (Finset.mem_insert_self p S))
    obtain ⟨𝒯_S, h𝒯_S, hmem_S⟩ := ih hS_sub
    let D := locationStepSide G hℒ S p
    have hd_eq : locationStepSide G hℒ (insert p S) p = D :=
      locationStepSide_insert_self hℒ hpS
    have ⟨hsep_Cp, hV_Cp, hVD_eq⟩ := isSeparation_locationStep_of_notMem hℒ hS_sub hp_ℒ hpS
    have hord_p : separationOrder p.1 p.2 < θ :=
      separationOrder_lt_of_locationOrder_lt hℒ hord hp_ℒ
    have hord_Cp : separationOrder (locationHeartEdge p) D < θ := by
      unfold separationOrder
      rwa [hV_Cp]
    have hDCp_not : (D, locationHeartEdge p) ∉ 𝒯_S := fun hm ↦
      h𝒯_S.axiom3 hm hVD_eq
    have hCpD_mem : (locationHeartEdge p, D) ∈ 𝒯_S :=
      (h𝒯_S.axiom1 hsep_Cp hord_Cp).resolve_right hDCp_not
    have ⟨hsep_Ap_ins, hV_Ap_ins⟩ :=
      isSeparation_locationStep_of_mem hℒ hS (Finset.mem_insert_self p S)
    rw [hd_eq] at hsep_Ap_ins hV_Ap_ins
    -- Show `GM10.IsTitanic (locationStepHypergraph G hℒ (insert p S)) (mapInl _ p.1) D` by (3.1)
    have htit_p : GM10.IsTitanic G p.1 p.2 := htitanic hp_ℒ
    have htit_Ap : GM10.IsTitanic (locationStepHypergraph G hℒ (insert p S)) (mapInl _ p.1) D := by
      refine ⟨hsep_Ap_ins, fun X Y Z hX hY hZ hU hdXY hdYZ hdXZ ↦ ?_⟩
      have hX' : comapInl X ≤ p.1 := by
        refine ⟨hX.vertexSet_subset, fun e he ↦ ?_, fun e he ↦ ?_⟩
        · rcases hX.edgeSet_subset he with ⟨e', he', heq⟩
          cases heq
          exact he'
        · exact hX.ends_eq (Sum.inl e) he
      have hY' : comapInl Y ≤ p.1 := by
        refine ⟨hY.vertexSet_subset, fun e he ↦ ?_, fun e he ↦ ?_⟩
        · rcases hY.edgeSet_subset he with ⟨e', he', heq⟩
          cases heq
          exact he'
        · exact hY.ends_eq (Sum.inl e) he
      have hZ' : comapInl Z ≤ p.1 := by
        refine ⟨hZ.vertexSet_subset, fun e he ↦ ?_, fun e he ↦ ?_⟩
        · rcases hZ.edgeSet_subset he with ⟨e', he', heq⟩
          cases heq
          exact he'
        · exact hZ.ends_eq (Sum.inl e) he
      have hU' : comapInl X ∪ comapInl Y ∪ comapInl Z = p.1 := by
        have h := congrArg comapInl hU
        rwa [comapInl_union, comapInl_union, comapInl_mapInl] at h
      have hdXY' : Disjoint (comapInl X).edgeSet (comapInl Y).edgeSet :=
        Set.disjoint_iff.2 fun e ⟨hx, hy⟩ ↦ Set.disjoint_iff.1 hdXY ⟨hx, hy⟩
      have hdYZ' : Disjoint (comapInl Y).edgeSet (comapInl Z).edgeSet :=
        Set.disjoint_iff.2 fun e ⟨hy, hz⟩ ↦ Set.disjoint_iff.1 hdYZ ⟨hy, hz⟩
      have hdXZ' : Disjoint (comapInl X).edgeSet (comapInl Z).edgeSet :=
        Set.disjoint_iff.2 fun e ⟨hx, hz⟩ ↦ Set.disjoint_iff.1 hdXZ ⟨hx, hz⟩
      have v_inter_eq : ∀ {H : Hypergraph α (β ⊕ (Hypergraph α β × Hypergraph α β))},
          H ≤ mapInl _ p.1 →
          (H ∩ D).vertexSet = ((comapInl H) ∩ p.2).vertexSet := by
        intro H hH
        ext v
        simp only [GM10.inter_vertexSet, Set.mem_inter_iff]
        constructor
        · rintro ⟨hvH, hvD⟩
          have hv_p1D : v ∈ (mapInl _ p.1 ∩ D).vertexSet := ⟨hH.vertexSet_subset hvH, hvD⟩
          rw [hV_Ap_ins] at hv_p1D
          exact ⟨hvH, hv_p1D.2⟩
        · rintro ⟨hvH, hvp2⟩
          have hv_p12 : v ∈ (p.1 ∩ p.2).vertexSet := ⟨hH.vertexSet_subset hvH, hvp2⟩
          rw [← hV_Ap_ins] at hv_p12
          exact ⟨hvH, hv_p12.2⟩
      have h1 := v_inter_eq (GM10.union_le hX hY)
      have h2 := v_inter_eq (GM10.union_le hY hZ)
      have h3 := v_inter_eq (GM10.union_le hZ hX)
      rw [comapInl_union] at h1 h2 h3
      rw [h1, h2, h3]
      exact htit_p.2 hX' hY' hZ' hU' hdXY' hdYZ' hdXZ'
    have hV_eq_CD : (locationHeartEdge p ∩ D).vertexSet = (mapInl _ p.1 ∩ D).vertexSet := by
      rw [hV_Cp, hV_Ap_ins]
    let 𝒯_ins := GM10.titanicTransferredTangle
      (locationStepHypergraph G hℒ (insert p S)) D 𝒯_S θ
    have h𝒯_ins : GM10.IsTangle (locationStepHypergraph G hℒ (insert p S)) θ 𝒯_ins :=
      theorem_3_2_proof hsep_Cp htit_Ap hV_eq_CD h𝒯_S hθ hCpD_mem
    refine ⟨𝒯_ins, h𝒯_ins, fun q hq ↦ ?_⟩
    have ⟨hsep_Aq_ins, hV_Aq_ins⟩ := isSeparation_locationStep_of_mem hℒ hS hq
    have hq_ℒ : q ∈ ℒ := hℒ.finite.mem_toFinset.1 (hS hq)
    have hord_Aq_ins : separationOrder (mapInl _ q.1)
        (locationStepSide G hℒ (insert p S) q) < θ := by
      unfold separationOrder
      rw [hV_Aq_ins]
      exact separationOrder_lt_of_locationOrder_lt hℒ hord hq_ℒ
    rcases Finset.mem_insert.1 hq with rfl | hqS
    · refine ⟨hsep_Aq_ins, hord_Aq_ins, (locationHeartEdge q, D), hCpD_mem, ?_⟩
      rw [hsep_Cp.edgeSet_inter_eq, ← hd_eq, hsep_Aq_ins.edgeSet_inter_eq]
    · exact ⟨hsep_Aq_ins, hord_Aq_ins, (mapInl _ q.1, locationStepSide G hℒ S q),
        hmem_S q hqS, rfl⟩

/-- Pulls back a tangle on `mapInl γ G` to a tangle on `G`. -/
theorem isTangle_comapInl {γ : Type*} {G : Hypergraph α β} {θ : ℕ}
    {𝒯' : Set (Hypergraph α (β ⊕ γ) × Hypergraph α (β ⊕ γ))}
    (h𝒯' : GM10.IsTangle (mapInl γ G) θ 𝒯') :
    GM10.IsTangle G θ
      {p | (mapInl γ p.1, mapInl γ p.2) ∈ 𝒯'} where
  one_le := h𝒯'.one_le
  isSeparation A B h := by
    have hsep' := h𝒯'.isSeparation h
    have hA : A ≤ G := by
      refine ⟨hsep'.left_le.vertexSet_subset, ?_, ?_⟩
      · intro e he
        rcases hsep'.left_le.edgeSet_subset ⟨e, he, rfl⟩ with ⟨e', he', heq⟩
        cases heq
        exact he'
      · intro e he
        exact hsep'.left_le.ends_eq (Sum.inl e) ⟨e, he, rfl⟩
    have hB : B ≤ G := by
      refine ⟨hsep'.right_le.vertexSet_subset, ?_, ?_⟩
      · intro e he
        rcases hsep'.right_le.edgeSet_subset ⟨e, he, rfl⟩ with ⟨e', he', heq⟩
        cases heq
        exact he'
      · intro e he
        exact hsep'.right_le.ends_eq (Sum.inl e) ⟨e, he, rfl⟩
    rw [GM10.isSeparation_iff_of_le hA hB]
    refine ⟨hsep'.vertexSet_union, ?_, ?_⟩
    · have hE := congrArg (Set.preimage Sum.inl) hsep'.edgeSet_union
      simpa [mapInl, Set.preimage_image_eq _ Sum.inl_injective] using hE
    · have hI := congrArg (Set.preimage Sum.inl) hsep'.edgeSet_inter_eq
      simpa [mapInl, Set.preimage_image_eq _ Sum.inl_injective] using hI
  order_lt A B h := h𝒯'.order_lt h
  axiom1 A B hsep hord := by
    have hsep' : (mapInl γ G).IsSeparation (mapInl γ A) (mapInl γ B) := by
      rw [GM10.isSeparation_iff_of_le (mapInl_mono γ hsep.left_le) (mapInl_mono γ hsep.right_le)]
      refine ⟨hsep.vertexSet_union, ?_, ?_⟩
      · simp [mapInl, ← Set.image_union, hsep.edgeSet_union]
      · have hE : A.edgeSet ∩ B.edgeSet = ∅ := hsep.edgeSet_inter_eq
        change Sum.inl '' A.edgeSet ∩ Sum.inl '' B.edgeSet = ∅
        rw [← Set.image_inter Sum.inl_injective, hE, Set.image_empty]
    exact h𝒯'.axiom1 hsep' hord
  axiom2 A₁ B₁ A₂ B₂ A₃ B₃ h₁ h₂ h₃ hU := by
    apply h𝒯'.axiom2 h₁ h₂ h₃
    rw [← mapInl_union, ← mapInl_union, hU]
  axiom3 A B h hVA := h𝒯'.axiom3 h hVA

/-- **Graph Minors XVIII, (3.4)** (page 84):
"**3.4.** *Let $\mathscr{L}$ be a location in a hypergraph $G$, such that each
$(A, B) \in \mathscr{L}$ is titanic, and $\mathscr{L}$ has order $< \theta$, where $\theta \ge 2$.
Then either there is a tangle $\mathscr{T}$ in $G$ of order $\theta$ with
$\mathscr{L} \subseteq \mathscr{T}$, or $\mathscr{L}$ has tree-width $\le \frac{3}{2}\theta$.*" -/
theorem theorem_3_4_proof
    {G : Hypergraph α β} {ℒ : Set (Hypergraph α β × Hypergraph α β)}
    (hℒ : GM10.IsLocation G ℒ)
    (htitanic : ∀ ⦃p⦄, p ∈ ℒ → GM10.IsTitanic G p.1 p.2)
    {θ : ℕ} (hθ : 2 ≤ θ) (hord : locationOrder ℒ < θ) :
    (∃ 𝒯, GM10.IsTangle G θ 𝒯 ∧ ℒ ⊆ 𝒯) ∨
      2 * locationTreeWidth G ℒ ≤ 3 * (θ : ℤ) := by
  classical
  by_cases hex_H : ∃ 𝒯₀, GM10.IsTangle (locationHeart G ℒ) θ 𝒯₀
  · left
    obtain ⟨𝒯₀, h𝒯₀⟩ := hex_H
    obtain ⟨𝒯_full, h𝒯_full, hmem_full⟩ :=
      lemma_3_4_claim_1 hℒ htitanic hθ hord h𝒯₀ hℒ.finite.toFinset Finset.Subset.rfl
    rw [locationStepHypergraph_full hℒ] at h𝒯_full
    refine ⟨{p | (mapInl _ p.1, mapInl _ p.2) ∈ 𝒯_full}, isTangle_comapInl h𝒯_full, ?_⟩
    intro p hp
    have h := hmem_full p (hℒ.finite.mem_toFinset.2 hp)
    rwa [locationStepSide_full hℒ hp] at h
  · right
    have hno : ∀ ⦃θ' : ℕ⦄ ⦃𝒯₀ : Set _⦄,
        GM10.IsTangle (locationHeart G ℒ) θ' 𝒯₀ → θ' < θ := by
      intro θ' 𝒯₀ h𝒯₀
      by_contra! hle
      exact hex_H ⟨GM10.truncation 𝒯₀ θ, h𝒯₀.truncation (by omega) hle⟩
    exact theorem_2_2_proof (locationHeart G ℒ) (by omega) hno

end GraphMinor.GM18
