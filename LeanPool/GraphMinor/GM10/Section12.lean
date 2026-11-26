/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs2
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM10.Section8
import Mathlib.Combinatorics.Matroid.IndepAxioms

/-!
# Graph Minors X, Section 12: Tangles and Matroids

This file formalizes Section 12 ("Tangles and Matroids", pages 188–190) of Robertson and Seymour,
*Graph Minors. X. Obstructions to Tree-Decomposition*, J. Combin. Theory Ser. B **52** (1991),
153–190:

- **(12.1) (`theorem_12_1`, page 188):** for any tangle `𝒯` of order `θ` in a hypergraph `G`, the
  tangle rank function `r(X) = tangleRank 𝒯 θ X` satisfies the matroid rank axioms on `V(G)`
  (`IsMatroidRankOn G.vertexSet (tangleRank 𝒯 θ)`).
- **(12.2) (`theorem_12_2`, page 189):** the free sets (`IsFreeSet G 𝒯 θ`) are the independent sets
  of a matroid (`tangleMatroid G h𝒯`) on `V(G)` with rank function `tangleRank 𝒯 θ`.
-/

namespace GraphMinor.GM10

open Hypergraph Set Matroid
open scoped Sym2

variable {α β : Type*}

public section

/-! ## Basic Properties of `tangleRank` -/

/-- If `(A, B) ∈ 𝒯` and `X ⊆ V(A)`, then `tangleRank 𝒯 θ X ≤ separationOrder A B`
(Graph Minors X, Section 12, page 188). -/
theorem tangleRank_le_separationOrder {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    {X : Set α} {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯) (hX : X ⊆ A.vertexSet) :
    tangleRank 𝒯 θ X ≤ separationOrder A B := by
  classical
  have hex : ∃ p ∈ 𝒯, X ⊆ p.1.vertexSet := ⟨(A, B), hAB, hX⟩
  rw [tangleRank, ite_eq_left hex]
  exact Nat.sInf_le ⟨(A, B), hAB, hX, rfl⟩

/-- For any tangle `𝒯` of order `θ` in `G` and any set `X`, `tangleRank 𝒯 θ X ≤ θ`
(Graph Minors X, Section 12, page 189). -/
theorem tangleRank_le_order {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) (X : Set α) :
    tangleRank 𝒯 θ X ≤ θ := by
  classical
  by_cases hex : ∃ p ∈ 𝒯, X ⊆ p.1.vertexSet
  · rcases hex with ⟨⟨A, B⟩, hAB, hX⟩
    exact (tangleRank_le_separationOrder hAB hX).trans (h𝒯.order_lt hAB).le
  · rw [tangleRank, ite_eq_right hex]

/-- If `tangleRank 𝒯 θ X < θ`, then there exists `(A, B) ∈ 𝒯` with `X ⊆ V(A)` and
`separationOrder A B = tangleRank 𝒯 θ X` (Graph Minors X, Section 12, page 189). -/
theorem exists_mem_of_tangleRank_lt {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    {X : Set α} (hlt : tangleRank 𝒯 θ X < θ) :
    ∃ A B : Hypergraph α β, (A, B) ∈ 𝒯 ∧ X ⊆ A.vertexSet ∧
      separationOrder A B = tangleRank 𝒯 θ X := by
  classical
  by_cases hex : ∃ p ∈ 𝒯, X ⊆ p.1.vertexSet
  · have hne : {k : ℕ | ∃ p ∈ 𝒯, X ⊆ p.1.vertexSet ∧ separationOrder p.1 p.2 = k}.Nonempty := by
      rcases hex with ⟨p, hp, hX⟩
      exact ⟨separationOrder p.1 p.2, p, hp, hX, rfl⟩
    obtain ⟨⟨A, B⟩, hAB, hX, hord⟩ := Nat.sInf_mem hne
    refine ⟨A, B, hAB, hX, ?_⟩
    rw [tangleRank, ite_eq_left hex]
    exact hord
  · rw [tangleRank, ite_eq_right hex] at hlt
    exact (lt_irrefl θ hlt).elim

/-- Monotonicity of `tangleRank`: if `X ⊆ Y`, then `tangleRank 𝒯 θ X ≤ tangleRank 𝒯 θ Y`
(Graph Minors X, Section 12, (12.1)(iii), page 189). -/
theorem tangleRank_mono {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {X Y : Set α} (hXY : X ⊆ Y) :
    tangleRank 𝒯 θ X ≤ tangleRank 𝒯 θ Y := by
  by_cases hlt : tangleRank 𝒯 θ Y < θ
  · obtain ⟨A, B, hAB, hY, hord⟩ := exists_mem_of_tangleRank_lt hlt
    rw [← hord]
    exact tangleRank_le_separationOrder hAB (hXY.trans hY)
  · push Not at hlt
    exact (tangleRank_le_order h𝒯 X).trans hlt

/-! ## Proof of Graph Minors X, (12.1) -/

/-- For `X ⊆ V(G)`, the edgeless subhypergraph `K` with `V(K) = X` and `E(K) = ∅` forms a
separation `(K, G)` of `G` of order `|X|` (Graph Minors X, Section 12, proof of (12.1), page 189).
-/
private def edgelessSub (G : Hypergraph α β) (X : Set α) (hX : X ⊆ G.vertexSet) :
    Hypergraph α β where
  vertexSet := X
  edgeSet := ∅
  Inc _ _ := False
  vertex_mem_of_inc _ _ h := h.elim
  edge_mem_of_inc _ _ h := h.elim
  vertexSet_finite := G.vertexSet_finite.subset hX
  edgeSet_finite := finite_empty

private lemma isSeparation_edgelessSub (G : Hypergraph α β) {X : Set α} (hX : X ⊆ G.vertexSet) :
    G.IsSeparation (edgelessSub G X hX) G := by
  have hle : edgelessSub G X hX ≤ G :=
    ⟨hX, empty_subset _, fun _ he ↦ he.elim⟩
  rw [isSeparation_iff_of_le hle le_rfl]
  refine ⟨?_, ?_, ?_⟩
  · change X ∪ G.vertexSet = G.vertexSet
    exact union_eq_right.2 hX
  · change ∅ ∪ G.edgeSet = G.edgeSet
    exact empty_union _
  · change ∅ ∩ G.edgeSet = ∅
    exact empty_inter _

private lemma separationOrder_edgelessSub (G : Hypergraph α β) {X : Set α} (hX : X ⊆ G.vertexSet) :
    separationOrder (edgelessSub G X hX) G = X.ncard := by
  unfold separationOrder
  have hinter : (edgelessSub G X hX ∩ G).vertexSet = X := by
    change X ∩ G.vertexSet = X
    exact inter_eq_left.2 hX
  rw [hinter]

/-- **Graph Minors X, (12.1)** (pages 188–189):
"Let $\mathscr{T}$ be a tangle in a hypergraph $G$, of order $\theta$. For $X \subseteq
V(G)$, let us define $r(X)$ to be the least order of a separation $(A, B) \in \mathscr{T}$
with $X \subseteq V(A)$, if one exists, and $\theta$ otherwise. (12.1) *$r$ is the rank
function of a matroid on $V(G)$." -/
theorem theorem_12_1_proof (G : Hypergraph α β) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    IsMatroidRankOn G.vertexSet (tangleRank 𝒯 θ) where
  le_ncard := by
    intro X hX
    -- Follow the paper (page 189): "Since `r(X) ≤ θ`, we may assume that `|X| < θ`. Let `K` be the
    -- hypergraph with `V(K) = X`, `E(K) = ∅`. Since `(G, K) ∉ 𝒯` and has order `< θ`, it follows
    -- that `(K, G) ∈ 𝒯`, and so `r(X) ≤ |V(K ∩ G)| ≤ |X|`."
    by_cases hcard : X.ncard < θ
    · let K := edgelessSub G X hX
      have hsep : G.IsSeparation K G := isSeparation_edgelessSub G hX
      have hord : separationOrder K G < θ := by
        rwa [separationOrder_edgelessSub G hX]
      have hGK_not : (G, K) ∉ 𝒯 := fun hGK ↦ h𝒯.axiom3 hGK rfl
      have hKG : (K, G) ∈ 𝒯 := (h𝒯.axiom1 hsep hord).resolve_right hGK_not
      have hle := tangleRank_le_separationOrder (θ := θ) hKG (Subset.rfl : X ⊆ K.vertexSet)
      rwa [separationOrder_edgelessSub G hX] at hle
    · push Not at hcard
      exact (tangleRank_le_order h𝒯 X).trans hcard
  mono := fun _ _ hXY _ ↦ tangleRank_mono h𝒯 hXY
  submodular := by
    intro X Y _ _
    -- Follow the paper (page 189): "Since `r(X ∩ Y) ≤ r(Y)` and `r(X ∪ Y) ≤ θ`, we may assume
    -- that `r(X) < θ` and similarly `r(Y) < θ`."
    by_cases hrX : tangleRank 𝒯 θ X < θ
    · by_cases hrY : tangleRank 𝒯 θ Y < θ
      · obtain ⟨A, B, hAB, hXA, hordAB⟩ := exists_mem_of_tangleRank_lt hrX
        obtain ⟨C, D, hCD, hYC, hordCD⟩ := exists_mem_of_tangleRank_lt hrY
        have hsepAB := h𝒯.isSeparation hAB
        have hsepCD := h𝒯.isSeparation hCD
        -- "We claim that `r(X ∩ Y)` is at most the order of `(A ∩ C, B ∪ D)`; for this is true if
        -- `(A ∩ C, B ∪ D)` has order `≥ θ`, and otherwise `(A ∩ C, B ∪ D) ∈ 𝒯`, and the claim
        -- follows since `X ∩ Y ⊆ V(A ∩ C)`."
        have h_inter : tangleRank 𝒯 θ (X ∩ Y) ≤ separationOrder (A ∩ C) (B ∪ D) := by
          by_cases hord : separationOrder (A ∩ C) (B ∪ D) < θ
          · have hsep_inter : G.IsSeparation (A ∩ C) (B ∪ D) :=
              (hsepAB.symm.union_inter hsepCD.symm).symm
            have hmem_inter : (A ∩ C, B ∪ D) ∈ 𝒯 :=
              theorem_2_9_case_1 h𝒯 hAB hsep_inter hord subset_union_left
            exact tangleRank_le_separationOrder hmem_inter (inter_subset_inter hXA hYC)
          · push Not at hord
            exact (tangleRank_le_order h𝒯 (X ∩ Y)).trans hord
        -- "Similarly, `r(X ∪ Y)` is at most the order of `(A ∪ C, B ∩ D)`, by (2.2)."
        have h_union : tangleRank 𝒯 θ (X ∪ Y) ≤ separationOrder (A ∪ C) (B ∩ D) := by
          by_cases hord : separationOrder (A ∪ C) (B ∩ D) < θ
          · have hmem_union : (A ∪ C, B ∩ D) ∈ 𝒯 :=
              theorem_2_2_proof h𝒯 hAB hCD hord
            exact tangleRank_le_separationOrder hmem_union (union_subset_union hXA hYC)
          · push Not at hord
            exact (tangleRank_le_order h𝒯 (X ∪ Y)).trans hord
        -- "Since the sum of the orders of `(A, B)` and `(C, D)` equals the sum of the order of
        -- `(A ∩ C, B ∪ D)` and `(A ∪ C, B ∩ D)`, the result follows."
        have hsum := separationOrder_add_separationOrder hsepAB hsepCD
        omega
      · push Not at hrY
        have h1 : tangleRank 𝒯 θ (X ∪ Y) ≤ tangleRank 𝒯 θ Y :=
          (tangleRank_le_order h𝒯 (X ∪ Y)).trans hrY
        have h2 : tangleRank 𝒯 θ (X ∩ Y) ≤ tangleRank 𝒯 θ X :=
          tangleRank_mono h𝒯 inter_subset_left
        omega
    · push Not at hrX
      have h1 : tangleRank 𝒯 θ (X ∪ Y) ≤ tangleRank 𝒯 θ X :=
        (tangleRank_le_order h𝒯 (X ∪ Y)).trans hrX
      have h2 : tangleRank 𝒯 θ (X ∩ Y) ≤ tangleRank 𝒯 θ Y :=
        tangleRank_mono h𝒯 inter_subset_right
      omega

/-! ## Proof of Graph Minors X, (12.2) -/

/-- A subset `X` is free with respect to `𝒯` if and only if `X ⊆ V(G)` and
`tangleRank 𝒯 θ X = X.ncard` (Graph Minors X, Section 12, page 189). -/
theorem isFreeSet_iff_tangleRank_eq {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) {X : Set α} :
    IsFreeSet G 𝒯 θ X ↔ X ⊆ G.vertexSet ∧ tangleRank 𝒯 θ X = X.ncard := by
  have hmat := theorem_12_1_proof G h𝒯
  constructor
  · rintro ⟨hX, hXθ, hfree⟩
    refine ⟨hX, le_antisymm (hmat.le_ncard hX) ?_⟩
    by_cases hlt : tangleRank 𝒯 θ X < θ
    · obtain ⟨A, B, hAB, hXA, hord⟩ := exists_mem_of_tangleRank_lt hlt
      rw [← hord]
      exact hfree hAB hXA
    · push Not at hlt
      exact hXθ.trans hlt
  · rintro ⟨hX, hr⟩
    refine ⟨hX, ?_, ?_⟩
    · rw [← hr]
      exact tangleRank_le_order h𝒯 X
    · intro A B hAB hXA
      rw [← hr]
      exact tangleRank_le_separationOrder hAB hXA

/-- Submodular closure lemma for `IsMatroidRankOn`: if `I ⊆ E`, `S` is a finite subset of `E \ I`,
and `r (insert e I) ≤ r I` for every `e ∈ S`, then `r (I ∪ S) ≤ r I`. -/
private lemma rank_union_le_of_forall_insert_le {E : Set α} {r : Set α → ℕ}
    (hr : IsMatroidRankOn E r) {I S : Set α} (hI : I ⊆ E) (hS_fin : S.Finite)
    (hS : S ⊆ E \ I) (hins : ∀ e ∈ S, r (insert e I) ≤ r I) :
    r (I ∪ S) ≤ r I := by
  induction S, hS_fin using Set.Finite.induction_on with
  | empty => simp
  | @insert a s ha_notMem _ ih =>
    have haE : a ∈ E ∧ a ∉ I := hS (mem_insert a s)
    have hs_sub : s ⊆ E \ I := (subset_insert a s).trans hS
    have ih' : r (I ∪ s) ≤ r I := ih hs_sub (fun e he ↦ hins e (mem_insert_of_mem a he))
    have ha_le : r (insert a I) ≤ r I := hins a (mem_insert a s)
    have hIs_sub : I ∪ s ⊆ E := union_subset hI (hs_sub.trans sdiff_subset)
    have haI_sub : insert a I ⊆ E := insert_subset haE.1 hI
    have hsubmod := hr.submodular hIs_sub haI_sub
    have hunion : (I ∪ s) ∪ insert a I = I ∪ insert a s := by
      ext x
      simp only [mem_union, mem_insert_iff]
      tauto
    have hinter : (I ∪ s) ∩ insert a I = I := by
      ext x
      simp only [mem_inter_iff, mem_union, mem_insert_iff]
      constructor
      · rintro ⟨hxI | hxs, rfl | hxI⟩
        · exact hxI
        · exact hxI
        · exact (ha_notMem hxs).elim
        · exact hxI
      · intro hxI
        exact ⟨Or.inl hxI, Or.inr hxI⟩
    rw [hunion, hinter] at hsubmod
    omega

/-- The empty set is free with respect to any tangle `𝒯` in `G` (Graph Minors X, Section 12,
page 189). -/
theorem isFreeSet_empty (G : Hypergraph α β) (𝒯 : Set (Hypergraph α β × Hypergraph α β))
    (θ : ℕ) : IsFreeSet G 𝒯 θ ∅ :=
  ⟨empty_subset _, by simp, fun _ _ _ _ ↦ by simp⟩

/-- Any subset of a free set is free (Graph Minors X, Section 12, (12.2), page 189). -/
theorem IsFreeSet.subset {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {I J : Set α} (hJ : IsFreeSet G 𝒯 θ J) (hIJ : I ⊆ J) :
    IsFreeSet G 𝒯 θ I := by
  have hr := theorem_12_1_proof G h𝒯
  rw [isFreeSet_iff_tangleRank_eq h𝒯] at hJ ⊢
  rcases hJ with ⟨hJE, hrJ⟩
  have hIE : I ⊆ G.vertexSet := hIJ.trans hJE
  refine ⟨hIE, ?_⟩
  have hdiffE : J \ I ⊆ G.vertexSet := sdiff_subset.trans hJE
  have hsubmod := hr.submodular hIE hdiffE
  rw [union_sdiff_cancel hIJ, inter_sdiff_self] at hsubmod
  have hrI_le : tangleRank 𝒯 θ I ≤ I.ncard := hr.le_ncard hIE
  have hr_diff_le : tangleRank 𝒯 θ (J \ I) ≤ (J \ I).ncard := hr.le_ncard hdiffE
  have hJ_fin : J.Finite := G.vertexSet_finite.subset hJE
  have hcard_add : I.ncard + (J \ I).ncard = J.ncard := by
    have h := ncard_sdiff_add_ncard_of_subset hIJ hJ_fin
    omega
  omega

/-- Augmentation property for free sets (Graph Minors X, Section 12, (12.2), page 189). -/
theorem IsFreeSet.augment {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {I J : Set α} (hI : IsFreeSet G 𝒯 θ I) (hJ : IsFreeSet G 𝒯 θ J) (hlt : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ IsFreeSet G 𝒯 θ (insert e I) := by
  have hr := theorem_12_1_proof G h𝒯
  rw [isFreeSet_iff_tangleRank_eq h𝒯] at hI hJ
  rcases hI with ⟨hIE, hrI⟩
  rcases hJ with ⟨hJE, hrJ⟩
  by_contra! hnot
  have hins : ∀ e ∈ J \ I, tangleRank 𝒯 θ (insert e I) ≤ tangleRank 𝒯 θ I := by
    intro e ⟨heJ, heI⟩
    have heE : insert e I ⊆ G.vertexSet := insert_subset (hJE heJ) hIE
    have hnot_free : ¬ IsFreeSet G 𝒯 θ (insert e I) := hnot e heJ heI
    rw [isFreeSet_iff_tangleRank_eq h𝒯, not_and] at hnot_free
    have hne : tangleRank 𝒯 θ (insert e I) ≠ (insert e I).ncard := hnot_free heE
    have hle : tangleRank 𝒯 θ (insert e I) ≤ (insert e I).ncard := hr.le_ncard heE
    have hcard_ins : (insert e I).ncard = I.ncard + 1 :=
      ncard_insert_of_notMem heI (G.vertexSet_finite.subset hIE)
    omega
  have hJ_diff_fin : (J \ I).Finite := (G.vertexSet_finite.subset hJE).sdiff
  have hJ_diff_sub : J \ I ⊆ G.vertexSet \ I := sdiff_subset_sdiff_left hJE
  have h_union_le : tangleRank 𝒯 θ (I ∪ (J \ I)) ≤ tangleRank 𝒯 θ I :=
    rank_union_le_of_forall_insert_le hr hIE hJ_diff_fin hJ_diff_sub hins
  have hJ_sub : J ⊆ I ∪ (J \ I) := by
    rw [union_sdiff_self]
    exact subset_union_right
  have hJ_le : tangleRank 𝒯 θ J ≤ tangleRank 𝒯 θ (I ∪ (J \ I)) :=
    hr.mono hJ_sub (union_subset hIE (sdiff_subset.trans hJE))
  omega

/-- The matroid on `V(G)` whose independent sets are the free sets with respect to a tangle `𝒯` of
order `θ` in `G` (Graph Minors X, Section 12, (12.2), page 189). -/
noncomputable def tangleMatroid (G : Hypergraph α β) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) : Matroid α :=
  (IndepMatroid.ofFinite G.vertexSet_finite (IsFreeSet G 𝒯 θ)
    (isFreeSet_empty G 𝒯 θ)
    (fun _ _ hJ hIJ ↦ hJ.subset h𝒯 hIJ)
    (fun _ _ hI hJ hlt ↦ hI.augment h𝒯 hJ hlt)
    (fun _ hI ↦ hI.1)).matroid

theorem tangleMatroid_E (G : Hypergraph α β) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    (tangleMatroid G h𝒯).E = G.vertexSet := by rfl

theorem tangleMatroid_indep_iff (G : Hypergraph α β) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) {I : Set α} :
    (tangleMatroid G h𝒯).Indep I ↔ IsFreeSet G 𝒯 θ I := by rfl

/-- The rank function of `tangleMatroid G h𝒯` on subsets of `V(G)` agrees with `tangleRank 𝒯 θ`
(Graph Minors X, Section 12, (12.2), page 189). -/
theorem tangleMatroid_eRk (G : Hypergraph α β) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {X : Set α} (hX : X ⊆ G.vertexSet) :
    (tangleMatroid G h𝒯).eRk X = tangleRank 𝒯 θ X := by
  have hr := theorem_12_1_proof G h𝒯
  obtain ⟨I, hI⟩ := (tangleMatroid G h𝒯).exists_isBasis X
  have hIX : I ⊆ X := hI.subset
  have hIE : I ⊆ G.vertexSet := hIX.trans hX
  have hI_free : IsFreeSet G 𝒯 θ I := hI.indep
  have hrI : tangleRank 𝒯 θ I = I.ncard := ((isFreeSet_iff_tangleRank_eq h𝒯).1 hI_free).2
  have hI_le_X : tangleRank 𝒯 θ I ≤ tangleRank 𝒯 θ X := hr.mono hIX hX
  have hins : ∀ e ∈ X \ I, tangleRank 𝒯 θ (insert e I) ≤ tangleRank 𝒯 θ I := by
    intro e he
    have hdep : (tangleMatroid G h𝒯).Dep (insert e I) := hI.insert_dep he
    have hnot_indep : ¬ IsFreeSet G 𝒯 θ (insert e I) := hdep.not_indep
    have heE : insert e I ⊆ G.vertexSet := insert_subset (hX he.1) hIE
    rw [isFreeSet_iff_tangleRank_eq h𝒯, not_and] at hnot_indep
    have hne : tangleRank 𝒯 θ (insert e I) ≠ (insert e I).ncard := hnot_indep heE
    have hle : tangleRank 𝒯 θ (insert e I) ≤ (insert e I).ncard := hr.le_ncard heE
    have hcard_ins : (insert e I).ncard = I.ncard + 1 :=
      ncard_insert_of_notMem he.2 (G.vertexSet_finite.subset hIE)
    omega
  have hX_le_I : tangleRank 𝒯 θ X ≤ tangleRank 𝒯 θ I := by
    have h := rank_union_le_of_forall_insert_le hr hIE
      ((G.vertexSet_finite.subset hX).sdiff) (sdiff_subset_sdiff_left hX) hins
    rwa [union_sdiff_cancel hIX] at h
  have hr_eq : tangleRank 𝒯 θ X = I.ncard := by omega
  rw [← hI.encard_eq_eRk, hr_eq, (G.vertexSet_finite.subset hIE).cast_ncard_eq]

/-- **Graph Minors X, (12.2)** (page 189):
"The free sets are the independent sets of a matroid on $V(G)$ with rank function $r$ as in
(12.1)." -/
theorem theorem_12_2_proof (G : Hypergraph α β) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    ∃ M : Matroid α, M.E = G.vertexSet ∧
      (∀ I : Set α, M.Indep I ↔ IsFreeSet G 𝒯 θ I) ∧
      (∀ X : Set α, X ⊆ G.vertexSet → M.eRk X = tangleRank 𝒯 θ X) :=
  ⟨tangleMatroid G h𝒯, tangleMatroid_E G h𝒯,
    fun _ ↦ tangleMatroid_indep_iff G h𝒯,
    fun _ hX ↦ tangleMatroid_eRk G h𝒯 hX⟩

end

end GraphMinor.GM10
