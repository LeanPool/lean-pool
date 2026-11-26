/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Cited
import LeanPool.GraphMinor.GM10.TangleLemmas
import Mathlib.Data.Set.Card

import LeanPool.GraphMinor.GM09.Bridge

/-!
# Graph Minors XV, Section 2: Tangles and Transactions

This file formalizes Section 2 ("Tangles and transactions", pages 116–119) of N. Robertson and
P. D. Seymour, *Graph Minors. XV. Giant steps*, J. Combin. Theory Ser. B 68 (1996) 112–148, over the
shared definitions in `GraphMinor.GM09.Defs`, `GraphMinor.GM10.Defs`, `GraphMinor.GM14.Defs`, and
`GraphMinor.GM15.Defs`:

- Equivalence lemmas between the wording of Graph Minors XV and the shared definitions of
  `GraphMinor.GM09.Defs` (`isCrookedTransaction_iff_exists_ends_in_intervals`,
  `isTransaction_of_fence_partition`, `isPVortex_of_bar_ncard_le_three`).
- `minimalComplementarySubgraph` ($\hat{X}$) and `boundaryVertices` ($N(X) = V(X \cap \hat{X})$):
  for any subgraph $X \le G$, the unique minimal subgraph $\hat{X} \le G$ such that $(X, \hat{X})$
  is a separation of $G$, with $N(X)$ consisting of all $v \in V(X)$ incident with an edge of $G$
  not in $E(X)$ (page 117).
- `IsSmallSubgraph` ($X \le G$ is small relative to $\mathcal{T}$ if $(X, \hat{X}) \in \mathcal{T}$,
  page 117).
- Intermediate numbered claims `(5)`–`(10)` of the proof of (2.1) (`lemma_2_1_claim_5`,
  `lemma_2_1_claim_6`, `lemma_2_1_claim_7`, `lemma_2_1_claim_8`, `lemma_2_1_claim_9`,
  `lemma_2_1_claim_10`, pages 117–119).
- `theorem_2_1` (**Graph Minors XV, (2.1)**, page 116): if $\mathcal{T}$ is a tangle in $G$ of
  order $\ge 5\rho + 2$ ($\rho \ge 1$) and $\mathcal{S}$ is a segregation of $G$ of type $(\rho,
  \kappa)$
  such that for every $(C, \Omega) \in \mathcal{S}$ there is no $(A, B) \in \mathcal{T}$ of order
  $\le 2\rho + 1$ with $B \subseteq C$, then $\mathcal{S}$ is $\mathcal{T}$-central.
-/

public section

namespace GraphMinor.GM15

open Set Function Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14

universe u v

variable {α : Type u} {β : Type v}

/-! ## Equivalence of Wording for Transactions and Crooked Transactions -/

private lemma graphWalk_start_mem_support {G : Graph α β} {u v : α} (W : GraphWalk G u v) :
    u ∈ W.support := by
  cases W <;> simp [GraphWalk.support]

private lemma graphWalk_end_mem_support {G : Graph α β} {u v : α} (W : GraphWalk G u v) :
    v ∈ W.support := by
  induction W with
  | nil _ => simp [GraphWalk.support]
  | cons _ _ ih => simp [GraphWalk.support, ih]

private lemma endpoints_mem_of_isGraphPathWithEnds {G P : Graph α β} {a b : α}
    (h : IsGraphPathWithEnds G P a b) : a ∈ V(P) ∧ b ∈ V(P) := by
  rcases h with ⟨_, W, _, hV, _⟩
  rw [hV]
  exact ⟨graphWalk_start_mem_support W, graphWalk_end_mem_support W⟩

private lemma isOmegaPathWithEnds_symm {S : Society α β} {P : Graph α β} {a b : α}
    (h : S.IsOmegaPathWithEnds P a b) :
    a ∈ V(P) ∧ b ∈ V(P) ∧ a ≠ b ∧ a ∈ S.Ω.bar ∧ b ∈ S.Ω.bar := by
  have hab := endpoints_mem_of_isGraphPathWithEnds h.1
  exact ⟨hab.1, hab.2, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Equivalence between the shared definition of a crooked transaction
(`GM09.Society.IsCrookedTransaction`,
having no peripheral member) and the interval wording of Graph Minors XIV (Section 8, page 40) and
Graph Minors XV: a transaction `P_set` in `S` is crooked if and only if for every `P ∈ P_set` and
every pair of ends `a, b` of `P`, both open intervals `S.Ω.interval a b` and `S.Ω.interval b a`
contain an end in `S.transactionEnds P_set`. -/
theorem isCrookedTransaction_iff_exists_ends_in_intervals (S : Society α β)
    (P_set : Set (Graph α β)) :
    S.IsCrookedTransaction P_set ↔
      S.IsTransaction P_set ∧
      ∀ P ∈ P_set, ∀ a b : α, S.IsOmegaPathWithEnds P a b →
        (∃ u' ∈ S.transactionEnds P_set, u' ∈ S.Ω.interval a b) ∧
        (∃ v' ∈ S.transactionEnds P_set, v' ∈ S.Ω.interval b a) := by
  constructor
  · rintro ⟨htrans, hno_periph⟩
    refine ⟨htrans, fun P hP a b hab => ?_⟩
    have hnot : ¬ (Disjoint (S.Ω.interval a b) (S.transactionEnds P_set) ∨
        Disjoint (S.Ω.interval b a) (S.transactionEnds P_set)) := by
      intro hdisj
      exact hno_periph P hP ⟨hP, a, b, hab, hdisj⟩
    rw [not_or, Set.not_disjoint_iff, Set.not_disjoint_iff] at hnot
    rcases hnot with ⟨⟨u', hu'1, hu'2⟩, ⟨v', hv'1, hv'2⟩⟩
    exact ⟨⟨u', hu'2, hu'1⟩, ⟨v', hv'2, hv'1⟩⟩
  · rintro ⟨htrans, hex⟩
    refine ⟨htrans, fun P hP ⟨_, a, b, hab, hdisj⟩ => ?_⟩
    rcases hex P hP a b hab with ⟨⟨u', hu'1, hu'2⟩, ⟨v', hv'1, hv'2⟩⟩
    rcases hdisj with h1 | h2
    · exact h1.le_bot ⟨hu'2, hu'1⟩
    · exact h2.le_bot ⟨hv'2, hv'1⟩

/-- If `(A, B)` is a fence of `S.Ω` and `P_set` is a set of mutually vertex-disjoint `Ω`-paths in
`S`
such that each `P ∈ P_set` has one end in `A` and one end in `B`, then `P_set` is a transaction in
`S`
(`GM09.Society.IsTransaction`). -/
theorem isTransaction_of_fence_partition (S : Society α β) (P_set : Set (Graph α β))
    (A B : Set α) (hdisj : S.IsDisjointOmegaPathSet P_set) (hfence : S.Ω.IsFence A B)
    (hends : ∀ P ∈ P_set, ∃ a ∈ A, ∃ b ∈ B, S.IsOmegaPathWithEnds P a b) :
    S.IsTransaction P_set :=
  ⟨A, B, hdisj, hfence, hends⟩

/-! ## Every society with $|\bar{\Omega}| \le 3$ is a $\rho$-vortex for $\rho \ge 1$ (page 116) -/

/-- Remark at the start of the proof of (2.1) (page 116):
"If $|\bar{\Omega}| \le 3$ then $(C, \Omega)$ has no transaction of cardinality $\ge 2$, and again
it is a $\rho$-vortex since $\rho \ge 1$." -/
theorem isPVortex_of_bar_ncard_le_three {S : Society α β} {p : ℕ}
    (hbar : S.Ω.bar.ncard ≤ 3) (hp : 1 ≤ p) :
    S.IsPVortex p := by
  intro P_set ⟨A, B, hdisj, hfence, hends⟩
  by_contra! hgt
  have h2 : 1 < P_set.ncard := by omega
  obtain ⟨P₁, hP₁⟩ := Set.nonempty_of_ncard_ne_zero (by omega : P_set.ncard ≠ 0)
  obtain ⟨P₂, hP₂, hne⟩ := Set.exists_ne_of_one_lt_ncard h2 P₁
  obtain ⟨a₁, ha₁, b₁, hb₁, hpath₁⟩ := hends P₁ hP₁
  obtain ⟨a₂, ha₂, b₂, hb₂, hpath₂⟩ := hends P₂ hP₂
  have hdisj₁₂ : Disjoint V(P₁) V(P₂) := hdisj.2 hP₁ hP₂ hne.symm
  obtain ⟨ha₁_V, hb₁_V, hab₁, ha₁_bar, hb₁_bar⟩ := isOmegaPathWithEnds_symm hpath₁
  obtain ⟨ha₂_V, hb₂_V, hab₂, ha₂_bar, hb₂_bar⟩ := isOmegaPathWithEnds_symm hpath₂
  have ha₁a₂ : a₁ ≠ a₂ := fun h => hdisj₁₂.le_bot ⟨ha₁_V, h ▸ ha₂_V⟩
  have ha₁b₂ : a₁ ≠ b₂ := fun h => hdisj₁₂.le_bot ⟨ha₁_V, h ▸ hb₂_V⟩
  have hb₁a₂ : b₁ ≠ a₂ := fun h => hdisj₁₂.le_bot ⟨hb₁_V, h ▸ ha₂_V⟩
  have hb₁b₂ : b₁ ≠ b₂ := fun h => hdisj₁₂.le_bot ⟨hb₁_V, h ▸ hb₂_V⟩
  have hsub : ({a₁, b₁, a₂, b₂} : Set α) ⊆ S.Ω.bar := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact ha₁_bar
    · exact hb₁_bar
    · exact ha₂_bar
    · exact hb₂_bar
  have hcard4 : ({a₁, b₁, a₂, b₂} : Set α).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hab₂]
    · simp [hb₁a₂, hb₁b₂]
    · simp [hab₁, ha₁a₂, ha₁b₂]
  have hle : ({a₁, b₁, a₂, b₂} : Set α).ncard ≤ S.Ω.bar.ncard :=
    Set.ncard_le_ncard hsub S.Ω.finite_bar
  omega

/-! ## Minimal complementary subgraph $\hat{X}$ and boundary $N(X)$ (page 117) -/

/-- For a subgraph $X \le G$, its boundary $N(X)$ is the set of all $v \in V(X)$ incident in $G$
with an edge of $G$ not in $E(X)$.
Graph Minors XV, Section 2 (page 117): "Thus, $N(X)$ is the set of all $v \in V(X)$ incident with
an edge of $G$ not in $E(X)$." -/
def boundaryVertices (G X : Hypergraph α β) : Set α :=
  {v ∈ X.vertexSet | ∃ e ∈ G.edgeSet \ X.edgeSet, G.Inc e v}

/-- For a subgraph $X \le G$, $\hat{X}$ is the unique minimal subgraph of $G$ such that
$(X, \hat{X})$ is a separation of $G$: its edge set is $E(G) \setminus E(X)$ and its vertex set is
$(V(G) \setminus V(X)) \cup N(X)$.
Graph Minors XV, Section 2 (page 117): "For any subgraph $X$ of $G$, let $\hat{X}$ be the unique
minimal subgraph so that $(X, \hat{X})$ is a separation of $G$, and let $N(X) = V(X \cap \hat{X})$."
-/
def minimalComplementarySubgraph (G X : Hypergraph α β) : Hypergraph α β where
  vertexSet := (G.vertexSet \ X.vertexSet) ∪ boundaryVertices G X
  edgeSet := G.edgeSet \ X.edgeSet
  Inc e v := e ∈ G.edgeSet \ X.edgeSet ∧ G.Inc e v
  vertex_mem_of_inc e v h := by
    by_cases hv : v ∈ X.vertexSet
    · exact Or.inr ⟨hv, e, h.1, h.2⟩
    · exact Or.inl ⟨G.vertex_mem_of_inc h.2, hv⟩
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := (G.vertexSet_finite.sdiff).union (X.vertexSet_finite.subset fun _ h => h.1)
  edgeSet_finite := G.edgeSet_finite.sdiff

/-- A subgraph $X \le G$ is *small* with respect to $\mathcal{T}$ if $(X, \hat{X}) \in \mathcal{T}$.
Graph Minors XV, Section 2 (page 117): "Let us say that $X \subseteq G$ is *small* if
$(X, \hat{X}) \in \mathscr{T}$." -/
def IsSmallSubgraph (G : Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (X : Hypergraph α β) : Prop :=
  (X, minimalComplementarySubgraph G X) ∈ 𝒯

private lemma minimalComplementarySubgraph_le (G X : Hypergraph α β) :
    minimalComplementarySubgraph G X ≤ G where
  vertexSet_subset := by
    rintro v (⟨hv, _⟩ | ⟨hv, e, he, hinc⟩)
    · exact hv
    · exact G.vertex_mem_of_inc hinc
  edgeSet_subset := sdiff_subset
  ends_eq e he := by
    ext v
    exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩

private lemma isSeparation_minimalComplementarySubgraph {G X : Hypergraph α β} (hX : X ≤ G) :
    G.IsSeparation X (minimalComplementarySubgraph G X) := by
  rw [isSeparation_iff_of_le hX (minimalComplementarySubgraph_le G X)]
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [mem_union, minimalComplementarySubgraph, mem_sdiff, boundaryVertices,
      Set.mem_ofPred_eq]
    constructor
    · rintro (hv | ⟨hv, _⟩ | ⟨hv, _⟩)
      · exact hX.vertexSet_subset hv
      · exact hv
      · exact hX.vertexSet_subset hv
    · intro hvG
      by_cases hvX : v ∈ X.vertexSet
      · exact Or.inl hvX
      · exact Or.inr (Or.inl ⟨hvG, hvX⟩)
  · exact union_sdiff_self.trans (Set.union_eq_right.mpr hX.edgeSet_subset)
  · exact inter_sdiff_self X.edgeSet G.edgeSet

private lemma inter_vertexSet_minimalComplementarySubgraph (G X : Hypergraph α β) :
    (X ∩ minimalComplementarySubgraph G X).vertexSet = boundaryVertices G X := by
  ext v
  simp only [inter_vertexSet, minimalComplementarySubgraph, mem_inter_iff, mem_union, mem_sdiff,
    boundaryVertices, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hvX, ⟨_, hvnot⟩ | ⟨_, h⟩⟩
    · exact (hvnot hvX).elim
    · exact ⟨hvX, h⟩
  · rintro ⟨hvX, h⟩
    exact ⟨hvX, Or.inr ⟨hvX, h⟩⟩

private lemma separationOrder_minimalComplementarySubgraph (G X : Hypergraph α β) :
    separationOrder X (minimalComplementarySubgraph G X) = (boundaryVertices G X).ncard :=
  congrArg Set.ncard (inter_vertexSet_minimalComplementarySubgraph G X)

private lemma boundaryVertices_bot (G : Hypergraph α β) :
    boundaryVertices G (⊥ : Hypergraph α β) = ∅ := by
  ext v
  simp [boundaryVertices]

private lemma minimalComplementarySubgraph_bot (G : Hypergraph α β) :
    minimalComplementarySubgraph G (⊥ : Hypergraph α β) = G := by
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq (minimalComplementarySubgraph_le G ⊥) le_rfl
  · simp [minimalComplementarySubgraph, boundaryVertices_bot]
  · simp [minimalComplementarySubgraph]

private lemma isSmallSubgraph_bot {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) (hθ : 1 ≤ θ) :
    IsSmallSubgraph G 𝒯 ⊥ := by
  rw [IsSmallSubgraph, minimalComplementarySubgraph_bot]
  have hsep : G.IsSeparation ⊥ G := by
    simpa [minimalComplementarySubgraph_bot] using
      isSeparation_minimalComplementarySubgraph (bot_le : (⊥ : Hypergraph α β) ≤ G)
  have hord : separationOrder (⊥ : Hypergraph α β) G < θ := by
    have : separationOrder (⊥ : Hypergraph α β) G = 0 := by simp [separationOrder]
    omega
  rcases h𝒯.axiom1 hsep hord with h | h
  · exact h
  · exact (h𝒯.axiom3 h rfl).elim

private lemma boundaryVertices_union_subset (G X Y : Hypergraph α β) :
    boundaryVertices G (X ∪ Y) ⊆ boundaryVertices G X ∪ boundaryVertices G Y := by
  rintro v ⟨hv, e, ⟨heG, heXY⟩, hinc⟩
  simp only [union_edgeSet, mem_union, not_or] at heXY
  rcases hv with hvX | hvY
  · exact Or.inl ⟨hvX, e, ⟨heG, heXY.1⟩, hinc⟩
  · exact Or.inr ⟨hvY, e, ⟨heG, heXY.2⟩, hinc⟩

/-! ## Claims (5)–(10) and Proof of (2.1) (pages 117–119) -/

/-- Indexed subgraphs $X_k$ ($0 \le k \le n + 1$) of $C$ for a linear decomposition of $(C,
\Omega)$,
where $X_0 = X_{n+1} = \bot$ and $X_{i+1} = X(i)$ for $i \in \operatorname{Fin} n$
(Graph Minors XV, Section 2, page 117). -/
private def decompPiece {n : ℕ} (X : Fin n → Hypergraph α β) (k : ℕ) : Hypergraph α β :=
  if h : 1 ≤ k ∧ k ≤ n then X ⟨k - 1, by omega⟩ else ⊥

/-- Prefix union $P_i = \bigcup_{1 \le j \le i} X_j$ for $0 \le i \le n$, with $P_0 = \bot$
(Graph Minors XV, Section 2, page 118). -/
private def prefixUnion {n : ℕ} (X : Fin n → Hypergraph α β) : ℕ → Hypergraph α β
  | 0 => ⊥
  | i + 1 => prefixUnion X i ∪ decompPiece X (i + 1)

private def suffixUnionAux {n : ℕ} (X : Fin n → Hypergraph α β) : ℕ → Hypergraph α β
  | 0 => ⊥
  | d + 1 => decompPiece X (n + 1 - (d + 1)) ∪ suffixUnionAux X d

/-- Suffix union $Q_k = \bigcup_{k \le j \le n} X_j$ for $1 \le k \le n + 1$, with $Q_{n+1} = \bot$
(Graph Minors XV, Section 2, page 118). -/
private def suffixUnion {n : ℕ} (X : Fin n → Hypergraph α β) (k : ℕ) : Hypergraph α β :=
  suffixUnionAux X (n + 1 - k)

private lemma suffixUnion_n_add_one {n : ℕ} (X : Fin n → Hypergraph α β) :
    suffixUnion X (n + 1) = ⊥ := by
  simp [suffixUnion, suffixUnionAux]

private lemma suffixUnion_eq_union {n : ℕ} (X : Fin n → Hypergraph α β) {k : ℕ} (hk : k ≤ n) :
    suffixUnion X k = decompPiece X k ∪ suffixUnion X (k + 1) := by
  unfold suffixUnion
  have h1 : n + 1 - k = (n - k) + 1 := by omega
  have h2 : n + 1 - (k + 1) = n - k := by omega
  have h3 : n + 1 - ((n - k) + 1) = k := by omega
  rw [h1, suffixUnionAux, h3, h2]

private lemma decompPiece_le {G : Hypergraph α β} {n : ℕ} {X : Fin n → Hypergraph α β}
    (hX : ∀ i, X i ≤ G) (k : ℕ) : decompPiece X k ≤ G := by
  unfold decompPiece
  split_ifs with h
  · exact hX _
  · exact bot_le

private lemma prefixUnion_le {G : Hypergraph α β} {n : ℕ} {X : Fin n → Hypergraph α β}
    (hX : ∀ i, X i ≤ G) (i : ℕ) : prefixUnion X i ≤ G := by
  induction i with
  | zero => exact bot_le
  | succ i ih => exact union_le ih (decompPiece_le hX (i + 1))

private lemma suffixUnionAux_le {G : Hypergraph α β} {n : ℕ} {X : Fin n → Hypergraph α β}
    (hX : ∀ i, X i ≤ G) (d : ℕ) : suffixUnionAux X d ≤ G := by
  induction d with
  | zero => exact bot_le
  | succ d ih => exact union_le (decompPiece_le hX _) ih

private lemma suffixUnion_le {G : Hypergraph α β} {n : ℕ} {X : Fin n → Hypergraph α β}
    (hX : ∀ i, X i ≤ G) (k : ℕ) : suffixUnion X k ≤ G :=
  suffixUnionAux_le hX _

private lemma mem_prefixUnion_vertexSet {n : ℕ} (X : Fin n → Hypergraph α β) (i : ℕ) (v : α) :
    v ∈ (prefixUnion X i).vertexSet ↔ ∃ j : Fin n, j.1 < i ∧ v ∈ (X j).vertexSet := by
  induction i with
  | zero => simp [prefixUnion]
  | succ i ih =>
    simp only [prefixUnion, union_vertexSet, mem_union, ih]
    constructor
    · rintro (⟨j, hj, hv⟩ | hv)
      · exact ⟨j, by omega, hv⟩
      · by_cases hi : i < n
        · have hcond : 1 ≤ i + 1 ∧ i + 1 ≤ n := ⟨by omega, by omega⟩
          simp only [decompPiece, hcond, and_self, ↓reduceDIte, Nat.add_sub_cancel] at hv
          exact ⟨⟨i, hi⟩, Nat.lt_succ_self i, hv⟩
        · have hbot : decompPiece X (i + 1) = ⊥ :=
            dite_eq_right_iff.mpr fun h => ((by omega : ¬ (1 ≤ i + 1 ∧ i + 1 ≤ n)) h).elim
          rw [hbot] at hv
          exact hv.elim
    · rintro ⟨j, hj, hv⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact Or.inl ⟨j, hlt, hv⟩
      · right
        have hcond : 1 ≤ i + 1 ∧ i + 1 ≤ n := ⟨by omega, by omega⟩
        simp only [decompPiece, hcond, and_self, ↓reduceDIte, Nat.add_sub_cancel]
        have hj_eq : (⟨i, by omega⟩ : Fin n) = j := Fin.ext heq.symm
        rwa [hj_eq]

private lemma mem_prefixUnion_edgeSet {n : ℕ} (X : Fin n → Hypergraph α β) (i : ℕ) (e : β) :
    e ∈ (prefixUnion X i).edgeSet ↔ ∃ j : Fin n, j.1 < i ∧ e ∈ (X j).edgeSet := by
  induction i with
  | zero => simp [prefixUnion]
  | succ i ih =>
    simp only [prefixUnion, union_edgeSet, mem_union, ih]
    constructor
    · rintro (⟨j, hj, he⟩ | he)
      · exact ⟨j, by omega, he⟩
      · by_cases hi : i < n
        · have hcond : 1 ≤ i + 1 ∧ i + 1 ≤ n := ⟨by omega, by omega⟩
          simp only [decompPiece, hcond, and_self, ↓reduceDIte, Nat.add_sub_cancel] at he
          exact ⟨⟨i, hi⟩, Nat.lt_succ_self i, he⟩
        · have hbot : decompPiece X (i + 1) = ⊥ :=
            dite_eq_right_iff.mpr fun h => ((by omega : ¬ (1 ≤ i + 1 ∧ i + 1 ≤ n)) h).elim
          rw [hbot] at he
          exact he.elim
    · rintro ⟨j, hj, he⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact Or.inl ⟨j, hlt, he⟩
      · right
        have hcond : 1 ≤ i + 1 ∧ i + 1 ≤ n := ⟨by omega, by omega⟩
        simp only [decompPiece, hcond, and_self, ↓reduceDIte, Nat.add_sub_cancel]
        have hj_eq : (⟨i, by omega⟩ : Fin n) = j := Fin.ext heq.symm
        rwa [hj_eq]

private lemma mem_suffixUnionAux_vertexSet {n : ℕ} (X : Fin n → Hypergraph α β) (d : ℕ)
    (hd : d ≤ n) (v : α) :
    v ∈ (suffixUnionAux X d).vertexSet ↔ ∃ j : Fin n, n - d ≤ j.1 ∧ v ∈ (X j).vertexSet := by
  induction d with
  | zero =>
    simp only [suffixUnionAux, bot_vertexSet, mem_empty_iff_false, Nat.sub_zero, false_iff,
      not_exists, not_and]
    intro j hj
    exact absurd hj (not_le_of_gt j.2)
  | succ d ih =>
    have hd_lt : d < n := Nat.lt_of_succ_le hd
    simp only [suffixUnionAux, union_vertexSet, mem_union, ih (le_of_lt hd_lt)]
    have hcond : 1 ≤ n + 1 - (d + 1) ∧ n + 1 - (d + 1) ≤ n := ⟨by omega, by omega⟩
    constructor
    · rintro (hv | ⟨j, hj, hv⟩)
      · simp only [decompPiece, hcond, and_self, ↓reduceDIte] at hv
        exact ⟨⟨n + 1 - (d + 1) - 1, by omega⟩, by dsimp; omega, hv⟩
      · exact ⟨j, by omega, hv⟩
    · rintro ⟨j, hj, hv⟩
      by_cases heq : j.1 = n - (d + 1)
      · left
        simp only [decompPiece, hcond, and_self, ↓reduceDIte]
        have hj_eq : (⟨n + 1 - (d + 1) - 1, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
        rwa [hj_eq]
      · right
        exact ⟨j, by omega, hv⟩

private lemma mem_suffixUnionAux_edgeSet {n : ℕ} (X : Fin n → Hypergraph α β) (d : ℕ)
    (hd : d ≤ n) (e : β) :
    e ∈ (suffixUnionAux X d).edgeSet ↔ ∃ j : Fin n, n - d ≤ j.1 ∧ e ∈ (X j).edgeSet := by
  induction d with
  | zero =>
    simp only [suffixUnionAux, bot_edgeSet, mem_empty_iff_false, Nat.sub_zero, false_iff,
      not_exists, not_and]
    intro j hj
    exact absurd hj (not_le_of_gt j.2)
  | succ d ih =>
    have hd_lt : d < n := Nat.lt_of_succ_le hd
    simp only [suffixUnionAux, union_edgeSet, mem_union, ih (le_of_lt hd_lt)]
    have hcond : 1 ≤ n + 1 - (d + 1) ∧ n + 1 - (d + 1) ≤ n := ⟨by omega, by omega⟩
    constructor
    · rintro (he | ⟨j, hj, he⟩)
      · simp only [decompPiece, hcond, and_self, ↓reduceDIte] at he
        exact ⟨⟨n + 1 - (d + 1) - 1, by omega⟩, by dsimp; omega, he⟩
      · exact ⟨j, by omega, he⟩
    · rintro ⟨j, hj, he⟩
      by_cases heq : j.1 = n - (d + 1)
      · left
        simp only [decompPiece, hcond, and_self, ↓reduceDIte]
        have hj_eq : (⟨n + 1 - (d + 1) - 1, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
        rwa [hj_eq]
      · right
        exact ⟨j, by omega, he⟩

private lemma mem_suffixUnion_vertexSet {n : ℕ} (X : Fin n → Hypergraph α β) {k : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n + 1) (v : α) :
    v ∈ (suffixUnion X k).vertexSet ↔ ∃ j : Fin n, k - 1 ≤ j.1 ∧ v ∈ (X j).vertexSet := by
  unfold suffixUnion
  rw [mem_suffixUnionAux_vertexSet X (n + 1 - k) (by omega)]
  have hsub : n - (n + 1 - k) = k - 1 := by omega
  rw [hsub]

private lemma mem_suffixUnion_edgeSet {n : ℕ} (X : Fin n → Hypergraph α β) {k : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n + 1) (e : β) :
    e ∈ (suffixUnion X k).edgeSet ↔ ∃ j : Fin n, k - 1 ≤ j.1 ∧ e ∈ (X j).edgeSet := by
  unfold suffixUnion
  rw [mem_suffixUnionAux_edgeSet X (n + 1 - k) (by omega)]
  have hsub : n - (n + 1 - k) = k - 1 := by omega
  rw [hsub]

/-- Claim (5) in the proof of Graph Minors XV, (2.1) (page 117):
"For $1 \le i \le n$, $N(X_i) \subseteq V(X_i \cap X_{i-1}) \cup V(X_i \cap X_{i+1}) \cup \{t_i\}$,
and consequently $|N(X_i)| \le 2\rho+1$." -/
private lemma lemma_2_1_claim_5 {G C : Hypergraph α β} {n p : ℕ}
    {t : Fin n → α} {X : Fin n → Hypergraph α β}
    (hC_le : C ≤ G)
    (hbd_C : boundaryVertices G C ⊆ range t)
    (hX_le : ∀ i, X i ≤ C)
    (hX_E : ∀ e ∈ C.edgeSet, ∃ i, e ∈ (X i).edgeSet)
    (hX_disj : ∀ i j : Fin n, i < j →
      Disjoint (X i).edgeSet (X j).edgeSet ∧ ((X i).vertexSet ∩ (X j).vertexSet).ncard ≤ p)
    (hX_betw : ∀ i j k : Fin n, i ≤ j → j ≤ k →
      (X i).vertexSet ∩ (X k).vertexSet ⊆ (X j).vertexSet)
    (hX_t : ∀ i : Fin n, t i ∈ (X i).vertexSet)
    (i : Fin n) :
    boundaryVertices G (X i) ⊆
      ((X i).vertexSet ∩ (decompPiece X i.1).vertexSet) ∪
      ((X i).vertexSet ∩ (decompPiece X (i.1 + 2)).vertexSet) ∪
      {t i} ∧
    (boundaryVertices G (X i)).ncard ≤ 2 * p + 1 := by
  have hsub : boundaryVertices G (X i) ⊆
      ((X i).vertexSet ∩ (decompPiece X i.1).vertexSet) ∪
      ((X i).vertexSet ∩ (decompPiece X (i.1 + 2)).vertexSet) ∪
      {t i} := by
    rintro v ⟨hvXi, e, ⟨heG, heXi⟩, hinc⟩
    by_cases hlt : ∃ j : Fin n, j < i ∧ v ∈ (X j).vertexSet
    · rcases hlt with ⟨j, hj, hvXj⟩
      left; left
      refine ⟨hvXi, ?_⟩
      have hi1 : 1 ≤ i.1 ∧ i.1 ≤ n := ⟨by omega, le_of_lt i.2⟩
      simp only [decompPiece, hi1, and_self, ↓reduceDIte]
      exact hX_betw j ⟨i.1 - 1, by omega⟩ i (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
        (Fin.le_iff_val_le_val.mpr (by dsimp; omega)) ⟨hvXj, hvXi⟩
    · by_cases hgt : ∃ j : Fin n, i < j ∧ v ∈ (X j).vertexSet
      · rcases hgt with ⟨j, hj, hvXj⟩
        left; right
        refine ⟨hvXi, ?_⟩
        have hi2 : 1 ≤ i.1 + 2 ∧ i.1 + 2 ≤ n := ⟨by omega, by omega⟩
        simp only [decompPiece, hi2, and_self, ↓reduceDIte]
        exact hX_betw i ⟨i.1 + 2 - 1, by omega⟩ j (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
          (Fin.le_iff_val_le_val.mpr (by dsimp; omega)) ⟨hvXi, hvXj⟩
      · right
        push Not at hlt hgt
        have he_not_C : e ∉ C.edgeSet := by
          intro heC
          obtain ⟨j, hj⟩ := hX_E e heC
          have hvXj : v ∈ (X j).vertexSet :=
            (X j).vertex_mem_of_inc ((inc_iff_of_le ((hX_le j).trans hC_le) hj).mpr hinc)
          rcases lt_trichotomy j i with h1 | rfl | h2
          · exact hlt j h1 hvXj
          · exact heXi hj
          · exact hgt j h2 hvXj
        have hv_bd : v ∈ boundaryVertices G C :=
          ⟨(hX_le i).vertexSet_subset hvXi, e, ⟨heG, he_not_C⟩, hinc⟩
        obtain ⟨j, hj_eq⟩ := hbd_C hv_bd
        have hvXj : v ∈ (X j).vertexSet := by
          rw [← hj_eq]
          exact hX_t j
        have hji : j = i := by
          rcases lt_trichotomy j i with h1 | h | h2
          · exact (hlt j h1 hvXj).elim
          · exact h
          · exact (hgt j h2 hvXj).elim
        subst hji
        exact mem_singleton_iff.mpr hj_eq.symm
  refine ⟨hsub, ?_⟩
  have h1 : ((X i).vertexSet ∩ (decompPiece X i.1).vertexSet).ncard ≤ p := by
    by_cases hi : 1 ≤ i.1 ∧ i.1 ≤ n
    · simp only [decompPiece, hi, and_self, ↓reduceDIte]
      rw [Set.inter_comm]
      exact (hX_disj ⟨i.1 - 1, by omega⟩ i (Fin.lt_def.mpr (by dsimp; omega))).2
    · have hbot : decompPiece X i.1 = ⊥ := dite_eq_right_iff.mpr fun h => (hi h).elim
      rw [hbot]
      simp
  have h2 : ((X i).vertexSet ∩ (decompPiece X (i.1 + 2)).vertexSet).ncard ≤ p := by
    by_cases hi : 1 ≤ i.1 + 2 ∧ i.1 + 2 ≤ n
    · simp only [decompPiece, hi, and_self, ↓reduceDIte]
      exact (hX_disj i ⟨i.1 + 2 - 1, by omega⟩ (Fin.lt_def.mpr (by dsimp; omega))).2
    · have hbot : decompPiece X (i.1 + 2) = ⊥ := dite_eq_right_iff.mpr fun h => (hi h).elim
      rw [hbot]
      simp
  have hfin1 : ((X i).vertexSet ∩ (decompPiece X i.1).vertexSet).Finite :=
    (X i).vertexSet_finite.inter_of_left _
  have hfin2 : ((X i).vertexSet ∩ (decompPiece X (i.1 + 2)).vertexSet).Finite :=
    (X i).vertexSet_finite.inter_of_left _
  have hfin_union := (hfin1.union hfin2).union (Set.finite_singleton (t i))
  have hle1 := Set.ncard_le_ncard hsub hfin_union
  have hle2 := Set.ncard_union_le
    (((X i).vertexSet ∩ (decompPiece X i.1).vertexSet) ∪
      ((X i).vertexSet ∩ (decompPiece X (i.1 + 2)).vertexSet)) {t i}
  have hle3 := Set.ncard_union_le
    ((X i).vertexSet ∩ (decompPiece X i.1).vertexSet)
    ((X i).vertexSet ∩ (decompPiece X (i.1 + 2)).vertexSet)
  rw [Set.ncard_singleton] at hle2
  omega

/-- Claim (6) in the proof of Graph Minors XV, (2.1) (page 117):
"$X_1, \dots, X_n$ are small." -/
private lemma lemma_2_1_claim_6 {G C : Hypergraph α β} {θ p : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    (hθ : 2 * p + 2 ≤ θ)
    (hno_small : ∀ A B : Hypergraph α β, (A, B) ∈ 𝒯 → separationOrder A B ≤ 2 * p + 1 →
      ¬ (B ≤ C))
    {X : Hypergraph α β} (hX_le : X ≤ C) (hX_G : X ≤ G)
    (hbd : (boundaryVertices G X).ncard ≤ 2 * p + 1) :
    IsSmallSubgraph G 𝒯 X := by
  have hsep := isSeparation_minimalComplementarySubgraph hX_G
  have hord : separationOrder X (minimalComplementarySubgraph G X) ≤ 2 * p + 1 := by
    rw [separationOrder_minimalComplementarySubgraph]
    exact hbd
  rcases h𝒯.axiom1 hsep (by omega) with h | h
  · exact h
  · exfalso
    rw [separationOrder_comm] at hord
    exact hno_small (minimalComplementarySubgraph G X) X h hord hX_le

/-- Claim (7) in the proof of Graph Minors XV, (2.1) (page 117):
"If $Z \subseteq X \cup Y \subseteq G$ and $X, Y$ are small and $|N(Z)| < ord(\mathscr{T})$,
then $Z$ is small." -/
private lemma lemma_2_1_claim_7 {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {X Y Z : Hypergraph α β} (hX : X ≤ G) (hY : Y ≤ G) (hZ : Z ≤ G)
    (hZ_sub : Z ≤ X ∪ Y) (hX_small : IsSmallSubgraph G 𝒯 X) (hY_small : IsSmallSubgraph G 𝒯 Y)
    (hbd : (boundaryVertices G Z).ncard < θ) :
    IsSmallSubgraph G 𝒯 Z := by
  have hsep := isSeparation_minimalComplementarySubgraph hZ
  have hord : separationOrder Z (minimalComplementarySubgraph G Z) < θ := by
    rwa [separationOrder_minimalComplementarySubgraph]
  rcases h𝒯.axiom1 hsep hord with h | h
  · exact h
  · exfalso
    have hunion : X ∪ Y ∪ minimalComplementarySubgraph G Z = G := by
      apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq
        (union_le (union_le hX hY) (minimalComplementarySubgraph_le G Z)) le_rfl
      · ext v
        simp only [union_vertexSet, mem_union]
        constructor
        · rintro ((hvX | hvY) | hvZ)
          · exact hX.vertexSet_subset hvX
          · exact hY.vertexSet_subset hvY
          · exact (minimalComplementarySubgraph_le G Z).vertexSet_subset hvZ
        · intro hvG
          have hv_sep : v ∈ Z.vertexSet ∪ (minimalComplementarySubgraph G Z).vertexSet := by
            rw [hsep.vertexSet_union]
            exact hvG
          rcases hv_sep with hvZ | hvZ'
          · exact Or.inl (hZ_sub.vertexSet_subset hvZ)
          · exact Or.inr hvZ'
      · ext e
        simp only [union_edgeSet, mem_union]
        constructor
        · rintro ((heX | heY) | heZ)
          · exact hX.edgeSet_subset heX
          · exact hY.edgeSet_subset heY
          · exact (minimalComplementarySubgraph_le G Z).edgeSet_subset heZ
        · intro heG
          have he_sep : e ∈ Z.edgeSet ∪ (minimalComplementarySubgraph G Z).edgeSet := by
            rw [hsep.edgeSet_union]
            exact heG
          rcases he_sep with heZ | heZ'
          · exact Or.inl (hZ_sub.edgeSet_subset heZ)
          · exact Or.inr heZ'
    exact h𝒯.axiom2 hX_small hY_small h hunion

private lemma bot_inter (B : Hypergraph α β) : (⊥ : Hypergraph α β) ∩ B = ⊥ := by
  ext <;> exact ⟨And.left, False.elim⟩

private lemma boundaryVertices_prefixUnion_inter_subset {G C A B : Hypergraph α β} {n : ℕ}
    {X : Fin n → Hypergraph α β}
    (hsep_AB : G.IsSeparation A B) (hB_le_C : B ≤ C) (hC_le : C ≤ G)
    (hX_le : ∀ j, X j ≤ C)
    (hX_E : ∀ e ∈ C.edgeSet, ∃ j, e ∈ (X j).edgeSet)
    (hX_betw : ∀ a b c : Fin n, a ≤ b → b ≤ c →
      (X a).vertexSet ∩ (X c).vertexSet ⊆ (X b).vertexSet)
    (i : ℕ) (hi : i ≤ n) :
    boundaryVertices G (prefixUnion X i ∩ B) ⊆
      ((prefixUnion X i).vertexSet ∩ (A ∩ B).vertexSet) ∪
      ((decompPiece X i).vertexSet ∩ (decompPiece X (i + 1)).vertexSet) := by
  rintro v ⟨⟨hvPi, hvB⟩, e, ⟨heG, hePiB⟩, hinc⟩
  simp only [inter_edgeSet, mem_inter_iff, not_and] at hePiB
  by_cases heB : e ∈ B.edgeSet
  · right
    have he_not_Pi : e ∉ (prefixUnion X i).edgeSet := fun h => hePiB h heB
    have heC : e ∈ C.edgeSet := hB_le_C.edgeSet_subset heB
    obtain ⟨j, hjE⟩ := hX_E e heC
    have hij : i ≤ j.1 := by
      by_contra! hlt
      exact he_not_Pi ((mem_prefixUnion_edgeSet X i e).mpr ⟨j, hlt, hjE⟩)
    obtain ⟨j₀, hj₀_lt, hvXj₀⟩ := (mem_prefixUnion_vertexSet X i v).mp hvPi
    have hvXj : v ∈ (X j).vertexSet :=
      (X j).vertex_mem_of_inc ((inc_iff_of_le ((hX_le j).trans hC_le) hjE).mpr hinc)
    have hi1 : 1 ≤ i ∧ i ≤ n := ⟨by omega, hi⟩
    have hi2 : 1 ≤ i + 1 ∧ i + 1 ≤ n := ⟨by omega, by omega⟩
    simp only [decompPiece, hi1, hi2, and_self, ↓reduceDIte, Nat.add_sub_cancel]
    refine ⟨?_, ?_⟩
    · exact hX_betw j₀ ⟨i - 1, by omega⟩ j
        (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
        (Fin.le_iff_val_le_val.mpr (by dsimp; omega)) ⟨hvXj₀, hvXj⟩
    · exact hX_betw j₀ ⟨i, by omega⟩ j
        (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
        (Fin.le_iff_val_le_val.mpr (by dsimp; omega)) ⟨hvXj₀, hvXj⟩
  · left
    have heA : e ∈ A.edgeSet := by
      have he_union : e ∈ A.edgeSet ∪ B.edgeSet := by
        rw [hsep_AB.edgeSet_union]
        exact heG
      exact he_union.resolve_right heB
    have hvA : v ∈ A.vertexSet :=
      A.vertex_mem_of_inc ((inc_iff_of_le hsep_AB.left_le heA).mpr hinc)
    exact ⟨hvPi, hvA, hvB⟩

/-- Claim (8) in the proof of Graph Minors XV, (2.1) (page 118):
"For $0 \le i \le n$, if $|V(P_i) \cap R| < ord(\mathscr{T}) - \rho$ then $P_i \cap B$ is small." -/
private lemma lemma_2_1_claim_8 {G C A B : Hypergraph α β} {n θ p : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {X : Fin n → Hypergraph α β}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 1 ≤ θ)
    (hsep_AB : G.IsSeparation A B) (hB_le_C : B ≤ C) (hC_le : C ≤ G)
    (hX_le : ∀ j, X j ≤ C)
    (hX_E : ∀ e ∈ C.edgeSet, ∃ j, e ∈ (X j).edgeSet)
    (hX_disj : ∀ a b : Fin n, a < b →
      Disjoint (X a).edgeSet (X b).edgeSet ∧ ((X a).vertexSet ∩ (X b).vertexSet).ncard ≤ p)
    (hX_betw : ∀ a b c : Fin n, a ≤ b → b ≤ c →
      (X a).vertexSet ∩ (X c).vertexSet ⊆ (X b).vertexSet)
    (hX_small : ∀ j : Fin n, IsSmallSubgraph G 𝒯 (X j))
    (i : ℕ) (hi : i ≤ n)
    (hcard : ((prefixUnion X i).vertexSet ∩ (A ∩ B).vertexSet).ncard + p < θ) :
    IsSmallSubgraph G 𝒯 (prefixUnion X i ∩ B) := by
  induction i with
  | zero =>
    rw [prefixUnion, bot_inter]
    exact isSmallSubgraph_bot h𝒯 hθ
  | succ i ih =>
    have hi_le : i ≤ n := le_of_lt hi
    have hsub_R : (prefixUnion X i).vertexSet ∩ (A ∩ B).vertexSet ⊆
        (prefixUnion X (i + 1)).vertexSet ∩ (A ∩ B).vertexSet := by
      intro v ⟨hv1, hv2⟩
      exact ⟨Or.inl hv1, hv2⟩
    have hfin_R : ((prefixUnion X (i + 1)).vertexSet ∩ (A ∩ B).vertexSet).Finite :=
      (prefixUnion X (i + 1)).vertexSet_finite.inter_of_left _
    have hcard_prev : ((prefixUnion X i).vertexSet ∩ (A ∩ B).vertexSet).ncard + p < θ := by
      have hle := Set.ncard_le_ncard hsub_R hfin_R
      omega
    have hsmall_prev : IsSmallSubgraph G 𝒯 (prefixUnion X i ∩ B) := ih hi_le hcard_prev
    have hsmall_Xi : IsSmallSubgraph G 𝒯 (decompPiece X (i + 1)) := by
      have hcond : 1 ≤ i + 1 ∧ i + 1 ≤ n := ⟨by omega, hi⟩
      simp only [decompPiece, hcond, and_self, ↓reduceDIte]
      exact hX_small _
    have hZ_sub : prefixUnion X (i + 1) ∩ B ≤ (prefixUnion X i ∩ B) ∪ decompPiece X (i + 1) := by
      refine ⟨?_, ?_, ?_⟩
      · rintro v ⟨hv1 | hv2, hvB⟩
        · exact Or.inl ⟨hv1, hvB⟩
        · exact Or.inr hv2
      · rintro e ⟨he1 | he2, heB⟩
        · exact Or.inl ⟨he1, heB⟩
        · exact Or.inr he2
      · intro e he
        have hle1 : prefixUnion X (i + 1) ∩ B ≤ G :=
          inter_le (prefixUnion_le (fun j => (hX_le j).trans hC_le) (i + 1)) hsep_AB.right_le
        have hle2 : (prefixUnion X i ∩ B) ∪ decompPiece X (i + 1) ≤ G :=
          union_le (inter_le (prefixUnion_le (fun j => (hX_le j).trans hC_le) i) hsep_AB.right_le)
            (decompPiece_le (fun j => (hX_le j).trans hC_le) (i + 1))
        have he_union : e ∈ ((prefixUnion X i ∩ B) ∪ decompPiece X (i + 1)).edgeSet := by
          rcases he with ⟨he1 | he2, heB⟩
          · exact Or.inl ⟨he1, heB⟩
          · exact Or.inr he2
        exact (hle2.ends_eq e he_union).symm.trans (hle1.ends_eq e he)
    have hbd_sub := boundaryVertices_prefixUnion_inter_subset hsep_AB hB_le_C hC_le hX_le hX_E
      hX_betw (i + 1) hi
    have hcap_le : ((decompPiece X (i + 1)).vertexSet ∩ (decompPiece X
      (i + 1 + 1)).vertexSet).ncard ≤ p := by
      by_cases hi2 : 1 ≤ i + 1 + 1 ∧ i + 1 + 1 ≤ n
      · have hi1 : 1 ≤ i + 1 ∧ i + 1 ≤ n := ⟨by omega, hi⟩
        simp only [decompPiece, hi1, hi2, and_self, ↓reduceDIte]
        exact (hX_disj ⟨i + 1 - 1, by omega⟩ ⟨i + 1 + 1 - 1, by omega⟩
          (Fin.lt_def.mpr (by dsimp; omega))).2
      · have hbot : decompPiece X (i + 1 + 1) = ⊥ :=
          dite_eq_right_iff.mpr fun h => (hi2 h).elim
        rw [hbot]
        simp
    have hbd_lt : (boundaryVertices G (prefixUnion X (i + 1) ∩ B)).ncard < θ := by
      have hfin2 : ((decompPiece X (i + 1)).vertexSet ∩ (decompPiece X
        (i + 1 + 1)).vertexSet).Finite :=
        (decompPiece X (i + 1)).vertexSet_finite.inter_of_left _
      have hle1 := Set.ncard_le_ncard hbd_sub (hfin_R.union hfin2)
      have hle2 := Set.ncard_union_le
        ((prefixUnion X (i + 1)).vertexSet ∩ (A ∩ B).vertexSet)
        ((decompPiece X (i + 1)).vertexSet ∩ (decompPiece X (i + 1 + 1)).vertexSet)
      omega
    exact lemma_2_1_claim_7 h𝒯
      (inter_le (prefixUnion_le (fun j => (hX_le j).trans hC_le) i) hsep_AB.right_le)
      (decompPiece_le (fun j => (hX_le j).trans hC_le) (i + 1))
      (inter_le (prefixUnion_le (fun j => (hX_le j).trans hC_le) (i + 1)) hsep_AB.right_le)
      hZ_sub hsmall_prev hsmall_Xi hbd_lt

private lemma boundaryVertices_suffixUnion_inter_subset {G C A B : Hypergraph α β} {n : ℕ}
    {X : Fin n → Hypergraph α β}
    (hsep_AB : G.IsSeparation A B) (hB_le_C : B ≤ C) (hC_le : C ≤ G)
    (hX_le : ∀ j, X j ≤ C)
    (hX_E : ∀ e ∈ C.edgeSet, ∃ j, e ∈ (X j).edgeSet)
    (hX_betw : ∀ a b c : Fin n, a ≤ b → b ≤ c →
      (X a).vertexSet ∩ (X c).vertexSet ⊆ (X b).vertexSet)
    (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    boundaryVertices G (suffixUnion X k ∩ B) ⊆
      ((suffixUnion X k).vertexSet ∩ (A ∩ B).vertexSet) ∪
      ((decompPiece X (k - 1)).vertexSet ∩ (decompPiece X k).vertexSet) := by
  rintro v ⟨⟨hvQk, hvB⟩, e, ⟨heG, heQkB⟩, hinc⟩
  simp only [inter_edgeSet, mem_inter_iff, not_and] at heQkB
  by_cases heB : e ∈ B.edgeSet
  · right
    have he_not_Qk : e ∉ (suffixUnion X k).edgeSet := fun h => heQkB h heB
    have heC : e ∈ C.edgeSet := hB_le_C.edgeSet_subset heB
    obtain ⟨j, hjE⟩ := hX_E e heC
    have hjk : j.1 < k - 1 := by
      by_contra! hge
      exact he_not_Qk ((mem_suffixUnion_edgeSet X hk1 (by omega) e).mpr ⟨j, hge, hjE⟩)
    obtain ⟨j₀, hj₀_ge, hvXj₀⟩ := (mem_suffixUnion_vertexSet X hk1 (by omega) v).mp hvQk
    have hvXj : v ∈ (X j).vertexSet :=
      (X j).vertex_mem_of_inc ((inc_iff_of_le ((hX_le j).trans hC_le) hjE).mpr hinc)
    have hk_prev : 1 ≤ k - 1 ∧ k - 1 ≤ n := ⟨by omega, by omega⟩
    have hk_curr : 1 ≤ k ∧ k ≤ n := ⟨hk1, hkn⟩
    simp only [decompPiece, hk_prev, hk_curr, and_self, ↓reduceDIte]
    refine ⟨?_, ?_⟩
    · exact hX_betw j ⟨k - 1 - 1, by omega⟩ j₀
        (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
        (Fin.le_iff_val_le_val.mpr (by dsimp; omega)) ⟨hvXj, hvXj₀⟩
    · exact hX_betw j ⟨k - 1, by omega⟩ j₀
        (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
        (Fin.le_iff_val_le_val.mpr (by dsimp; omega)) ⟨hvXj, hvXj₀⟩
  · left
    have heA : e ∈ A.edgeSet := by
      have he_union : e ∈ A.edgeSet ∪ B.edgeSet := by
        rw [hsep_AB.edgeSet_union]
        exact heG
      exact he_union.resolve_right heB
    have hvA : v ∈ A.vertexSet :=
      A.vertex_mem_of_inc ((inc_iff_of_le hsep_AB.left_le heA).mpr hinc)
    exact ⟨hvQk, hvA, hvB⟩

private lemma suffixUnion_inter_isSmall {G C A B : Hypergraph α β} {n θ p : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {X : Fin n → Hypergraph α β}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 1 ≤ θ)
    (hsep_AB : G.IsSeparation A B) (hB_le_C : B ≤ C) (hC_le : C ≤ G)
    (hX_le : ∀ j, X j ≤ C)
    (hX_E : ∀ e ∈ C.edgeSet, ∃ j, e ∈ (X j).edgeSet)
    (hX_disj : ∀ a b : Fin n, a < b →
      Disjoint (X a).edgeSet (X b).edgeSet ∧ ((X a).vertexSet ∩ (X b).vertexSet).ncard ≤ p)
    (hX_betw : ∀ a b c : Fin n, a ≤ b → b ≤ c →
      (X a).vertexSet ∩ (X c).vertexSet ⊆ (X b).vertexSet)
    (hX_small : ∀ j : Fin n, IsSmallSubgraph G 𝒯 (X j))
    (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n + 1)
    (hcard : ((suffixUnion X k).vertexSet ∩ (A ∩ B).vertexSet).ncard + p < θ) :
    IsSmallSubgraph G 𝒯 (suffixUnion X k ∩ B) := by
  obtain ⟨d, hd⟩ : ∃ d, d = n + 1 - k := ⟨n + 1 - k, rfl⟩
  have hk_eq : k = n + 1 - d := by omega
  have hd_le : d ≤ n := by omega
  subst hk_eq
  induction d with
  | zero =>
    rw [Nat.sub_zero, suffixUnion_n_add_one, bot_inter]
    exact isSmallSubgraph_bot h𝒯 hθ
  | succ d ih =>
    have hd_lt : d < n := Nat.lt_of_succ_le hd_le
    let k := n + 1 - (d + 1)
    have hk_succ : n + 1 - d = k + 1 := by omega
    have hk_le_n : k ≤ n := by omega
    have hk_ge_1 : 1 ≤ k := by omega
    rw [ suffixUnion_eq_union X hk_le_n ] at hcard
    have hsub_R : (suffixUnion X (k + 1)).vertexSet ∩ (A ∩ B).vertexSet ⊆
        (suffixUnion X k).vertexSet ∩ (A ∩ B).vertexSet := by
      rw [suffixUnion_eq_union X hk_le_n]
      intro v ⟨hv1, hv2⟩
      exact ⟨Or.inr hv1, hv2⟩
    have hfin_R : ((suffixUnion X k).vertexSet ∩ (A ∩ B).vertexSet).Finite :=
      (suffixUnion X k).vertexSet_finite.inter_of_left _
    have hcard_next : ((suffixUnion X (k + 1)).vertexSet ∩ (A ∩ B).vertexSet).ncard + p < θ := by
      have hle := Set.ncard_le_ncard hsub_R hfin_R
      rw [suffixUnion_eq_union X hk_le_n] at hle
      omega
    have hsmall_next : IsSmallSubgraph G 𝒯 (suffixUnion X (k + 1) ∩ B) := by
      rw [← hk_succ] at hcard_next ⊢
      exact ih (le_of_lt hd_lt) (by omega) (by omega) hcard_next (by omega)
    have hsmall_Xk : IsSmallSubgraph G 𝒯 (decompPiece X k) := by
      have hcond : 1 ≤ k ∧ k ≤ n := ⟨hk_ge_1, hk_le_n⟩
      simp only [decompPiece, hcond, and_self, ↓reduceDIte]
      exact hX_small _
    have hZ_sub : suffixUnion X k ∩ B ≤ decompPiece X k ∪ (suffixUnion X (k + 1) ∩ B) := by
      have heq_u := suffixUnion_eq_union X hk_le_n
      refine ⟨?_, ?_, ?_⟩
      · intro v hv
        rw [heq_u] at hv
        rcases hv with ⟨hv1 | hv2, hvB⟩
        · exact Or.inl hv1
        · exact Or.inr ⟨hv2, hvB⟩
      · intro e he
        rw [heq_u] at he
        rcases he with ⟨he1 | he2, heB⟩
        · exact Or.inl he1
        · exact Or.inr ⟨he2, heB⟩
      · intro e he
        have hle1 : suffixUnion X k ∩ B ≤ G :=
          inter_le (suffixUnion_le (fun j => (hX_le j).trans hC_le) k) hsep_AB.right_le
        have hle2 : decompPiece X k ∪ (suffixUnion X (k + 1) ∩ B) ≤ G :=
          union_le (decompPiece_le (fun j => (hX_le j).trans hC_le) k)
            (inter_le (suffixUnion_le (fun j => (hX_le j).trans hC_le) (k + 1)) hsep_AB.right_le)
        have he_union : e ∈ (decompPiece X k ∪ (suffixUnion X (k + 1) ∩ B)).edgeSet := by
          rw [heq_u] at he
          rcases he with ⟨he1 | he2, heB⟩
          · exact Or.inl he1
          · exact Or.inr ⟨he2, heB⟩
        exact (hle2.ends_eq e he_union).symm.trans (hle1.ends_eq e he)
    have hbd_sub := boundaryVertices_suffixUnion_inter_subset hsep_AB hB_le_C hC_le hX_le hX_E
      hX_betw k hk_ge_1 hk_le_n
    have hcap_le : ((decompPiece X (k - 1)).vertexSet ∩ (decompPiece X k).vertexSet).ncard ≤ p := by
      by_cases hk2 : 1 ≤ k - 1 ∧ k - 1 ≤ n
      · have hk_c : 1 ≤ k ∧ k ≤ n := ⟨hk_ge_1, hk_le_n⟩
        simp only [decompPiece, hk2, hk_c, and_self, ↓reduceDIte]
        exact (hX_disj ⟨k - 1 - 1, by omega⟩ ⟨k - 1, by omega⟩
          (Fin.lt_def.mpr (by dsimp; omega))).2
      · have hbot : decompPiece X (k - 1) = ⊥ :=
          dite_eq_right_iff.mpr fun h => (hk2 h).elim
        rw [hbot]
        simp
    have hbd_lt : (boundaryVertices G (suffixUnion X k ∩ B)).ncard < θ := by
      have hfin2 : ((decompPiece X (k - 1)).vertexSet ∩ (decompPiece X k).vertexSet).Finite :=
        (decompPiece X (k - 1)).vertexSet_finite.inter_of_left _
      have hle1 := Set.ncard_le_ncard hbd_sub (hfin_R.union hfin2)
      have hle2 := Set.ncard_union_le
        ((suffixUnion X k).vertexSet ∩ (A ∩ B).vertexSet)
        ((decompPiece X (k - 1)).vertexSet ∩ (decompPiece X k).vertexSet)
      rw [← suffixUnion_eq_union X hk_le_n] at hcard
      omega
    exact lemma_2_1_claim_7 h𝒯
      (decompPiece_le (fun j => (hX_le j).trans hC_le) k)
      (inter_le (suffixUnion_le (fun j => (hX_le j).trans hC_le) (k + 1)) hsep_AB.right_le)
      (inter_le (suffixUnion_le (fun j => (hX_le j).trans hC_le) k) hsep_AB.right_le)
      hZ_sub hsmall_Xk hsmall_next hbd_lt

private lemma not_isSmallSubgraph_of_mem_tangle {G A B : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (hAB : (A, B) ∈ 𝒯) :
    ¬ IsSmallSubgraph G 𝒯 B := by
  intro hsmall
  have hsep_AB := h𝒯.isSeparation hAB
  have hunion : A ∪ B ∪ B = G := by
    rw [GM10.union_assoc, GM10.union_self, hsep_AB.union_eq]
  exact h𝒯.axiom2 hAB hsmall hsmall hunion

/-- Claim (9) in the proof of Graph Minors XV, (2.1) (page 118):
"$j < n$, and $(P_j \cap B) \cup X_{j+1}$ is small, and $|P_{j+1} \cap R| \ge ord(\mathscr{T}) -
2\rho - 1$." -/
private lemma lemma_2_1_claim_9 {G C A B : Hypergraph α β} {n θ p : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {t : Fin n → α} {X : Fin n → Hypergraph α β}
    (h𝒯 : IsTangle G θ 𝒯) (hp : 1 ≤ p) (hθ : 5 * p + 2 ≤ θ)
    (hAB : (A, B) ∈ 𝒯) (hB_le_C : B ≤ C) (hC_le : C ≤ G)
    (hbd_C : boundaryVertices G C ⊆ range t)
    (hX_le : ∀ j, X j ≤ C)
    (hX_V : ∀ v ∈ C.vertexSet, ∃ j, v ∈ (X j).vertexSet)
    (hX_E : ∀ e ∈ C.edgeSet, ∃ j, e ∈ (X j).edgeSet)
    (hX_disj : ∀ a b : Fin n, a < b →
      Disjoint (X a).edgeSet (X b).edgeSet ∧ ((X a).vertexSet ∩ (X b).vertexSet).ncard ≤ p)
    (hX_betw : ∀ a b c : Fin n, a ≤ b → b ≤ c →
      (X a).vertexSet ∩ (X c).vertexSet ⊆ (X b).vertexSet)
    (hX_t : ∀ j : Fin n, t j ∈ (X j).vertexSet)
    (hX_small : ∀ j : Fin n, IsSmallSubgraph G 𝒯 (X j))
    (j : ℕ) (hj_le : j ≤ n)
    (hj_lt_bound : ((prefixUnion X j).vertexSet ∩ (A ∩ B).vertexSet).ncard + 2 * p + 1 < θ)
    (hj_max : ∀ m : ℕ, m ≤ n →
      ((prefixUnion X m).vertexSet ∩ (A ∩ B).vertexSet).ncard + 2 * p + 1 < θ → m ≤ j) :
    j < n ∧
    IsSmallSubgraph G 𝒯 ((prefixUnion X j ∩ B) ∪ decompPiece X (j + 1)) ∧
    θ ≤ ((prefixUnion X (j + 1)).vertexSet ∩ (A ∩ B).vertexSet).ncard + 2 * p + 1 := by
  have hsep_AB := h𝒯.isSeparation hAB
  have hsmall_PjB : IsSmallSubgraph G 𝒯 (prefixUnion X j ∩ B) :=
    lemma_2_1_claim_8 h𝒯 (by omega) hsep_AB hB_le_C hC_le hX_le hX_E hX_disj hX_betw hX_small
      j hj_le (by omega)
  have hj_lt_n : j < n := by
    by_contra! hge
    have hjeq : j = n := le_antisymm hj_le hge
    subst hjeq
    have hPn_B : prefixUnion X j ∩ B = B := by
      apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq
        (inter_le_right (prefixUnion_le (fun i => (hX_le i).trans hC_le) j) hsep_AB.right_le) le_rfl
      · ext v
        simp only [inter_vertexSet, mem_inter_iff]
        refine ⟨fun h => h.2, fun hvB => ⟨?_, hvB⟩⟩
        obtain ⟨i, hi⟩ := hX_V v (hB_le_C.vertexSet_subset hvB)
        exact (mem_prefixUnion_vertexSet X j v).mpr ⟨i, i.2, hi⟩
      · ext e
        simp only [inter_edgeSet, mem_inter_iff]
        refine ⟨fun h => h.2, fun heB => ⟨?_, heB⟩⟩
        obtain ⟨i, hi⟩ := hX_E e (hB_le_C.edgeSet_subset heB)
        exact (mem_prefixUnion_edgeSet X j e).mpr ⟨i, i.2, hi⟩
    rw [hPn_B] at hsmall_PjB
    exact not_isSmallSubgraph_of_mem_tangle h𝒯 hAB hsmall_PjB
  have hge_next : θ ≤ ((prefixUnion X (j + 1)).vertexSet ∩ (A ∩ B).vertexSet).ncard + 2 * p + 1
    := by
    by_contra! hlt
    have hle := hj_max (j + 1) hj_lt_n hlt
    omega
  have hbd_PjB_sub := boundaryVertices_prefixUnion_inter_subset hsep_AB hB_le_C hC_le hX_le hX_E
    hX_betw j hj_le
  have hcond_j1 : 1 ≤ j + 1 ∧ j + 1 ≤ n := ⟨by omega, hj_lt_n⟩
  have hpiece_j1 : decompPiece X (j + 1) = X ⟨j, hj_lt_n⟩ := by
    simp [decompPiece, hcond_j1]
  have hsmall_Xj1 : IsSmallSubgraph G 𝒯 (decompPiece X (j + 1)) := by
    rw [hpiece_j1]
    exact hX_small ⟨j, hj_lt_n⟩
  have hbd_union_lt : (boundaryVertices G ((prefixUnion X j ∩ B) ∪ decompPiece X
    (j + 1))).ncard < θ := by
    let j_fin : Fin n := ⟨j, hj_lt_n⟩
    let S_j1 : Set α :=
      ((X j_fin).vertexSet ∩ (decompPiece X j).vertexSet) ∪
      ((X j_fin).vertexSet ∩ (decompPiece X (j + 2)).vertexSet) ∪
      {t j_fin}
    have hclaim5_sub : boundaryVertices G (decompPiece X (j + 1)) ⊆ S_j1 := by
      rw [hpiece_j1]
      exact (lemma_2_1_claim_5 hC_le hbd_C hX_le hX_E hX_disj hX_betw hX_t j_fin).1
    have hsub_total : boundaryVertices G ((prefixUnion X j ∩ B) ∪ decompPiece X (j + 1)) ⊆
        ((prefixUnion X j).vertexSet ∩ (A ∩ B).vertexSet) ∪ S_j1 := by
      intro v hv
      rcases boundaryVertices_union_subset G (prefixUnion X j ∩ B) (decompPiece X
        (j + 1)) hv with hv1 | hv2
      · rcases hbd_PjB_sub hv1 with hvR | ⟨hv_dj, hv_dj1⟩
        · exact Or.inl hvR
        · rw [hpiece_j1] at hv_dj1
          exact Or.inr (Or.inl (Or.inl ⟨hv_dj1, hv_dj⟩))
      · exact Or.inr (hclaim5_sub hv2)
    have h1 : ((X j_fin).vertexSet ∩ (decompPiece X j).vertexSet).ncard ≤ p := by
      by_cases hi : 1 ≤ j ∧ j ≤ n
      · simp only [decompPiece, hi, and_self, ↓reduceDIte]
        rw [Set.inter_comm]
        exact (hX_disj ⟨j - 1, by omega⟩ j_fin (Fin.lt_def.mpr (by dsimp [j_fin]; omega))).2
      · have hbot : decompPiece X j = ⊥ := dite_eq_right_iff.mpr fun h => (hi h).elim
        rw [hbot]
        simp
    have h2 : ((X j_fin).vertexSet ∩ (decompPiece X (j + 2)).vertexSet).ncard ≤ p := by
      by_cases hi : 1 ≤ j + 2 ∧ j + 2 ≤ n
      · simp only [decompPiece, hi, and_self, ↓reduceDIte]
        exact (hX_disj j_fin ⟨j + 2 - 1, by omega⟩ (Fin.lt_def.mpr (by dsimp [j_fin]; omega))).2
      · have hbot : decompPiece X (j + 2) = ⊥ := dite_eq_right_iff.mpr fun h => (hi h).elim
        rw [hbot]
        simp
    have hfin1 : ((X j_fin).vertexSet ∩ (decompPiece X j).vertexSet).Finite :=
      (X j_fin).vertexSet_finite.inter_of_left _
    have hfin2 : ((X j_fin).vertexSet ∩ (decompPiece X (j + 2)).vertexSet).Finite :=
      (X j_fin).vertexSet_finite.inter_of_left _
    have hfin_Sj1 : S_j1.Finite := (hfin1.union hfin2).union (Set.finite_singleton (t j_fin))
    have hSj1_le : S_j1.ncard ≤ 2 * p + 1 := by
      have hle_a : S_j1.ncard ≤
          (((X j_fin).vertexSet ∩ (decompPiece X j).vertexSet) ∪
            ((X j_fin).vertexSet ∩ (decompPiece X (j + 2)).vertexSet)).ncard +
          ({t j_fin} : Set α).ncard := Set.ncard_union_le _ _
      have hle_b := Set.ncard_union_le
        ((X j_fin).vertexSet ∩ (decompPiece X j).vertexSet)
        ((X j_fin).vertexSet ∩ (decompPiece X (j + 2)).vertexSet)
      rw [Set.ncard_singleton] at hle_a
      omega
    have hfin_R : ((prefixUnion X j).vertexSet ∩ (A ∩ B).vertexSet).Finite :=
      (prefixUnion X j).vertexSet_finite.inter_of_left _
    have hle1 := Set.ncard_le_ncard hsub_total (hfin_R.union hfin_Sj1)
    have hle2 := Set.ncard_union_le
      ((prefixUnion X j).vertexSet ∩ (A ∩ B).vertexSet) S_j1
    omega
  have hsmall_union : IsSmallSubgraph G 𝒯 ((prefixUnion X j ∩ B) ∪ decompPiece X (j + 1)) :=
    lemma_2_1_claim_7 h𝒯
      (inter_le (prefixUnion_le (fun i => (hX_le i).trans hC_le) j) hsep_AB.right_le)
      (decompPiece_le (fun i => (hX_le i).trans hC_le) (j + 1))
      (union_le (inter_le (prefixUnion_le (fun i => (hX_le i).trans hC_le) j) hsep_AB.right_le)
        (decompPiece_le (fun i => (hX_le i).trans hC_le) (j + 1)))
      le_rfl hsmall_PjB hsmall_Xj1 hbd_union_lt
  exact ⟨hj_lt_n, hsmall_union, hge_next⟩

/-- Claim (10) in the proof of Graph Minors XV, (2.1) (page 119):
"$k > 1$, and $(Q_k \cap B) \cup X_{k-1}$ is small, and $|Q_{k-1} \cap R| \ge ord(\mathscr{T}) -
2\rho - 1$." -/
private lemma lemma_2_1_claim_10 {G C A B : Hypergraph α β} {n θ p : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {t : Fin n → α} {X : Fin n → Hypergraph α β}
    (h𝒯 : IsTangle G θ 𝒯) (hp : 1 ≤ p) (hθ : 5 * p + 2 ≤ θ)
    (hAB : (A, B) ∈ 𝒯) (hB_le_C : B ≤ C) (hC_le : C ≤ G)
    (hbd_C : boundaryVertices G C ⊆ range t)
    (hX_le : ∀ j, X j ≤ C)
    (hX_V : ∀ v ∈ C.vertexSet, ∃ j, v ∈ (X j).vertexSet)
    (hX_E : ∀ e ∈ C.edgeSet, ∃ j, e ∈ (X j).edgeSet)
    (hX_disj : ∀ a b : Fin n, a < b →
      Disjoint (X a).edgeSet (X b).edgeSet ∧ ((X a).vertexSet ∩ (X b).vertexSet).ncard ≤ p)
    (hX_betw : ∀ a b c : Fin n, a ≤ b → b ≤ c →
      (X a).vertexSet ∩ (X c).vertexSet ⊆ (X b).vertexSet)
    (hX_t : ∀ j : Fin n, t j ∈ (X j).vertexSet)
    (hX_small : ∀ j : Fin n, IsSmallSubgraph G 𝒯 (X j))
    (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n + 1)
    (hk_lt_bound : ((suffixUnion X k).vertexSet ∩ (A ∩ B).vertexSet).ncard + 2 * p + 1 < θ)
    (hk_min : ∀ m : ℕ, 1 ≤ m → m ≤ n + 1 →
      ((suffixUnion X m).vertexSet ∩ (A ∩ B).vertexSet).ncard + 2 * p + 1 < θ → k ≤ m) :
    1 < k ∧
    IsSmallSubgraph G 𝒯 ((suffixUnion X k ∩ B) ∪ decompPiece X (k - 1)) ∧
    θ ≤ ((suffixUnion X (k - 1)).vertexSet ∩ (A ∩ B).vertexSet).ncard + 2 * p + 1 := by
  have hsep_AB := h𝒯.isSeparation hAB
  have hsmall_QkB : IsSmallSubgraph G 𝒯 (suffixUnion X k ∩ B) :=
    suffixUnion_inter_isSmall h𝒯 (by omega) hsep_AB hB_le_C hC_le hX_le hX_E hX_disj hX_betw
      hX_small k hk1 hkn (by omega)
  have hk_gt_1 : 1 < k := by
    by_contra! hle
    have hkeq : k = 1 := le_antisymm hle hk1
    subst hkeq
    have hQ1_B : suffixUnion X 1 ∩ B = B := by
      apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq
        (inter_le_right (suffixUnion_le (fun i => (hX_le i).trans hC_le) 1) hsep_AB.right_le) le_rfl
      · ext v
        simp only [inter_vertexSet, mem_inter_iff]
        refine ⟨fun h => h.2, fun hvB => ⟨?_, hvB⟩⟩
        obtain ⟨i, hi⟩ := hX_V v (hB_le_C.vertexSet_subset hvB)
        exact (mem_suffixUnion_vertexSet X le_rfl (by omega) v).mpr ⟨i, by omega, hi⟩
      · ext e
        simp only [inter_edgeSet, mem_inter_iff]
        refine ⟨fun h => h.2, fun heB => ⟨?_, heB⟩⟩
        obtain ⟨i, hi⟩ := hX_E e (hB_le_C.edgeSet_subset heB)
        exact (mem_suffixUnion_edgeSet X le_rfl (by omega) e).mpr ⟨i, by omega, hi⟩
    rw [hQ1_B] at hsmall_QkB
    exact not_isSmallSubgraph_of_mem_tangle h𝒯 hAB hsmall_QkB
  have hge_prev : θ ≤ ((suffixUnion X (k - 1)).vertexSet ∩ (A ∩ B).vertexSet).ncard + 2 * p + 1
    := by
    by_contra! hlt
    have hle := hk_min (k - 1) (by omega) (by omega) hlt
    omega
  have hcond_k1 : 1 ≤ k - 1 ∧ k - 1 ≤ n := ⟨by omega, by omega⟩
  have hpiece_k1 : decompPiece X (k - 1) = X ⟨k - 1 - 1, by omega⟩ := by
    simp [decompPiece, hcond_k1]
  have hsmall_Xk1 : IsSmallSubgraph G 𝒯 (decompPiece X (k - 1)) := by
    rw [hpiece_k1]
    exact hX_small ⟨k - 1 - 1, by omega⟩
  have hbd_union_lt : (boundaryVertices G ((suffixUnion X k ∩ B) ∪ decompPiece X
    (k - 1))).ncard < θ := by
    let k_fin : Fin n := ⟨k - 1 - 1, by omega⟩
    let S_k1 : Set α :=
      ((X k_fin).vertexSet ∩ (decompPiece X (k - 1 - 1)).vertexSet) ∪
      ((X k_fin).vertexSet ∩ (decompPiece X (k - 1 - 1 + 2)).vertexSet) ∪
      {t k_fin}
    have hclaim5_sub : boundaryVertices G (decompPiece X (k - 1)) ⊆ S_k1 := by
      rw [hpiece_k1]
      exact (lemma_2_1_claim_5 hC_le hbd_C hX_le hX_E hX_disj hX_betw hX_t k_fin).1
    have hk_add : k - 1 - 1 + 2 = k := by omega
    have hsub_total : boundaryVertices G ((suffixUnion X k ∩ B) ∪ decompPiece X (k - 1)) ⊆
        ((suffixUnion X k).vertexSet ∩ (A ∩ B).vertexSet) ∪ S_k1 := by
      intro v hv
      rcases boundaryVertices_union_subset G (suffixUnion X k ∩ B) (decompPiece X
        (k - 1)) hv with hv1 | hv2
      · by_cases hkn_eq : k = n + 1
        · subst hkn_eq
          rw [suffixUnion_n_add_one, bot_inter, boundaryVertices_bot] at hv1
          exact hv1.elim
        · have hk_le_n : k ≤ n := by omega
          have hbd_sub := boundaryVertices_suffixUnion_inter_subset hsep_AB hB_le_C hC_le hX_le hX_E
            hX_betw k hk1 hk_le_n
          rcases hbd_sub hv1 with hvR | ⟨hv_dk1, hv_dk⟩
          · exact Or.inl hvR
          · rw [hpiece_k1] at hv_dk1
            rw [← hk_add] at hv_dk
            exact Or.inr (Or.inl (Or.inr ⟨hv_dk1, hv_dk⟩))
      · exact Or.inr (hclaim5_sub hv2)
    have h1 : ((X k_fin).vertexSet ∩ (decompPiece X (k - 1 - 1)).vertexSet).ncard ≤ p := by
      by_cases hi : 1 ≤ k - 1 - 1 ∧ k - 1 - 1 ≤ n
      · simp only [decompPiece, hi, and_self, ↓reduceDIte]
        rw [Set.inter_comm]
        exact (hX_disj ⟨k - 1 - 1 - 1, by omega⟩ k_fin (Fin.lt_def.mpr (by dsimp [k_fin]; omega))).2
      · have hbot : decompPiece X (k - 1 - 1) = ⊥ := dite_eq_right_iff.mpr fun h => (hi h).elim
        rw [hbot]
        simp
    have h2 : ((X k_fin).vertexSet ∩ (decompPiece X (k - 1 - 1 + 2)).vertexSet).ncard ≤ p := by
      by_cases hi : 1 ≤ k - 1 - 1 + 2 ∧ k - 1 - 1 + 2 ≤ n
      · simp only [decompPiece, hi, and_self, ↓reduceDIte]
        exact (hX_disj k_fin ⟨k - 1 - 1 + 2 - 1, by omega⟩ (Fin.lt_def.mpr
          (by dsimp [k_fin]; omega))).2
      · have hbot : decompPiece X (k - 1 - 1 + 2) = ⊥ := dite_eq_right_iff.mpr fun h => (hi h).elim
        rw [hbot]
        simp
    have hfin1 : ((X k_fin).vertexSet ∩ (decompPiece X (k - 1 - 1)).vertexSet).Finite :=
      (X k_fin).vertexSet_finite.inter_of_left _
    have hfin2 : ((X k_fin).vertexSet ∩ (decompPiece X (k - 1 - 1 + 2)).vertexSet).Finite :=
      (X k_fin).vertexSet_finite.inter_of_left _
    have hfin_Sk1 : S_k1.Finite := (hfin1.union hfin2).union (Set.finite_singleton (t k_fin))
    have hSk1_le : S_k1.ncard ≤ 2 * p + 1 := by
      have hle_a : S_k1.ncard ≤
          (((X k_fin).vertexSet ∩ (decompPiece X (k - 1 - 1)).vertexSet) ∪
            ((X k_fin).vertexSet ∩ (decompPiece X (k - 1 - 1 + 2)).vertexSet)).ncard +
          ({t k_fin} : Set α).ncard := Set.ncard_union_le _ _
      have hle_b := Set.ncard_union_le
        ((X k_fin).vertexSet ∩ (decompPiece X (k - 1 - 1)).vertexSet)
        ((X k_fin).vertexSet ∩ (decompPiece X (k - 1 - 1 + 2)).vertexSet)
      rw [Set.ncard_singleton] at hle_a
      omega
    have hfin_R : ((suffixUnion X k).vertexSet ∩ (A ∩ B).vertexSet).Finite :=
      (suffixUnion X k).vertexSet_finite.inter_of_left _
    have hle1 := Set.ncard_le_ncard hsub_total (hfin_R.union hfin_Sk1)
    have hle2 := Set.ncard_union_le
      ((suffixUnion X k).vertexSet ∩ (A ∩ B).vertexSet) S_k1
    omega
  have hsmall_union : IsSmallSubgraph G 𝒯 ((suffixUnion X k ∩ B) ∪ decompPiece X (k - 1)) :=
    lemma_2_1_claim_7 h𝒯
      (inter_le (suffixUnion_le (fun i => (hX_le i).trans hC_le) k) hsep_AB.right_le)
      (decompPiece_le (fun i => (hX_le i).trans hC_le) (k - 1))
      (union_le (inter_le (suffixUnion_le (fun i => (hX_le i).trans hC_le) k) hsep_AB.right_le)
        (decompPiece_le (fun i => (hX_le i).trans hC_le) (k - 1)))
      le_rfl hsmall_QkB hsmall_Xk1 hbd_union_lt
  exact ⟨hk_gt_1, hsmall_union, hge_prev⟩

private lemma exists_max_nat_le (n : ℕ) (P : ℕ → Prop) (h0 : P 0) :
    ∃ j ≤ n, P j ∧ ∀ m ≤ n, P m → m ≤ j := by
  classical
  induction n with
  | zero => exact ⟨0, le_rfl, h0, fun m hm _ => hm⟩
  | succ n ih =>
    by_cases hsucc : P (n + 1)
    · exact ⟨n + 1, le_rfl, hsucc, fun m hm _ => hm⟩
    · rcases ih with ⟨j, hj_le, hjP, hj_max⟩
      refine ⟨j, by omega, hjP, fun m hm hmP => ?_⟩
      rcases Nat.le_or_eq_of_le_succ hm with hle | rfl
      · exact hj_max m hle hmP
      · exact (hsucc hmP).elim

private lemma exists_min_nat_ge_one (n : ℕ) (P : ℕ → Prop) (hn : P (n + 1)) :
    ∃ k, 1 ≤ k ∧ k ≤ n + 1 ∧ P k ∧ ∀ m, 1 ≤ m → m ≤ n + 1 → P m → k ≤ m := by
  obtain ⟨d, hd_le, hdP, hd_max⟩ := exists_max_nat_le n (fun d => P (n + 1 - d)) (by simpa using hn)
  refine ⟨n + 1 - d, by omega, by omega, hdP, fun m hm1 hmn hmP => ?_⟩
  have h := hd_max (n + 1 - m) (by omega) (by
    have heq : n + 1 - (n + 1 - m) = m := by omega
    rwa [heq])
  omega

/-- Convert a subgraph `H ≤ G` of a finite graph `G` to a subhypergraph of
`Hypergraph.ofGraph G hV hE`. -/
private def subgraphToHypergraph {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (H : Graph α β) (hH : H ≤ G) : Hypergraph α β :=
  Hypergraph.ofGraph H (hV.subset hH.vertexSet_mono) (hE.subset hH.edgeSet_mono)

private lemma subgraphToHypergraph_le {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hle : H₁ ≤ H₂) :
    subgraphToHypergraph hV hE H₁ h₁ ≤ subgraphToHypergraph hV hE H₂ h₂ where
  vertexSet_subset := hle.vertexSet_mono
  edgeSet_subset := hle.edgeSet_mono
  ends_eq e he := by
    ext v
    exact (hle.inc_congr he).symm

private lemma subgraphToHypergraph_le_ofGraph {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    {H : Graph α β} (hH : H ≤ G) :
    subgraphToHypergraph hV hE H hH ≤ Hypergraph.ofGraph G hV hE :=
  subgraphToHypergraph_le hV hE hH le_rfl hH

private theorem le_union_of_close_decomp {G B : Hypergraph α β} {n j k : ℕ}
    {X : Fin n → Hypergraph α β}
    (hB_le : B ≤ G) (hX_le : ∀ i, X i ≤ G)
    (hX_V : ∀ v ∈ B.vertexSet, ∃ i : Fin n, v ∈ (X i).vertexSet)
    (hX_E : ∀ e ∈ B.edgeSet, ∃ i : Fin n, e ∈ (X i).edgeSet)
    (hj_lt_n : j < n) (hk_gt_1 : 1 < k) (hkn : k ≤ n + 1) (hkj : k ≤ j + 3) :
    B ≤ ((prefixUnion X j ∩ B) ∪ decompPiece X (j + 1)) ∪
      ((suffixUnion X k ∩ B) ∪ decompPiece X (k - 1)) := by
  have hk1 : 1 ≤ k := by omega
  have hv : B.vertexSet ⊆
      (((prefixUnion X j ∩ B) ∪ decompPiece X (j + 1)) ∪
        ((suffixUnion X k ∩ B) ∪ decompPiece X (k - 1))).vertexSet := by
    intro v hvB
    obtain ⟨i, hvi⟩ := hX_V v hvB
    by_cases hi1 : i.1 < j
    · exact Or.inl (Or.inl ⟨(mem_prefixUnion_vertexSet X j v).mpr ⟨i, hi1, hvi⟩, hvB⟩)
    · by_cases hi2 : i.1 = j
      · left; right
        have hcond : 1 ≤ j + 1 ∧ j + 1 ≤ n := ⟨by omega, hj_lt_n⟩
        simp only [decompPiece, hcond, and_self, ↓reduceDIte, Nat.add_sub_cancel]
        have hi_eq : (⟨j, hj_lt_n⟩ : Fin n) = i := Fin.ext hi2.symm
        rwa [hi_eq]
      · by_cases hi3 : k - 1 ≤ i.1
        · exact Or.inr (Or.inl ⟨(mem_suffixUnion_vertexSet X hk1 hkn v).mpr ⟨i, hi3, hvi⟩, hvB⟩)
        · right; right
          have hcond : 1 ≤ k - 1 ∧ k - 1 ≤ n := ⟨by omega, by omega⟩
          simp only [decompPiece, hcond, and_self, ↓reduceDIte]
          have hi_eq : (⟨k - 1 - 1, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
          rwa [hi_eq]
  have he : B.edgeSet ⊆
      (((prefixUnion X j ∩ B) ∪ decompPiece X (j + 1)) ∪
        ((suffixUnion X k ∩ B) ∪ decompPiece X (k - 1))).edgeSet := by
    intro e heB
    obtain ⟨i, hei⟩ := hX_E e heB
    by_cases hi1 : i.1 < j
    · exact Or.inl (Or.inl ⟨(mem_prefixUnion_edgeSet X j e).mpr ⟨i, hi1, hei⟩, heB⟩)
    · by_cases hi2 : i.1 = j
      · left; right
        have hcond : 1 ≤ j + 1 ∧ j + 1 ≤ n := ⟨by omega, hj_lt_n⟩
        simp only [decompPiece, hcond, and_self, ↓reduceDIte, Nat.add_sub_cancel]
        have hi_eq : (⟨j, hj_lt_n⟩ : Fin n) = i := Fin.ext hi2.symm
        rwa [hi_eq]
      · by_cases hi3 : k - 1 ≤ i.1
        · exact Or.inr (Or.inl ⟨(mem_suffixUnion_edgeSet X hk1 hkn e).mpr ⟨i, hi3, hei⟩, heB⟩)
        · right; right
          have hcond : 1 ≤ k - 1 ∧ k - 1 ≤ n := ⟨by omega, by omega⟩
          simp only [decompPiece, hcond, and_self, ↓reduceDIte]
          have hi_eq : (⟨k - 1 - 1, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
          rwa [hi_eq]
  refine ⟨hv, he, fun e heB => ?_⟩
  have hle_u : ((prefixUnion X j ∩ B) ∪ decompPiece X (j + 1)) ∪
      ((suffixUnion X k ∩ B) ∪ decompPiece X (k - 1)) ≤ G :=
    union_le
      (union_le (inter_le (prefixUnion_le hX_le j) hB_le)
        (decompPiece_le hX_le (j + 1)))
      (union_le (inter_le (suffixUnion_le hX_le k) hB_le)
        (decompPiece_le hX_le (k - 1)))
  exact (hle_u.ends_eq e (he heB)).symm.trans (hB_le.ends_eq e heB)

/-- **Graph Minors XV, (2.1)** (page 116):
"Let $\mathscr{T}$ be a tangle in a graph $G$, let $\rho \ge 1$ with $ord(\mathscr{T}) \ge 5\rho+2$,
and
let $\mathscr{S}$ be a segregation of $G$ of type $(\rho, \kappa)$ for some $\kappa$. Suppose that
for
every $(C, \Omega) \in \mathscr{S}$ there is no $(A, B) \in \mathscr{T}$ of order $\le 2\rho+1$ with
$B \subseteq C$. Then $\mathscr{S}$ is $\mathscr{T}$-central." -/
theorem theorem_2_1_proof
    (G : Graph α β) (θ p κ : ℕ)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β))
    (𝒮 : Set (Society α β))
    (h𝒯 : IsGraphTangle G θ 𝒯)
    (hp : 1 ≤ p)
    (hθ : 5 * p + 2 ≤ θ)
    (h𝒮 : IsSegregationOfType G p κ 𝒮)
    (hno_small : ∀ S₀ ∈ 𝒮, ∀ A B : Hypergraph α β, (A, B) ∈ 𝒯 →
      separationOrder A B ≤ 2 * p + 1 → ¬ SubhypergraphInGraph B S₀.G) :
    IsCentralSegregation G 𝒯 𝒮 := by
  refine ⟨h𝒮.isSegregation, fun S₀ hS₀ A B hAB hB_sub => ?_⟩
  let G_H := Hypergraph.ofGraph G h𝒯.finite_V h𝒯.finite_E
  have hS₀_le : S₀.G ≤ G := h𝒮.isSegregation.le S₀ hS₀
  let C := subgraphToHypergraph h𝒯.finite_V h𝒯.finite_E S₀.G hS₀_le
  have hC_le : C ≤ G_H := subgraphToHypergraph_le_ofGraph h𝒯.finite_V h𝒯.finite_E hS₀_le
  have hsep_AB : G_H.IsSeparation A B := h𝒯.isTangle.isSeparation hAB
  have hB_le_C : B ≤ C := by
    refine ⟨hB_sub.1, hB_sub.2, fun e he => ?_⟩
    have h1 := hsep_AB.right_le.ends_eq e he
    have h2 := hC_le.ends_eq e (hB_sub.2 he)
    exact h2.symm.trans h1
  have hno_small_C : ∀ A' B' : Hypergraph α β, (A', B') ∈ 𝒯 →
      separationOrder A' B' ≤ 2 * p + 1 → ¬ (B' ≤ C) := by
    intro A' B' hA'B' hord hle
    exact hno_small S₀ hS₀ A' B' hA'B' hord ⟨hle.vertexSet_subset, hle.edgeSet_subset⟩
  have hPV : S₀.IsPVortex p := by
    by_cases hgt3 : 3 < S₀.Ω.bar.ncard
    · exact h𝒮.is_p_vortex hS₀ hgt3
    · exact isPVortex_of_bar_ncard_le_three (not_lt.mp hgt3) hp
  have hbd_C_bar : boundaryVertices G_H C ⊆ S₀.Ω.bar := by
    rintro v ⟨hvC, e, ⟨heG, heC⟩, hinc⟩
    have he_union : e ∈ E(subgraphSUnion G ((fun S' : Society α β => S'.G) '' 𝒮)) := by
      rw [h𝒮.isSegregation.union_eq]
      exact heG
    simp only [subgraphSUnion, edgeSet_restrict, mem_inter_iff, mem_iUnion, exists_prop] at he_union
    rcases he_union.2 with ⟨_, ⟨S', hS', rfl⟩, heS'⟩
    have hne : S₀ ≠ S' := by
      rintro rfl
      exact heC heS'
    have hvS' : v ∈ V(S'.G) := by
      rcases hinc with ⟨w, hlink⟩
      have hlink' : S'.G.IsLink e v w :=
        ((h𝒮.isSegregation.le S' hS').isLink_iff heS').mpr hlink
      exact hlink'.left_mem
    exact (h𝒮.isSegregation.vertex_inter_subset S₀ hS₀ S' hS' hne ⟨hvC, hvS'⟩).1
  by_cases hbar : S₀.Ω.bar.Nonempty
  swap
  · have hbar_eq : S₀.Ω.bar = ∅ := Set.not_nonempty_iff_eq_empty.mp hbar
    have hbd_empty : boundaryVertices G_H C = ∅ := Set.eq_empty_of_subset hbd_C_bar hbar_eq
    have hC_small : IsSmallSubgraph G_H 𝒯 C :=
      lemma_2_1_claim_6 h𝒯.isTangle (by omega) hno_small_C le_rfl hC_le
        (by rw [hbd_empty]; simp)
    have hACC : A ∪ C ∪ C = G_H := by
      rw [GM10.union_assoc, GM10.union_self]
      apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq (union_le hsep_AB.left_le hC_le) le_rfl
      · ext v
        refine ⟨fun h => (union_le hsep_AB.left_le hC_le).vertexSet_subset h, fun hv => ?_⟩
        rw [← hsep_AB.vertexSet_union] at hv
        exact hv.imp_right fun h => hB_le_C.vertexSet_subset h
      · ext e
        refine ⟨fun h => (union_le hsep_AB.left_le hC_le).edgeSet_subset h, fun he => ?_⟩
        rw [← hsep_AB.edgeSet_union] at he
        exact he.imp_right fun h => hB_le_C.edgeSet_subset h
    exact h𝒯.isTangle.axiom2 hAB hC_small hC_small hACC
  obtain ⟨n, t, X_gr, hlin, hdepth⟩ := GraphMinor.GM09.gm15_theorem_8_1.{u, v} S₀ p hbar hPV
  let X : Fin n → Hypergraph α β := fun i =>
    subgraphToHypergraph h𝒯.finite_V h𝒯.finite_E (X_gr i) ((hlin.le_G i).trans hS₀_le)
  have hX_le : ∀ i : Fin n, X i ≤ C := fun i =>
    subgraphToHypergraph_le h𝒯.finite_V h𝒯.finite_E
      ((hlin.le_G i).trans hS₀_le) hS₀_le (hlin.le_G i)
  have hX_V : ∀ v ∈ C.vertexSet, ∃ i : Fin n, v ∈ (X i).vertexSet := by
    intro v hv
    have hv_union : v ∈ V(subgraphSUnion S₀.G (range X_gr)) := by
      rw [hlin.union_eq]
      exact hv
    change v ∈ ⋃ P ∈ range X_gr, V(P) at hv_union
    simp only [mem_iUnion, mem_range, exists_prop] at hv_union
    rcases hv_union with ⟨_, ⟨i, rfl⟩, hvi⟩
    exact ⟨i, hvi⟩
  have hX_E : ∀ e ∈ C.edgeSet, ∃ i : Fin n, e ∈ (X i).edgeSet := by
    intro e he
    have he_union : e ∈ E(subgraphSUnion S₀.G (range X_gr)) := by
      rw [hlin.union_eq]
      exact he
    simp only [subgraphSUnion, edgeSet_restrict, mem_inter_iff, mem_iUnion, exists_prop] at he_union
    rcases he_union.2 with ⟨_, ⟨i, rfl⟩, hei⟩
    exact ⟨i, hei⟩
  have hX_disj : ∀ i j : Fin n, i < j →
      Disjoint (X i).edgeSet (X j).edgeSet ∧ ((X i).vertexSet ∩ (X j).vertexSet).ncard ≤ p :=
    fun i j hij => ⟨hlin.edge_disjoint i j hij, hdepth i j hij⟩
  have hX_betw : ∀ i j k : Fin n, i ≤ j → j ≤ k →
      (X i).vertexSet ∩ (X k).vertexSet ⊆ (X j).vertexSet := by
    intro i j k hij hjk v ⟨hvi, hvk⟩
    have hle := hlin.inter_le i j k hij hjk
    have hv_inter : v ∈ V(subgraphInter S₀.G (X_gr i) (X_gr k)) := ⟨hvi, hvk⟩
    exact hle.vertexSet_mono hv_inter
  have hX_t : ∀ i : Fin n, t i ∈ (X i).vertexSet := hlin.mem_vertexSet
  have hbd_C : boundaryVertices G_H C ⊆ range t := by
    rw [hlin.range_t]
    exact hbd_C_bar
  have hX_small : ∀ i : Fin n, IsSmallSubgraph G_H 𝒯 (X i) := by
    intro i
    have hbd_i := (lemma_2_1_claim_5 hC_le hbd_C hX_le hX_E hX_disj hX_betw hX_t i).2
    exact lemma_2_1_claim_6 h𝒯.isTangle (by omega) hno_small_C (hX_le i)
      ((hX_le i).trans hC_le) hbd_i
  classical
  obtain ⟨j, hj_le, hj_lt, hj_max⟩ := exists_max_nat_le n
    (fun m => ((prefixUnion X m).vertexSet ∩ (A ∩ B).vertexSet).ncard + 2 * p + 1 < θ)
    (by simp [prefixUnion]; omega)
  obtain ⟨hj_lt_n, hsmall_left, hge_left⟩ :=
    lemma_2_1_claim_9 h𝒯.isTangle hp hθ hAB hB_le_C hC_le hbd_C hX_le hX_V hX_E hX_disj
      hX_betw hX_t hX_small j hj_le hj_lt hj_max
  obtain ⟨k, hk1, hkn, hk_lt, hk_min⟩ := exists_min_nat_ge_one n
    (fun m => ((suffixUnion X m).vertexSet ∩ (A ∩ B).vertexSet).ncard + 2 * p + 1 < θ)
    (by rw [suffixUnion_n_add_one]; simp; omega)
  obtain ⟨hk_gt_1, hsmall_right, hge_right⟩ :=
    lemma_2_1_claim_10 h𝒯.isTangle hp hθ hAB hB_le_C hC_le hbd_C hX_le hX_V hX_E hX_disj
      hX_betw hX_t hX_small k hk1 hkn hk_lt hk_min
  by_cases hkj : k ≤ j + 3
  · have hB_sub_union := le_union_of_close_decomp hsep_AB.right_le
      (fun i => (hX_le i).trans hC_le)
      (fun v hv => hX_V v (hB_le_C.vertexSet_subset hv))
      (fun e he => hX_E e (hB_le_C.edgeSet_subset he))
      hj_lt_n hk_gt_1 hkn hkj
    have hbd_B_lt : (boundaryVertices G_H B).ncard < θ := by
      have hsub_R : boundaryVertices G_H B ⊆ (A ∩ B).vertexSet := by
        rintro v ⟨hvB, e, ⟨heG, heB⟩, hinc⟩
        have heA : e ∈ A.edgeSet := by
          have he_u : e ∈ A.edgeSet ∪ B.edgeSet := by
            rw [hsep_AB.edgeSet_union]
            exact heG
          exact he_u.resolve_right heB
        exact ⟨A.vertex_mem_of_inc ((inc_iff_of_le hsep_AB.left_le heA).mpr hinc), hvB⟩
      have hle := Set.ncard_le_ncard hsub_R (A ∩ B).vertexSet_finite
      have hord := h𝒯.isTangle.order_lt hAB
      unfold separationOrder at hord
      omega
    have hB_small : IsSmallSubgraph G_H 𝒯 B :=
      lemma_2_1_claim_7 h𝒯.isTangle
        (union_le (inter_le (prefixUnion_le (fun i => (hX_le i).trans hC_le) j) hsep_AB.right_le)
          (decompPiece_le (fun i => (hX_le i).trans hC_le) (j + 1)))
        (union_le (inter_le (suffixUnion_le (fun i => (hX_le i).trans hC_le) k) hsep_AB.right_le)
          (decompPiece_le (fun i => (hX_le i).trans hC_le) (k - 1)))
        hsep_AB.right_le hB_sub_union hsmall_left hsmall_right hbd_B_lt
    exact not_isSmallSubgraph_of_mem_tangle h𝒯.isTangle hAB hB_small
  · have hkj4 : j + 4 ≤ k := by omega
    have hj1_lt_n : j + 1 < n := by omega
    have hinter_sub : ((prefixUnion X (j + 1)).vertexSet ∩ (A ∩ B).vertexSet) ∩
        ((suffixUnion X (k - 1)).vertexSet ∩ (A ∩ B).vertexSet) ⊆
        (X ⟨j, hj_lt_n⟩).vertexSet ∩ (X ⟨j + 1, hj1_lt_n⟩).vertexSet := by
      rintro v ⟨⟨hvP, _⟩, ⟨hvQ, _⟩⟩
      obtain ⟨a, ha_lt, hva⟩ := (mem_prefixUnion_vertexSet X (j + 1) v).mp hvP
      obtain ⟨b, hb_ge, hvb⟩ := (mem_suffixUnion_vertexSet X (by omega) (by omega) v).mp hvQ
      refine ⟨?_, ?_⟩
      · exact hX_betw a ⟨j, hj_lt_n⟩ b
          (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
          (Fin.le_iff_val_le_val.mpr (by dsimp; omega)) ⟨hva, hvb⟩
      · exact hX_betw a ⟨j + 1, hj1_lt_n⟩ b
          (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
          (Fin.le_iff_val_le_val.mpr (by dsimp; omega)) ⟨hva, hvb⟩
    have hinter_le_p : (((prefixUnion X (j + 1)).vertexSet ∩ (A ∩ B).vertexSet) ∩
        ((suffixUnion X (k - 1)).vertexSet ∩ (A ∩ B).vertexSet)).ncard ≤ p := by
      have hfin_cap : ((X ⟨j, hj_lt_n⟩).vertexSet ∩ (X ⟨j + 1, hj1_lt_n⟩).vertexSet).Finite :=
        (X ⟨j, hj_lt_n⟩).vertexSet_finite.inter_of_left _
      have hle1 := Set.ncard_le_ncard hinter_sub hfin_cap
      have hle2 := (hX_disj ⟨j, hj_lt_n⟩ ⟨j + 1, hj1_lt_n⟩ (Fin.lt_def.mpr (by dsimp; omega))).2
      omega
    have hunion_sub : ((prefixUnion X (j + 1)).vertexSet ∩ (A ∩ B).vertexSet) ∪
        ((suffixUnion X (k - 1)).vertexSet ∩ (A ∩ B).vertexSet) ⊆ (A ∩ B).vertexSet := by
      rintro v (⟨_, hvR⟩ | ⟨_, hvR⟩) <;> exact hvR
    have hunion_lt_theta : (((prefixUnion X (j + 1)).vertexSet ∩ (A ∩ B).vertexSet) ∪
        ((suffixUnion X (k - 1)).vertexSet ∩ (A ∩ B).vertexSet)).ncard < θ := by
      have hle := Set.ncard_le_ncard hunion_sub (A ∩ B).vertexSet_finite
      have hord := h𝒯.isTangle.order_lt hAB
      unfold separationOrder at hord
      omega
    have hfin_L : ((prefixUnion X (j + 1)).vertexSet ∩ (A ∩ B).vertexSet).Finite :=
      (prefixUnion X (j + 1)).vertexSet_finite.inter_of_left _
    have hfin_R : ((suffixUnion X (k - 1)).vertexSet ∩ (A ∩ B).vertexSet).Finite :=
      (suffixUnion X (k - 1)).vertexSet_finite.inter_of_left _
    have hadd := Set.ncard_union_add_ncard_inter
      ((prefixUnion X (j + 1)).vertexSet ∩ (A ∩ B).vertexSet)
      ((suffixUnion X (k - 1)).vertexSet ∩ (A ∩ B).vertexSet) hfin_L hfin_R
    omega

end GraphMinor.GM15
