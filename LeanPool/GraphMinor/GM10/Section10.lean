/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs2
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM10.Section6
import LeanPool.GraphMinor.GM10.Section8
import LeanPool.GraphMinor.GM10.Section9
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Tangle Tree-Decompositions (Graph Minors X, Section 10)

This file formalizes Section 10 of N. Robertson and P. D. Seymour,
*Graph Minors. X. Obstructions to tree-decomposition*, J. Combin. Theory Ser. B 52 (1991) 153–190
(pages 180–184):

- `exists_distinguishes_iff_areDistinguishable` and `theorem_10_1`
  (**Graph Minors X, (10.1)**, page 180): either there is a separation of `G` distinguishing `𝒯₁`
  from `𝒯₂` or `𝒯₁, 𝒯₂` are indistinguishable, and not both.
- `IsDistinction.unique`, `isDistinction_comm`, and `exists_isDistinction_iff` (page 181):
  uniqueness, symmetry, and existence of the `(𝒯₁, 𝒯₂)`-distinction.
- `theorem_10_2` (**Graph Minors X, (10.2)**, page 181): if `𝒯₁, 𝒯₂` are distinguishable tangles
  in `G`, the `(𝒯₁, 𝒯₂)`-distinction is doubly `λ`-robust.
- `theorem_10_3_claim_1` through `theorem_10_3_claim_7` and `theorem_10_3`
  (**Graph Minors X, (10.3)**, pages 181–184): existence of a standard tree-decomposition of `G`
  relative to mutually distinguishable tangles `𝒯₁, …, 𝒯ₙ`.
- `theorem_10_4_strict_inclusion`, `IsStandardTreeDecomposition.card_le_ncard_vertexSet`,
  `IsStandardTreeDecomposition.ncard_edgeSet_le`, `card_le_of_mutually_distinguishable`, and
  `theorem_10_4` (**Graph Minors X, (10.4)**, page 184): in any hypergraph `G` there are at most
  `|V(G)|` maximal tangles.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph Hypergraph

universe u v w

variable {α : Type u} {β : Type v} {Λ : Type w} {ι : Type*}

/-! ## Graph Minors X, (10.1) and basic properties of distinctions -/

theorem distinguishes_comm {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)}
    {A B : Hypergraph α β} :
    Distinguishes 𝒯₁ 𝒯₂ A B ↔ Distinguishes 𝒯₂ 𝒯₁ B A :=
  and_comm

theorem areIndistinguishable_comm {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)} :
    AreIndistinguishable 𝒯₁ 𝒯₂ ↔ AreIndistinguishable 𝒯₂ 𝒯₁ :=
  or_comm

theorem areDistinguishable_comm {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)} :
    AreDistinguishable 𝒯₁ 𝒯₂ ↔ AreDistinguishable 𝒯₂ 𝒯₁ :=
  not_congr areIndistinguishable_comm

/-- If `(A, B)` distinguishes `𝒯₁` from `𝒯₂`, then `𝒯₁` and `𝒯₂` are distinguishable. -/
theorem areDistinguishable_of_distinguishes {G : Hypergraph α β} {θ₁ θ₂ : ℕ}
    {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯₁ : IsTangle G θ₁ 𝒯₁) (h𝒯₂ : IsTangle G θ₂ 𝒯₂)
    {A B : Hypergraph α β} (h : Distinguishes 𝒯₁ 𝒯₂ A B) :
    AreDistinguishable 𝒯₁ 𝒯₂ := by
  rintro (hsub | hsub)
  · exact theorem_2_1_proof h𝒯₂ h.2 (hsub h.1)
  · exact theorem_2_1_proof h𝒯₁ h.1 (hsub h.2)

/-- Symmetry step in the proof of **Graph Minors X, (10.1)** (page 180): when `θ₁ ≤ θ₂`,
`𝒯₁` and `𝒯₂` are distinguishable if and only if there is a separation distinguishing `𝒯₁` from
`𝒯₂`. -/
private theorem exists_distinguishes_of_areDistinguishable_of_le {G : Hypergraph α β}
    {θ₁ θ₂ : ℕ} {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯₁ : IsTangle G θ₁ 𝒯₁) (h𝒯₂ : IsTangle G θ₂ 𝒯₂) (hle : θ₁ ≤ θ₂)
    (hdist : AreDistinguishable 𝒯₁ 𝒯₂) :
    ∃ A B : Hypergraph α β, Distinguishes 𝒯₁ 𝒯₂ A B := by
  have hnot_sub : ¬ 𝒯₁ ⊆ 𝒯₂ := fun hsub ↦ hdist (Or.inl hsub)
  obtain ⟨⟨A, B⟩, hAB₁, hAB₂⟩ := Set.not_subset.1 hnot_sub
  have hsep : G.IsSeparation A B := h𝒯₁.isSeparation hAB₁
  have hord : separationOrder A B < θ₂ := (h𝒯₁.order_lt hAB₁).trans_le hle
  have hBA₂ : (B, A) ∈ 𝒯₂ := (h𝒯₂.axiom1 hsep hord).resolve_left hAB₂
  exact ⟨A, B, hAB₁, hBA₂⟩

/-- Equivalence form of **Graph Minors X, (10.1)** (page 180):
there is a separation of `G` which distinguishes `𝒯₁` from `𝒯₂` if and only if `𝒯₁` and `𝒯₂` are
distinguishable. -/
theorem exists_distinguishes_iff_areDistinguishable {G : Hypergraph α β} {θ₁ θ₂ : ℕ}
    {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯₁ : IsTangle G θ₁ 𝒯₁) (h𝒯₂ : IsTangle G θ₂ 𝒯₂) :
    (∃ A B : Hypergraph α β, Distinguishes 𝒯₁ 𝒯₂ A B) ↔ AreDistinguishable 𝒯₁ 𝒯₂ := by
  refine ⟨fun ⟨A, B, h⟩ ↦ areDistinguishable_of_distinguishes h𝒯₁ h𝒯₂ h, fun hdist ↦ ?_⟩
  rcases le_total θ₁ θ₂ with hle | hle
  · exact exists_distinguishes_of_areDistinguishable_of_le h𝒯₁ h𝒯₂ hle hdist
  · obtain ⟨B, A, hBA⟩ :=
      exists_distinguishes_of_areDistinguishable_of_le h𝒯₂ h𝒯₁ hle (areDistinguishable_comm.1 hdist)
    exact ⟨A, B, distinguishes_comm.2 hBA⟩

/-- **Graph Minors X, (10.1)** (page 180):
"Either there is a separation of $G$ which distinguishes $\mathscr{T}_1$ from $\mathscr{T}_2$
or $\mathscr{T}_1$, $\mathscr{T}_2$ are indistinguishable and not both." -/
theorem theorem_10_1_proof {G : Hypergraph α β} {θ₁ θ₂ : ℕ}
    {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯₁ : IsTangle G θ₁ 𝒯₁) (h𝒯₂ : IsTangle G θ₂ 𝒯₂) :
    ((∃ A B : Hypergraph α β, Distinguishes 𝒯₁ 𝒯₂ A B) ∨ AreIndistinguishable 𝒯₁ 𝒯₂) ∧
      ¬ ((∃ A B : Hypergraph α β, Distinguishes 𝒯₁ 𝒯₂ A B) ∧ AreIndistinguishable 𝒯₁ 𝒯₂) := by
  rw [exists_distinguishes_iff_areDistinguishable h𝒯₁ h𝒯₂]
  unfold AreDistinguishable
  exact ⟨(em _).symm, fun ⟨h1, h2⟩ ↦ h1 h2⟩

/-- Uniqueness of the `(𝒯₁, 𝒯₂)`-distinction (Graph Minors X, Section 10, page 181):
"From the first tie-breaker axiom, $(A, B)$ is unique, and we may speak of *the*
$(\mathscr{T}_1, \mathscr{T}_2)$-distinction." -/
theorem IsDistinction.unique [LinearOrder Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hTB : IsTieBreaker G lam)
    {θ₁ : ℕ} {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)} (h𝒯₁ : IsTangle G θ₁ 𝒯₁)
    {A B A' B' : Hypergraph α β}
    (h : IsDistinction lam 𝒯₁ 𝒯₂ A B) (h' : IsDistinction lam 𝒯₁ 𝒯₂ A' B') :
    A = A' ∧ B = B' := by
  have hle1 : lam (A, B) ≤ lam (A', B') := h.2 h'.1
  have hle2 : lam (A', B') ≤ lam (A, B) := h'.2 h.1
  have heq : lam (A, B) = lam (A', B') := le_antisymm hle1 hle2
  have hsep : G.IsSeparation A B := h𝒯₁.isSeparation h.1.1
  have hsep' : G.IsSeparation A' B' := h𝒯₁.isSeparation h'.1.1
  rcases (hTB.axiom1 hsep hsep').1 heq with h1 | ⟨rfl, rfl⟩
  · exact h1
  · exact (theorem_2_1_proof h𝒯₁ h.1.1 h'.1.1).elim

/-- `(A, B)` is the `(𝒯₁, 𝒯₂)`-distinction if and only if `(B, A)` is the `(𝒯₂, 𝒯₁)`-distinction
(Graph Minors X, Section 10, proof of (10.2), page 181). -/
theorem isDistinction_comm [LinearOrder Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hTB : IsTieBreaker G lam)
    {θ₁ θ₂ : ℕ} {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯₁ : IsTangle G θ₁ 𝒯₁) (h𝒯₂ : IsTangle G θ₂ 𝒯₂)
    {A B : Hypergraph α β} :
    IsDistinction lam 𝒯₁ 𝒯₂ A B ↔ IsDistinction lam 𝒯₂ 𝒯₁ B A := by
  constructor <;> rintro ⟨hdist, hmin⟩
  · refine ⟨distinguishes_comm.1 hdist, fun B' A' h' ↦ ?_⟩
    have hsep : G.IsSeparation A B := h𝒯₁.isSeparation hdist.1
    have hsep' : G.IsSeparation A' B' := h𝒯₁.isSeparation h'.2
    rw [hTB.lam_swap hsep, hTB.lam_swap hsep']
    exact hmin (distinguishes_comm.2 h')
  · refine ⟨distinguishes_comm.2 hdist, fun A' B' h' ↦ ?_⟩
    have hsep : G.IsSeparation B A := h𝒯₂.isSeparation hdist.1
    have hsep' : G.IsSeparation B' A' := h𝒯₂.isSeparation h'.2
    rw [hTB.lam_swap hsep, hTB.lam_swap hsep']
    exact hmin (distinguishes_comm.1 h')

/-- Existence of the `(𝒯₁, 𝒯₂)`-distinction (Graph Minors X, Section 10, page 181):
"There is a $(\mathscr{T}_1, \mathscr{T}_2)$-distinction if and only if $\mathscr{T}_1,
\mathscr{T}_2$ are distinguishable." -/
theorem exists_isDistinction_iff [LinearOrder Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ₁ θ₂ : ℕ} {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯₁ : IsTangle G θ₁ 𝒯₁) (h𝒯₂ : IsTangle G θ₂ 𝒯₂) :
    (∃ A B : Hypergraph α β, IsDistinction lam 𝒯₁ 𝒯₂ A B) ↔ AreDistinguishable 𝒯₁ 𝒯₂ := by
  rw [← exists_distinguishes_iff_areDistinguishable h𝒯₁ h𝒯₂]
  refine ⟨fun ⟨A, B, h, _⟩ ↦ ⟨A, B, h⟩, fun ⟨A₀, B₀, h₀⟩ ↦ ?_⟩
  classical
  let D : Set (Hypergraph α β × Hypergraph α β) := {p | Distinguishes 𝒯₁ 𝒯₂ p.1 p.2}
  have hD_fin : D.Finite :=
    finite_of_forall_isSeparation fun p hp ↦ h𝒯₁.isSeparation hp.1
  have hD_ne : hD_fin.toFinset.Nonempty := ⟨(A₀, B₀), hD_fin.mem_toFinset.2 h₀⟩
  obtain ⟨⟨A, B⟩, hmem, hmin⟩ := hD_fin.toFinset.exists_min_image lam hD_ne
  refine ⟨A, B, hD_fin.mem_toFinset.1 hmem, fun A' B' h' ↦ ?_⟩
  exact hmin (A', B') (hD_fin.mem_toFinset.2 h')

/-! ## Graph Minors X, (10.2) -/

/-- If `(A, B)` is a separation of `G` and `(C, D)` is a separation of `A`, then `(C, B ∪ D)` is a
separation of `G`. -/
theorem isSeparation_of_isSeparation_left {G A B C D : Hypergraph α β}
    (hAB : G.IsSeparation A B) (hCD : A.IsSeparation C D) :
    G.IsSeparation C (B ∪ D) := by
  have hC_G : C ≤ G := hCD.left_le.trans hAB.left_le
  have hD_G : D ≤ G := hCD.right_le.trans hAB.left_le
  rw [isSeparation_iff_of_le hC_G (union_le hAB.right_le hD_G)]
  refine ⟨?_, ?_, ?_⟩
  · rw [union_vertexSet, ← Set.union_assoc, Set.union_comm C.vertexSet B.vertexSet,
      Set.union_assoc, hCD.vertexSet_union, Set.union_comm B.vertexSet A.vertexSet,
      hAB.vertexSet_union]
  · rw [union_edgeSet, ← Set.union_assoc, Set.union_comm C.edgeSet B.edgeSet,
      Set.union_assoc, hCD.edgeSet_union, Set.union_comm B.edgeSet A.edgeSet,
      hAB.edgeSet_union]
  · ext e
    simp only [union_edgeSet, Set.mem_inter_iff, Set.mem_union, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro heC (heB | heD)
    · exact hAB.notMem_edgeSet_right (hCD.left_le.edgeSet_subset heC) heB
    · exact hCD.notMem_edgeSet_right heC heD

/-- Key step of **Graph Minors X, (10.2)** (page 181): the `(𝒯₁, 𝒯₂)`-distinction is `λ`-robust. -/
private theorem isLambdaRobust_of_isDistinction [LinearOrder Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hTB : IsTieBreaker G lam)
    {θ₁ θ₂ : ℕ} {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯₁ : IsTangle G θ₁ 𝒯₁) (h𝒯₂ : IsTangle G θ₂ 𝒯₂)
    {A B : Hypergraph α β} (hdist : IsDistinction lam 𝒯₁ 𝒯₂ A B) :
    IsLambdaRobust G lam A B := by
  have hAB : G.IsSeparation A B := h𝒯₁.isSeparation hdist.1.1
  refine ⟨hAB, fun C D hCD ↦ ?_⟩
  by_contra! hlt
  rcases hlt with ⟨hltC, hltD⟩
  have hsepC : G.IsSeparation C (B ∪ D) := isSeparation_of_isSeparation_left hAB hCD
  have hsepD : G.IsSeparation D (B ∪ C) := isSeparation_of_isSeparation_left hAB hCD.symm
  have hordC_le : separationOrder C (B ∪ D) ≤ separationOrder A B := by
    by_contra! hgt
    exact not_lt_of_ge hltC.le (hTB.axiom3 hAB hsepC hgt)
  have hordD_le : separationOrder D (B ∪ C) ≤ separationOrder A B := by
    by_contra! hgt
    exact not_lt_of_ge hltD.le (hTB.axiom3 hAB hsepD hgt)
  have hordAB_1 : separationOrder A B < θ₁ := h𝒯₁.order_lt hdist.1.1
  have hordAB_2 : separationOrder A B < θ₂ := by
    rw [separationOrder_comm]
    exact h𝒯₂.order_lt hdist.1.2
  have hC_in_1 : (C, B ∪ D) ∈ 𝒯₁ :=
    theorem_2_9_proof h𝒯₁ hdist.1.1 hsepC (hordC_le.trans_lt hordAB_1)
      (Or.inr (Or.inl hCD.left_le.vertexSet_subset))
  have hD_in_1 : (D, B ∪ C) ∈ 𝒯₁ :=
    theorem_2_9_proof h𝒯₁ hdist.1.1 hsepD (hordD_le.trans_lt hordAB_1)
      (Or.inr (Or.inl hCD.right_le.vertexSet_subset))
  have hC_not_2 : (B ∪ D, C) ∉ 𝒯₂ := fun hm ↦
    not_lt_of_ge (hdist.2 ⟨hC_in_1, hm⟩) hltC
  have hD_not_2 : (B ∪ C, D) ∉ 𝒯₂ := fun hm ↦
    not_lt_of_ge (hdist.2 ⟨hD_in_1, hm⟩) hltD
  have hC_in_2 : (C, B ∪ D) ∈ 𝒯₂ :=
    (h𝒯₂.axiom1 hsepC (hordC_le.trans_lt hordAB_2)).resolve_right hC_not_2
  have hD_in_2 : (D, B ∪ C) ∈ 𝒯₂ :=
    (h𝒯₂.axiom1 hsepD (hordD_le.trans_lt hordAB_2)).resolve_right hD_not_2
  apply h𝒯₂.axiom2 hdist.1.2 hC_in_2 hD_in_2
  rw [union_assoc, hCD.union_eq, union_comm B A, hAB.union_eq]

/-- **Graph Minors X, (10.2)** (page 181):
"If $\mathscr{T}_1, \mathscr{T}_2$ are distinguishable tangles in $G$, the $(\mathscr{T}_1,
\mathscr{T}_2)$-distinction is doubly $\lambda$-robust." -/
theorem theorem_10_2_proof [LinearOrder Λ]
    (G : Hypergraph α β) (lam : Hypergraph α β × Hypergraph α β → Λ)
    (θ₁ θ₂ : ℕ) (𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β))
    (A B : Hypergraph α β)
    (hTB : IsTieBreaker G lam)
    (h𝒯₁ : IsTangle G θ₁ 𝒯₁)
    (h𝒯₂ : IsTangle G θ₂ 𝒯₂)
    (hdist : IsDistinction lam 𝒯₁ 𝒯₂ A B) :
    IsDoublyLambdaRobust G lam A B :=
  ⟨isLambdaRobust_of_isDistinction hTB h𝒯₁ h𝒯₂ hdist,
   isLambdaRobust_of_isDistinction hTB h𝒯₂ h𝒯₁
     ((isDistinction_comm hTB h𝒯₁ h𝒯₂).1 hdist)⟩

/-! ## Tree path and edge lemmas for (10.3) -/

/-- If a walk `p : T.Walk x y` does not contain the edge `e`, then `x` and `y` are reachable in
`T.deleteEdges {e}`. -/
private theorem reachable_deleteEdges_of_notMem_edges {T : SimpleGraph ι} {e : Sym2 ι}
    {x y : ι} (p : T.Walk x y) (he : e ∉ p.edges) :
    (T.deleteEdges {e}).Reachable x y := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons a b c hab q ih =>
    simp only [Walk.edges_cons, List.mem_cons, not_or] at he
    have hadj : (T.deleteEdges {e}).Adj a b :=
      deleteEdges_adj.mpr ⟨hab, Ne.symm he.1⟩
    exact hadj.reachable.trans (ih he.2)

/-- In a tree `T`, an edge `e ∈ T.edgeSet` lies on a path `p : T.Walk x y` if and only if
`x` and `y` are in different components of `T \ e`. -/
theorem edge_mem_path_iff_not_reachable_deleteEdges {T : SimpleGraph ι} (hT : T.IsTree)
    {e : Sym2 ι} {x y : ι} (p : T.Walk x y) (hp : p.IsPath) :
    e ∈ p.edges ↔ ¬ (T.deleteEdges {e}).Reachable x y := by
  classical
  constructor
  · intro he ⟨q⟩
    let q_path := q.toPath
    have hemb : T.deleteEdges {e} ≤ T := SimpleGraph.deleteEdges_le {e}
    let q' : T.Walk x y := q_path.1.map (Hom.ofLE hemb)
    have hq'_path : q'.IsPath := q_path.2.map (fun _ _ h ↦ h)
    obtain ⟨_, _, huniq⟩ := hT.existsUnique_path x y
    have hpq : p = q' := (huniq p hp).trans (huniq q' hq'_path).symm
    rw [hpq] at he
    have he_sub : e ∈ q_path.1.edges := by
      simpa [q', Walk.edges_map] using he
    have he_q : e ∈ q.edges := Walk.edges_toPath_subset_edges q he_sub
    have hnot : ∀ {u v : ι} (r : (T.deleteEdges {e}).Walk u v), e ∉ r.edges := by
      intro u v r
      induction r with
      | nil => simp
      | @cons a b c hab r ih =>
        simp only [Walk.edges_cons, List.mem_cons, not_or]
        exact ⟨Ne.symm (deleteEdges_adj.mp hab).2, ih⟩
    exact hnot q he_q
  · intro hnr
    by_contra he
    exact hnr (reachable_deleteEdges_of_notMem_edges p he)

/-- In a tree `T`, if `e = s(u, v)` is an edge of `T` (`T.Adj u v`), then `¬ (T \ e).Reachable x y`
if and only if `(T \ e).Reachable u x ∧ (T \ e).Reachable v y` or
`(T \ e).Reachable v x ∧ (T \ e).Reachable u y`. -/
theorem not_reachable_deleteEdges_iff_sides {T : SimpleGraph ι} (hT : T.IsTree)
    {u v x y : ι} (hadj : T.Adj u v) :
    ¬ (T.deleteEdges {s(u, v)}).Reachable x y ↔
      ((T.deleteEdges {s(u, v)}).Reachable u x ∧ (T.deleteEdges {s(u, v)}).Reachable v y) ∨
      ((T.deleteEdges {s(u, v)}).Reachable v x ∧ (T.deleteEdges {s(u, v)}).Reachable u y) := by
  have hnot_uv := not_reachable_deleteEdges hT hadj
  have hx := reachable_deleteEdges_or hT.connected (u := u) (v := v) x
  have hy := reachable_deleteEdges_or hT.connected (u := u) (v := v) y
  constructor
  · intro hnr
    rcases hx with hux | hvx <;> rcases hy with huy | hvy
    · exfalso; exact hnr (hux.symm.trans huy)
    · exact Or.inl ⟨hux, hvy⟩
    · exact Or.inr ⟨hvx, huy⟩
    · exfalso; exact hnr (hvx.symm.trans hvy)
  · rintro (⟨hux, hvy⟩ | ⟨hvx, huy⟩) hxy
    · exact hnot_uv (hux.trans (hxy.trans hvy.symm))
    · exact hnot_uv (huy.trans (hxy.symm.trans hvx.symm))

/-! ## Claims (1)–(7) and Proof of Graph Minors X, (10.3) -/

/-- Claim (1) in the proof of **Graph Minors X, (10.3)** (page 182):
"For $t_0 \in T$ and $1 \le i < j \le n$, $t_0$ is not a home for both $\mathscr{T}_i$ and
$\mathscr{T}_j$." -/
theorem theorem_10_3_claim_1 [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)}
    {e : Sym2 ι} {A B : Hypergraph α β}
    (hmk : MakesSeparation T τ e A B) (hdist : Distinguishes 𝒯₁ 𝒯₂ A B)
    (t₀ : ι) :
    ¬ (IsHome T τ 𝒯₁ t₀ ∧ IsHome T τ 𝒯₂ t₀) := by
  rintro ⟨h1, h2⟩
  obtain ⟨u, v, hadj, rfl, rfl, rfl⟩ := hmk
  rcases reachable_deleteEdges_or hTD.isTree.connected (u := u) (v := v) t₀ with hut₀ | hvt₀
  · exact h1 hadj hut₀ hdist.1
  · have h2' := h2 hadj.symm (by simpa [Sym2.eq_swap] using hvt₀)
    exact h2' (by simpa [Sym2.eq_swap] using hdist.2)

/-- An edge `e` of `T` is `θ`-relevant if the separations made by `e` have order `< θ`
(Graph Minors X, Section 10, proof of (10.3), page 182). -/
def IsRelevantEdge [Fintype ι] (T : SimpleGraph ι) (τ : ι → Hypergraph α β)
    (θ : ℕ) (e : Sym2 ι) : Prop :=
  ∃ u v : ι, T.Adj u v ∧ e = s(u, v) ∧
    separationOrder (treeDecompSide T τ s(u, v) u) (treeDecompSide T τ s(u, v) v) < θ

theorem IsRelevantEdge.order_lt_of_makesSeparation [Fintype ι] {T : SimpleGraph ι}
    {τ : ι → Hypergraph α β} {θ : ℕ} {e : Sym2 ι}
    (hrel : IsRelevantEdge T τ θ e) {A B : Hypergraph α β}
    (hmk : MakesSeparation T τ e A B) :
    separationOrder A B < θ := by
  obtain ⟨u, v, _, he, hord⟩ := hrel
  obtain ⟨u', v', _, he', rfl, rfl⟩ := hmk
  rcases Sym2.eq_iff.1 (he.symm.trans he') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hord
  · simpa [Sym2.eq_swap, separationOrder_comm] using hord

/-- Claim (2) in the proof of **Graph Minors X, (10.3)** (page 182):
"$t_0 \in V(T)$ is a home for $\mathscr{T}_i$ if and only if every $i$-relevant edge of $T$
is directed towards $t_0$." -/
theorem theorem_10_3_claim_2 [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {θ : ℕ} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) (t₀ : ι) :
    IsHome T τ 𝒯 t₀ ↔
      ∀ ⦃u v : ι⦄, T.Adj u v →
        separationOrder (treeDecompSide T τ s(u, v) u) (treeDecompSide T τ s(u, v) v) < θ →
        (T.deleteEdges {s(u, v)}).Reachable u t₀ →
        (treeDecompSide T τ s(u, v) v, treeDecompSide T τ s(u, v) u) ∈ 𝒯 := by
  constructor
  · intro hHome u v hadj hord hut₀
    have hsep := hTD.isSeparation_treeDecompSide hadj
    exact (h𝒯.axiom1 hsep hord).resolve_left (hHome hadj hut₀)
  · intro hDir u v hadj hut₀ hm
    have hord := h𝒯.order_lt hm
    exact theorem_2_1_proof h𝒯 hm (hDir hadj hord hut₀)

/-- Sub-claim of Claim (3) in the proof of **Graph Minors X, (10.3)** (pages 182–183):
for any two `i`-relevant edges `s(u, v)` and `s(u', v')` directed towards `v` and `v'` respectively,
the head components `V(T₂)` and `V(T'₂)` intersect. -/
theorem theorem_10_3_claim_3_heads_inter [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {θ : ℕ} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {u v u' v' : ι} (hadj : T.Adj u v) (hadj' : T.Adj u' v')
    (h1 : (treeDecompSide T τ s(u, v) u, treeDecompSide T τ s(u, v) v) ∈ 𝒯)
    (h2 : (treeDecompSide T τ s(u', v') u', treeDecompSide T τ s(u', v') v') ∈ 𝒯) :
    ∃ t : ι, (T.deleteEdges {s(u, v)}).Reachable v t ∧
      (T.deleteEdges {s(u', v')}).Reachable v' t := by
  by_contra! hdisj
  have hsub : treeDecompSide T τ s(u', v') v' ≤ treeDecompSide T τ s(u, v) u := by
    apply biUnion_mono hTD.le
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact (reachable_deleteEdges_or hTD.isTree.connected t).resolve_right
      fun hvt ↦ hdisj t hvt ht
  have hsep' := hTD.isSeparation_treeDecompSide hadj'
  apply h𝒯.axiom2 h1 h1 h2
  rw [union_self]
  have hle1 := (hTD.isSeparation_treeDecompSide hadj).left_le
  have hle2 := hsep'.left_le
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq (union_le hle1 hle2) le_rfl ?_ ?_
  · ext x
    simp only [union_vertexSet, Set.mem_union]
    exact ⟨fun h ↦ h.elim (fun hx ↦ hle1.vertexSet_subset hx) (fun hx ↦ hle2.vertexSet_subset hx),
      fun hx ↦ (hsep'.vertexSet_union.symm ▸ hx).elim Or.inr
        (fun hx' ↦ Or.inl (hsub.vertexSet_subset hx'))⟩
  · ext e
    simp only [union_edgeSet, Set.mem_union]
    exact ⟨fun h ↦ h.elim (fun he ↦ hle1.edgeSet_subset he) (fun he ↦ hle2.edgeSet_subset he),
      fun he ↦ (hsep'.edgeSet_union.symm ▸ he).elim Or.inr
        (fun he' ↦ Or.inl (hsub.edgeSet_subset he'))⟩

/-- First part of Claim (3) in the proof of **Graph Minors X, (10.3)** (page 182):
the set `Hᵢ` of homes for `𝒯ᵢ` is non-empty. -/
theorem theorem_10_3_claim_3_nonempty [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {θ : ℕ} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    ∃ t₀ : ι, IsHome T τ 𝒯 t₀ := by
  let R : ι → ι → Prop := fun x y ↦
    ∀ u v : ι, T.Adj u v →
      (∀ t : ι, (T.deleteEdges {s(u, v)}).Reachable v t →
        (T.deleteEdges {s(x, y)}).Reachable y t) →
      (treeDecompSide T τ s(u, v) u, treeDecompSide T τ s(u, v) v) ∉ 𝒯
  have hR : ∀ ⦃x y : ι⦄, T.Adj x y → R x y ∨ R y x := by
    intro x y hxy
    by_contra! hnot
    dsimp only [R] at hnot
    push Not at hnot
    rcases hnot with ⟨⟨u, v, huv, hsub1, hm1⟩, ⟨u', v', huv', hsub2, hm2⟩⟩
    obtain ⟨t, hvt, hv't⟩ := theorem_10_3_claim_3_heads_inter hTD h𝒯 huv huv' hm1 hm2
    have hyt : (T.deleteEdges {s(x, y)}).Reachable y t := hsub1 t hvt
    have hxt : (T.deleteEdges {s(x, y)}).Reachable x t := by
      simpa [Sym2.eq_swap] using hsub2 t hv't
    exact not_reachable_deleteEdges hTD.isTree hxy (hxt.trans hyt.symm)
  obtain ⟨t₀, ht₀⟩ := exists_sink_of_adj_or hTD.isTree hR
  refine ⟨t₀, fun u v huv hut₀ ↦ ?_⟩
  obtain ⟨p, hp, _⟩ := hTD.isTree.existsUnique_path t₀ v
  cases p with
  | nil =>
    exfalso
    exact not_reachable_deleteEdges hTD.isTree huv hut₀
  | @cons _ w _ htw q =>
    refine ht₀ w htw u v huv fun t hvt ↦ ?_
    have hnot_ut : ¬ (T.deleteEdges {s(u, v)}).Reachable u t :=
      fun hut ↦ not_reachable_deleteEdges hTD.isTree huv (hut.trans hvt.symm)
    have hnot_t₀t : ¬ (T.deleteEdges {s(u, v)}).Reachable t₀ t :=
      fun ht₀t ↦ hnot_ut (hut₀.trans ht₀t)
    have h_edge : s(t₀, w) ∈ (Walk.cons htw q).edges := by simp
    have h_uv_mem : s(u, v) ∈ (Walk.cons htw q).edges :=
      (edge_mem_path_iff_not_reachable_deleteEdges hTD.isTree (Walk.cons htw q) hp).2
        (fun ht₀v ↦ not_reachable_deleteEdges hTD.isTree huv (hut₀.trans ht₀v))
    by_cases heq : s(u, v) = s(t₀, w)
    · rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hvt
      · exfalso
        exact not_reachable_deleteEdges hTD.isTree huv hut₀
    · have hadj_uv_in_tw : (T.deleteEdges {s(t₀, w)}).Adj u v :=
        deleteEdges_adj.mpr ⟨huv, heq⟩
      have hvt_in_tw : (T.deleteEdges {s(t₀, w)}).Reachable v t :=
        reachable_deleteEdges_of_not_reachable hvt (fun hvt₀ ↦
          not_reachable_deleteEdges hTD.isTree huv (hut₀.trans hvt₀.symm))
      rw [Walk.cons_isPath_iff] at hp
      have h_wv_in_tw : (T.deleteEdges {s(t₀, w)}).Reachable w v :=
        reachable_deleteEdges_of_notMem_support q hp.2
      exact h_wv_in_tw.trans hvt_in_tw

/-- Second part of Claim (3) in the proof of **Graph Minors X, (10.3)** (page 182):
the set `Hᵢ` of homes for `𝒯ᵢ` is the vertex set of a subtree of `T` (closed under `OnTreePath`). -/
theorem theorem_10_3_claim_3_subtree [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {t₁ t₂ t : ι} (h1 : IsHome T τ 𝒯 t₁) (h2 : IsHome T τ 𝒯 t₂)
    (hon : OnTreePath T t₁ t₂ t) :
    IsHome T τ 𝒯 t := by
  classical
  intro u v hadj hut
  by_cases hut₁ : (T.deleteEdges {s(u, v)}).Reachable u t₁
  · exact h1 hadj hut₁
  · by_cases hut₂ : (T.deleteEdges {s(u, v)}).Reachable u t₂
    · exact h2 hadj hut₂
    · exfalso
      have hvt₁ : (T.deleteEdges {s(u, v)}).Reachable v t₁ :=
        (reachable_deleteEdges_or hTD.isTree.connected t₁).resolve_left hut₁
      have hvt₂ : (T.deleteEdges {s(u, v)}).Reachable v t₂ :=
        (reachable_deleteEdges_or hTD.isTree.connected t₂).resolve_left hut₂
      obtain ⟨p, hp, _⟩ := hTD.isTree.existsUnique_path t₁ t₂
      have hnot_e : s(u, v) ∉ p.edges := by
        rw [edge_mem_path_iff_not_reachable_deleteEdges hTD.isTree p hp, not_not]
        exact hvt₁.symm.trans hvt₂
      have ht_mem : t ∈ p.support := hon p hp
      have hp₁ : (p.takeUntil t ht_mem).IsPath := hp.takeUntil ht_mem
      have hnot_e₁ : s(u, v) ∉ (p.takeUntil t ht_mem).edges :=
        fun hm ↦ hnot_e (Walk.edges_takeUntil_subset_edges p ht_mem hm)
      have ht₁t : (T.deleteEdges {s(u, v)}).Reachable t₁ t :=
        reachable_deleteEdges_of_notMem_edges (p.takeUntil t ht_mem) hnot_e₁
      exact hut₁ (hut.trans ht₁t.symm)

/-- Claim (4) in the proof of **Graph Minors X, (10.3)** (page 183):
"If $e \in E(T)$ has ends $x, y \in V(T)$, and $x \in H_i$, $y \notin H_i$, then $e$ is
$i$-relevant" (and
directed from `y` to `x`). -/
theorem theorem_10_3_claim_4 [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β}
    {θ : ℕ} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {x y : ι} (hadj : T.Adj x y) (hx : IsHome T τ 𝒯 x) (hy : ¬ IsHome T τ 𝒯 y) :
    (treeDecompSide T τ s(x, y) y, treeDecompSide T τ s(x, y) x) ∈ 𝒯 ∧
      IsRelevantEdge T τ θ s(x, y) := by
  unfold IsHome at hy
  push Not at hy
  obtain ⟨u, v, huv, huy, hm⟩ := hy
  have hnot_ux : ¬ (T.deleteEdges {s(u, v)}).Reachable u x :=
    fun hux ↦ hx huv hux hm
  have heq : s(u, v) = s(x, y) := by
    by_contra hne
    have hadj_xy : (T.deleteEdges {s(u, v)}).Adj y x :=
      deleteEdges_adj.mpr ⟨hadj.symm, fun h ↦ hne (h.symm.trans Sym2.eq_swap)⟩
    exact hnot_ux (huy.trans hadj_xy.reachable)
  rcases Sym2.eq_iff.1 heq.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hnot_ux (Reachable.refl _)).elim
  · have hm' : (treeDecompSide T τ s(x, y) y, treeDecompSide T τ s(x, y) x) ∈ 𝒯 := by
      simpa [Sym2.eq_swap] using hm
    refine ⟨hm', x, y, hadj, rfl, ?_⟩
    rw [separationOrder_comm]
    exact h𝒯.order_lt hm'

/-- Claim (5) in the proof of **Graph Minors X, (10.3)** (page 183):
"For $1 \le i, j \le n$, and $e \in E(T)$, $e$ makes a separation which distinguishes
$\mathscr{T}_i$ from $\mathscr{T}_j$ if and only if $e$ lies on the (unique) minimal path of
$T$ between $V(H_i)$ and $V(H_j)$ and is $i$- and $j$-relevant."
Here `tᵢ ∈ Hᵢ` and `tⱼ ∈ Hⱼ` are any homes for `𝒯ᵢ` and `𝒯ⱼ`. -/
theorem theorem_10_3_claim_5 [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    {θ₁ θ₂ : ℕ} {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯₁ : IsTangle G θ₁ 𝒯₁) (h𝒯₂ : IsTangle G θ₂ 𝒯₂)
    {t₁ t₂ : ι} (ht₁ : IsHome T τ 𝒯₁ t₁) (ht₂ : IsHome T τ 𝒯₂ t₂)
    {e : Sym2 ι} (he : e ∈ T.edgeSet) :
    (∃ A B : Hypergraph α β, MakesSeparation T τ e A B ∧ Distinguishes 𝒯₁ 𝒯₂ A B) ↔
      (∀ p : T.Walk t₁ t₂, p.IsPath → e ∈ p.edges) ∧
      IsRelevantEdge T τ θ₁ e ∧ IsRelevantEdge T τ θ₂ e := by
  induction e using Sym2.ind with | _ u v =>
  have hadj : T.Adj u v := he
  constructor
  · rintro ⟨A, B, ⟨u', v', hadj', heq, rfl, rfl⟩, hA₁, hB₂⟩
    have hord₁ : separationOrder (treeDecompSide T τ s(u', v') u')
        (treeDecompSide T τ s(u', v') v') < θ₁ := h𝒯₁.order_lt hA₁
    have hord₂ : separationOrder (treeDecompSide T τ s(u', v') u')
        (treeDecompSide T τ s(u', v') v') < θ₂ := by
      rw [separationOrder_comm]
      exact h𝒯₂.order_lt hB₂
    have hnot_u't₁ : ¬ (T.deleteEdges {s(u', v')}).Reachable u' t₁ :=
      fun hr ↦ ht₁ hadj' hr hA₁
    have hv't₁ : (T.deleteEdges {s(u', v')}).Reachable v' t₁ :=
      (reachable_deleteEdges_or hTD.isTree.connected t₁).resolve_left hnot_u't₁
    have hnot_v't₂ : ¬ (T.deleteEdges {s(u', v')}).Reachable v' t₂ := by
      intro hr
      have := ht₂ hadj'.symm (by simpa [Sym2.eq_swap] using hr)
      exact this (by simpa [Sym2.eq_swap] using hB₂)
    have hu't₂ : (T.deleteEdges {s(u', v')}).Reachable u' t₂ :=
      (reachable_deleteEdges_or hTD.isTree.connected t₂).resolve_right hnot_v't₂
    have hnr : ¬ (T.deleteEdges {s(u, v)}).Reachable t₁ t₂ := by
      rw [heq]
      intro hr
      exact not_reachable_deleteEdges hTD.isTree hadj' (hu't₂.trans (hr.symm.trans hv't₁.symm))
    refine ⟨fun p hp ↦ (edge_mem_path_iff_not_reachable_deleteEdges hTD.isTree p hp).2 hnr,
      ⟨u', v', hadj', heq, hord₁⟩, ⟨u', v', hadj', heq, hord₂⟩⟩
  · rintro ⟨hpath, hrel₁, hrel₂⟩
    obtain ⟨p₀, hp₀, _⟩ := hTD.isTree.existsUnique_path t₁ t₂
    have hnr : ¬ (T.deleteEdges {s(u, v)}).Reachable t₁ t₂ :=
      (edge_mem_path_iff_not_reachable_deleteEdges hTD.isTree p₀ hp₀).1 (hpath p₀ hp₀)
    have hmk_uv : MakesSeparation T τ s(u, v)
        (treeDecompSide T τ s(u, v) u) (treeDecompSide T τ s(u, v) v) :=
      ⟨u, v, hadj, rfl, rfl, rfl⟩
    have hord₁ : separationOrder (treeDecompSide T τ s(u, v) u)
        (treeDecompSide T τ s(u, v) v) < θ₁ :=
      hrel₁.order_lt_of_makesSeparation hmk_uv
    have hord₂ : separationOrder (treeDecompSide T τ s(u, v) u)
        (treeDecompSide T τ s(u, v) v) < θ₂ :=
      hrel₂.order_lt_of_makesSeparation hmk_uv
    rcases (not_reachable_deleteEdges_iff_sides hTD.isTree hadj).1 hnr with
      ⟨hut₁, hvt₂⟩ | ⟨hvt₁, hut₂⟩
    · have h1 : (treeDecompSide T τ s(u, v) v, treeDecompSide T τ s(u, v) u) ∈ 𝒯₁ :=
        (theorem_10_3_claim_2 hTD h𝒯₁ t₁).1 ht₁ hadj hord₁ hut₁
      have h2 : (treeDecompSide T τ s(u, v) u, treeDecompSide T τ s(u, v) v) ∈ 𝒯₂ := by
        have := (theorem_10_3_claim_2 hTD h𝒯₂ t₂).1 ht₂ hadj.symm
          (by simpa [Sym2.eq_swap, separationOrder_comm] using hord₂)
          (by simpa [Sym2.eq_swap] using hvt₂)
        simpa [Sym2.eq_swap] using this
      exact ⟨treeDecompSide T τ s(u, v) v, treeDecompSide T τ s(u, v) u,
        makesSeparation_symm.1 hmk_uv, h1, h2⟩
    · have h1 : (treeDecompSide T τ s(u, v) u, treeDecompSide T τ s(u, v) v) ∈ 𝒯₁ := by
        have := (theorem_10_3_claim_2 hTD h𝒯₁ t₁).1 ht₁ hadj.symm
          (by simpa [Sym2.eq_swap, separationOrder_comm] using hord₁)
          (by simpa [Sym2.eq_swap] using hvt₁)
        simpa [Sym2.eq_swap] using this
      have h2 : (treeDecompSide T τ s(u, v) v, treeDecompSide T τ s(u, v) u) ∈ 𝒯₂ :=
        (theorem_10_3_claim_2 hTD h𝒯₂ t₂).1 ht₂ hadj hord₂ hut₂
      exact ⟨treeDecompSide T τ s(u, v) u, treeDecompSide T τ s(u, v) v,
        hmk_uv, h1, h2⟩

/-- Claim (6) in the proof of **Graph Minors X, (10.3)** (page 183):
"For `1 ≤ i ≤ n`, `|Hᵢ| = 1`" (every home for `𝒯ᵢ` equals any other home for `𝒯ᵢ`). -/
theorem theorem_10_3_claim_6 [Fintype ι] [LinearOrder Λ] {n : ℕ} {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hTB : IsTieBreaker G lam)
    {θ : Fin n → ℕ} {𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : ∀ i, IsTangle G (θ i) (𝒯 i))
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    (hex_edge : ∀ i j : Fin n, i ≠ j →
      ∃ e ∈ T.edgeSet, ∃ A B, MakesSeparation T τ e A B ∧ IsDistinction lam (𝒯 i) (𝒯 j) A B)
    (hevery_edge : ∀ e ∈ T.edgeSet,
      ∃ i j : Fin n, i ≠ j ∧ ∃ A B, MakesSeparation T τ e A B ∧ IsDistinction lam (𝒯 i) (𝒯 j) A B)
    (i : Fin n) {t₁ t₂ : ι} (ht₁ : IsHome T τ (𝒯 i) t₁) (ht₂ : IsHome T τ (𝒯 i) t₂) :
    t₁ = t₂ := by
  classical
  by_contra hne
  obtain ⟨q, hq, _⟩ := hTD.isTree.existsUnique_path t₁ t₂
  cases q with
  | nil => exact hne rfl
  | @cons _ w _ hadj_t₁w q' =>
    have hw_home : IsHome T τ (𝒯 i) w := by
      refine theorem_10_3_claim_3_subtree hTD ht₁ ht₂ fun p hp ↦ ?_
      obtain ⟨_, _, huniq⟩ := hTD.isTree.existsUnique_path t₁ t₂
      have hpq : p = Walk.cons hadj_t₁w q' :=
        (huniq p hp).trans (huniq (Walk.cons hadj_t₁w q') hq).symm
      rw [hpq]
      simp [Walk.start_mem_support]
    let e : Sym2 ι := s(t₁, w)
    have he_mem : e ∈ T.edgeSet := hadj_t₁w
    have hnot_rel_i : ¬ IsRelevantEdge T τ (θ i) e := by
      intro hrel
      have hmk : MakesSeparation T τ e
          (treeDecompSide T τ s(t₁, w) t₁) (treeDecompSide T τ s(t₁, w) w) :=
        ⟨t₁, w, hadj_t₁w, rfl, rfl, rfl⟩
      have hord := hrel.order_lt_of_makesSeparation hmk
      have hsep := hTD.isSeparation_treeDecompSide hadj_t₁w
      rcases (h𝒯 i).axiom1 hsep hord with hm | hm
      · exact ht₁ hadj_t₁w (Reachable.refl _) hm
      · have hw' := hw_home hadj_t₁w.symm (Reachable.refl _)
        exact hw' (by simpa [Sym2.eq_swap] using hm)
    obtain ⟨j, k, hjk, A_jk, B_jk, hmk_jk, hdist_jk⟩ := hevery_edge e he_mem
    obtain ⟨t_j, htj⟩ := theorem_10_3_claim_3_nonempty hTD (h𝒯 j)
    obtain ⟨t_k, htk⟩ := theorem_10_3_claim_3_nonempty hTD (h𝒯 k)
    obtain ⟨P, hP, _⟩ := hTD.isTree.existsUnique_path t_j t_k
    have he_claim5 := (theorem_10_3_claim_5 hTD (h𝒯 j) (h𝒯 k) htj htk he_mem).1
      ⟨A_jk, B_jk, hmk_jk, hdist_jk.1⟩
    have he_in_P : e ∈ P.edges := he_claim5.1 P hP
    have hji : j ≠ i := by rintro rfl; exact hnot_rel_i he_claim5.2.1
    have ht₁_in_P : t₁ ∈ P.support := Walk.fst_mem_support_of_mem_edges P he_in_P
    obtain ⟨f, hf_mem, A_ji, B_ji, hmk_ji, hdist_ji⟩ := hex_edge j i hji
    have hf_claim5 := (theorem_10_3_claim_5 hTD (h𝒯 j) (h𝒯 i) htj ht₁ hf_mem).1
      ⟨A_ji, B_ji, hmk_ji, hdist_ji.1⟩
    have hf_in_P₁ : f ∈ (P.takeUntil t₁ ht₁_in_P).edges :=
      hf_claim5.1 (P.takeUntil t₁ ht₁_in_P) (hP.takeUntil ht₁_in_P)
    have hf_in_P : f ∈ P.edges := Walk.edges_takeUntil_subset_edges P ht₁_in_P hf_in_P₁
    have hord_f_lt_i : separationOrder A_ji B_ji < θ i := by
      rw [separationOrder_comm]
      exact (h𝒯 i).order_lt hdist_ji.1.2
    have hord_e_ge_i : θ i ≤ separationOrder A_jk B_jk := by
      by_contra! hlt
      obtain ⟨u, v, hadj, heq, rfl, rfl⟩ := hmk_jk
      exact hnot_rel_i ⟨u, v, hadj, heq, hlt⟩
    have hord_f_lt_e : separationOrder A_ji B_ji < separationOrder A_jk B_jk :=
      hord_f_lt_i.trans_le hord_e_ge_i
    have hord_e_lt_k : separationOrder A_jk B_jk < θ k := by
      rw [separationOrder_comm]
      exact (h𝒯 k).order_lt hdist_jk.1.2
    have hf_rel_k : IsRelevantEdge T τ (θ k) f := by
      obtain ⟨u, v, hadj, heq, rfl, rfl⟩ := hmk_ji
      exact ⟨u, v, hadj, heq, hord_f_lt_e.trans hord_e_lt_k⟩
    have hf_for_jk : ∃ C D, MakesSeparation T τ f C D ∧ Distinguishes (𝒯 j) (𝒯 k) C D := by
      refine (theorem_10_3_claim_5 hTD (h𝒯 j) (h𝒯 k) htj htk hf_mem).2
        ⟨fun p hp ↦ ?_, hf_claim5.2.1, hf_rel_k⟩
      obtain ⟨_, _, huniq⟩ := hTD.isTree.existsUnique_path t_j t_k
      have hpP : p = P := (huniq p hp).trans (huniq P hP).symm
      exact hpP ▸ hf_in_P
    obtain ⟨C, D, hmk_CD, hCD_dist⟩ := hf_for_jk
    have hord_CD : separationOrder C D = separationOrder A_ji B_ji := by
      obtain ⟨u, v, _, heq, rfl, rfl⟩ := hmk_CD
      obtain ⟨u', v', _, heq', rfl, rfl⟩ := hmk_ji
      rcases Sym2.eq_iff.1 (heq.symm.trans heq') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · simp [Sym2.eq_swap, separationOrder_comm]
    have hlam_lt : lam (C, D) < lam (A_jk, B_jk) :=
      hTB.axiom3 (hmk_CD.isSeparation hTD) (hmk_jk.isSeparation hTD)
        (hord_CD.trans_lt hord_f_lt_e)
    exact not_lt_of_ge (hdist_jk.2 hCD_dist) hlam_lt

/-- Claim (7) in the proof of **Graph Minors X, (10.3)** (pages 183–184):
"`H₁ ∪ … ∪ Hₙ = V(T)`" (every vertex of `T` is a home for `𝒯ᵢ` for some `i`). -/
theorem theorem_10_3_claim_7 [Fintype ι] [LinearOrder Λ] {n : ℕ} (hn : 1 ≤ n)
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ} (hTB : IsTieBreaker G lam)
    {θ : Fin n → ℕ} {𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : ∀ i, IsTangle G (θ i) (𝒯 i))
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (hTD : IsTreeDecomposition G T τ)
    (huniq_edge : ∀ i j : Fin n, i ≠ j → ∀ A B : Hypergraph α β,
      IsDistinction lam (𝒯 i) (𝒯 j) A B →
      ∃! e : Sym2 ι, e ∈ T.edgeSet ∧ MakesSeparation T τ e A B)
    (hevery_edge : ∀ e ∈ T.edgeSet,
      ∃ i j : Fin n, i ≠ j ∧ ∃ A B, MakesSeparation T τ e A B ∧ IsDistinction lam (𝒯 i) (𝒯 j) A B)
    (t₀ : ι) :
    ∃ i : Fin n, IsHome T τ (𝒯 i) t₀ := by
  classical
  by_contra! hno_home
  let i₀ : Fin n := ⟨0, hn⟩
  obtain ⟨t_home₀, hth₀⟩ := theorem_10_3_claim_3_nonempty hTD (h𝒯 i₀)
  have ht₀_ne : t₀ ≠ t_home₀ := fun h ↦ hno_home i₀ (h ▸ hth₀)
  obtain ⟨q₀, hq₀, _⟩ := hTD.isTree.existsUnique_path t₀ t_home₀
  have hN_ne : (Finset.univ.filter fun u : ι ↦ T.Adj t₀ u).Nonempty := by
    cases q₀ with
    | nil => exact (ht₀_ne rfl).elim
    | @cons _ u _ hadj _ =>
      exact ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ u, hadj⟩⟩
  let val (u : ι) : Λ :=
    lam (treeDecompSide T τ s(t₀, u) t₀, treeDecompSide T τ s(t₀, u) u)
  obtain ⟨u₁, hu₁_mem, hmax⟩ :=
    (Finset.univ.filter fun u : ι ↦ T.Adj t₀ u).exists_max_image val hN_ne
  have hadj₁ : T.Adj t₀ u₁ := (Finset.mem_filter.1 hu₁_mem).2
  let e₁ : Sym2 ι := s(t₀, u₁)
  have he₁_mem : e₁ ∈ T.edgeSet := hadj₁
  obtain ⟨i, j, hij, A_ij, B_ij, hmk_ij, hdist_ij⟩ := hevery_edge e₁ he₁_mem
  have hval_u₁ : val u₁ = lam (A_ij, B_ij) := by
    obtain ⟨x, y, hadj_xy, heq, rfl, rfl⟩ := hmk_ij
    rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · simpa [val, Sym2.eq_swap] using (hTB.lam_swap (hTD.isSeparation_treeDecompSide hadj₁)).symm
  obtain ⟨t_i, hti⟩ := theorem_10_3_claim_3_nonempty hTD (h𝒯 i)
  obtain ⟨t_j, htj⟩ := theorem_10_3_claim_3_nonempty hTD (h𝒯 j)
  obtain ⟨P, hP, _⟩ := hTD.isTree.existsUnique_path t_i t_j
  have he₁_claim5 := (theorem_10_3_claim_5 hTD (h𝒯 i) (h𝒯 j) hti htj he₁_mem).1
    ⟨A_ij, B_ij, hmk_ij, hdist_ij.1⟩
  have he₁_in_P : e₁ ∈ P.edges := he₁_claim5.1 P hP
  have ht₀_in_P : t₀ ∈ P.support := Walk.fst_mem_support_of_mem_edges P he₁_in_P
  have ht₀_ne_i : t₀ ≠ t_i := fun h ↦ hno_home i (h ▸ hti)
  have ht₀_ne_j : t₀ ≠ t_j := fun h ↦ hno_home j (h ▸ htj)
  let P₁ := P.takeUntil t₀ ht₀_in_P
  let P₂ := P.dropUntil t₀ ht₀_in_P
  have hP_eq : P₁.append P₂ = P := Walk.take_spec P ht₀_in_P
  have hnodup_edges : (P₁.edges ++ P₂.edges).Nodup := by
    rw [← Walk.edges_append, hP_eq]
    exact hP.edges_nodup
  have hex_P₁ : ∃ w₁ : ι, T.Adj t₀ w₁ ∧ s(t₀, w₁) ∈ P₁.edges := by
    generalize hr : P₁.reverse = R₁
    cases R₁ with
    | nil =>
      exact (ht₀_ne_i rfl).elim
    | @cons _ w₁ _ hadj_w₁ r' =>
      refine ⟨w₁, hadj_w₁, ?_⟩
      have hmem : s(t₀, w₁) ∈ P₁.reverse.edges := by simp [hr]
      rwa [Walk.edges_reverse, List.mem_reverse] at hmem
  have hex_P₂ : ∃ w₂ : ι, T.Adj t₀ w₂ ∧ s(t₀, w₂) ∈ P₂.edges := by
    cases P₂ with
    | nil =>
      exact (ht₀_ne_j rfl).elim
    | @cons _ w₂ _ hadj_w₂ r' =>
      exact ⟨w₂, hadj_w₂, by simp⟩
  obtain ⟨w₁, hadj_w₁, hw₁_mem⟩ := hex_P₁
  obtain ⟨w₂, hadj_w₂, hw₂_mem⟩ := hex_P₂
  have hw₁_ne_w₂ : s(t₀, w₁) ≠ s(t₀, w₂) := by
    intro heq
    exact List.disjoint_of_nodup_append hnodup_edges hw₁_mem (heq ▸ hw₂_mem)
  have hex_u₂ : ∃ u₂ : ι, T.Adj t₀ u₂ ∧ s(t₀, u₂) ≠ e₁ ∧ s(t₀, u₂) ∈ P.edges := by
    rw [← hP_eq, Walk.edges_append]
    by_cases h1 : s(t₀, w₁) = e₁
    · refine ⟨w₂, hadj_w₂, ?_, List.mem_append_right _ hw₂_mem⟩
      rw [← h1]
      exact Ne.symm hw₁_ne_w₂
    · exact ⟨w₁, hadj_w₁, h1, List.mem_append_left _ hw₁_mem⟩
  obtain ⟨u₂, hadj₂, he₂_ne, he₂_in_P⟩ := hex_u₂
  let e₂ : Sym2 ι := s(t₀, u₂)
  have he₂_mem : e₂ ∈ T.edgeSet := hadj₂
  have hval_le : val u₂ ≤ val u₁ :=
    hmax u₂ (Finset.mem_filter.2 ⟨Finset.mem_univ u₂, hadj₂⟩)
  let A₂ := treeDecompSide T τ s(t₀, u₂) t₀
  let B₂ := treeDecompSide T τ s(t₀, u₂) u₂
  have hmk₂ : MakesSeparation T τ e₂ A₂ B₂ := ⟨t₀, u₂, hadj₂, rfl, rfl, rfl⟩
  have hval_ne : val u₂ ≠ val u₁ := by
    intro heq
    rw [hval_u₁] at heq
    have hsep₂ := hTD.isSeparation_treeDecompSide hadj₂
    have hsep_ij := hmk_ij.isSeparation hTD
    rcases (hTB.axiom1 hsep₂ hsep_ij).1 heq with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · obtain ⟨_, _, huniq⟩ := huniq_edge i j hij A_ij B_ij hdist_ij
      have h1 : e₂ = e₁ := (huniq e₂ ⟨he₂_mem, hA ▸ hB ▸ hmk₂⟩).trans
        (huniq e₁ ⟨he₁_mem, hmk_ij⟩).symm
      exact he₂_ne h1
    · obtain ⟨_, _, huniq⟩ := huniq_edge i j hij A_ij B_ij hdist_ij
      have hmk₂' : MakesSeparation T τ e₂ A_ij B_ij :=
        makesSeparation_symm.1 (hA ▸ hB ▸ hmk₂)
      have h1 : e₂ = e₁ := (huniq e₂ ⟨he₂_mem, hmk₂'⟩).trans
        (huniq e₁ ⟨he₁_mem, hmk_ij⟩).symm
      exact he₂_ne h1
  have hval_lt : lam (A₂, B₂) < lam (A_ij, B_ij) := by
    rw [← hval_u₁]
    exact lt_of_le_of_ne hval_le hval_ne
  have hord₂_le : separationOrder A₂ B₂ ≤ separationOrder A_ij B_ij := by
    by_contra! hgt
    exact not_lt_of_ge hval_lt.le
      (hTB.axiom3 (hmk_ij.isSeparation hTD) (hmk₂.isSeparation hTD) hgt)
  have hord_ij_i : separationOrder A_ij B_ij < θ i := (h𝒯 i).order_lt hdist_ij.1.1
  have hord_ij_j : separationOrder A_ij B_ij < θ j := by
    rw [separationOrder_comm]
    exact (h𝒯 j).order_lt hdist_ij.1.2
  have he₂_rel_i : IsRelevantEdge T τ (θ i) e₂ :=
    ⟨t₀, u₂, hadj₂, rfl, hord₂_le.trans_lt hord_ij_i⟩
  have he₂_rel_j : IsRelevantEdge T τ (θ j) e₂ :=
    ⟨t₀, u₂, hadj₂, rfl, hord₂_le.trans_lt hord_ij_j⟩
  have he₂_dist : ∃ C D, MakesSeparation T τ e₂ C D ∧ Distinguishes (𝒯 i) (𝒯 j) C D := by
    refine (theorem_10_3_claim_5 hTD (h𝒯 i) (h𝒯 j) hti htj he₂_mem).2
      ⟨fun p hp ↦ ?_, he₂_rel_i, he₂_rel_j⟩
    obtain ⟨_, _, huniq⟩ := hTD.isTree.existsUnique_path t_i t_j
    have hpP : p = P := (huniq p hp).trans (huniq P hP).symm
    exact hpP ▸ he₂_in_P
  obtain ⟨C, D, hmk_CD, hCD_dist⟩ := he₂_dist
  have hlam_CD : lam (C, D) = lam (A₂, B₂) := by
    obtain ⟨x, y, hadj_xy, heq, rfl, rfl⟩ := hmk_CD
    rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · simpa [A₂, B₂, Sym2.eq_swap] using hTB.lam_swap (hTD.isSeparation_treeDecompSide hadj₂)
  exact not_lt_of_ge (hdist_ij.2 hCD_dist) (hlam_CD ▸ hval_lt)

/-- Relabelling a tree-decomposition along `e : ι ≃ ι'` preserves `treeDecompSide`. -/
theorem treeDecompSide_map [Fintype ι] {ι' : Type*} [Fintype ι']
    (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (e : ι ≃ ι') (u v w : ι) :
    treeDecompSide (T.map e.toEmbedding) (τ ∘ e.symm) s(e u, e v) (e w) =
      treeDecompSide T τ s(u, v) w := by
  classical
  let φ : (T.deleteEdges {s(u, v)}) ≃g
      ((T.map e.toEmbedding).deleteEdges {s(e u, e v)}) :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
        refine and_congr (SimpleGraph.Iso.map e T).map_rel_iff (not_congr ?_)
        change Sym2.map e s(x, y) = Sym2.map e s(u, v) ↔ s(x, y) = s(u, v)
        exact (Sym2.map.injective e.injective).eq_iff }
  have hreach : ∀ t : ι,
      ((T.map e.toEmbedding).deleteEdges {s(e u, e v)}).Reachable (e w) (e t) ↔
        (T.deleteEdges {s(u, v)}).Reachable w t :=
    fun t ↦ ⟨fun ⟨p⟩ ↦ ⟨(p.map φ.symm.toHom).copy (e.symm_apply_apply _) (e.symm_apply_apply _)⟩,
      fun ⟨p⟩ ↦ ⟨p.map φ.toHom⟩⟩
  ext x <;>
    simp only [treeDecompSide, biUnion, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.comp_apply]
  · refine ⟨?_, fun ⟨t, hr, hx⟩ ↦ ⟨e t, (hreach t).2 hr, by simpa using hx⟩⟩
    rintro ⟨t', hr', hx'⟩
    obtain ⟨t, rfl⟩ := e.surjective t'
    exact ⟨t, (hreach t).1 hr', by simpa using hx'⟩
  · refine ⟨?_, fun ⟨t, hr, hx⟩ ↦ ⟨e t, (hreach t).2 hr, by simpa using hx⟩⟩
    rintro ⟨t', hr', hx'⟩
    obtain ⟨t, rfl⟩ := e.surjective t'
    exact ⟨t, (hreach t).1 hr', by simpa using hx'⟩
  · refine ⟨?_, fun ⟨t, hr, hx⟩ ↦ ⟨e t, (hreach t).2 hr, by simpa using hx⟩⟩
    rintro ⟨t', hr', hx'⟩
    obtain ⟨t, rfl⟩ := e.surjective t'
    exact ⟨t, (hreach t).1 hr', by simpa using hx'⟩

/-- Relabelling a tree-decomposition along `e : ι ≃ ι'` preserves `MakesSeparation`. -/
theorem makesSeparation_map [Fintype ι] {ι' : Type*} [Fintype ι']
    (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (e : ι ≃ ι') (f : Sym2 ι)
    (A B : Hypergraph α β) :
    MakesSeparation (T.map e.toEmbedding) (τ ∘ e.symm) (f.map e) A B ↔
      MakesSeparation T τ f A B := by
  constructor
  · rintro ⟨u', v', hadj', heq', rfl, rfl⟩
    obtain ⟨u, rfl⟩ := e.surjective u'
    obtain ⟨v, rfl⟩ := e.surjective v'
    have hadj : T.Adj u v := (SimpleGraph.Iso.map e T).map_rel_iff.1 hadj'
    have heq : f = s(u, v) :=
      Sym2.map.injective e.injective heq'
    refine ⟨u, v, hadj, heq, ?_, ?_⟩
    · exact treeDecompSide_map T τ e u v u
    · exact treeDecompSide_map T τ e u v v
  · rintro ⟨u, v, hadj, rfl, rfl, rfl⟩
    have hadj' : (T.map e.toEmbedding).Adj (e u) (e v) :=
      (SimpleGraph.Iso.map e T).map_rel_iff.2 hadj
    exact ⟨e u, e v, hadj', rfl,
      (treeDecompSide_map T τ e u v u).symm, (treeDecompSide_map T τ e u v v).symm⟩

/-- Relabelling a tree-decomposition along `e : ι ≃ ι'` preserves `IsHome`. -/
theorem isHome_map [Fintype ι] {ι' : Type*} [Fintype ι']
    (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (e : ι ≃ ι')
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (t₀ : ι) :
    IsHome (T.map e.toEmbedding) (τ ∘ e.symm) 𝒯 (e t₀) ↔ IsHome T τ 𝒯 t₀ := by
  constructor
  · intro h u v hadj hut₀
    have hadj' : (T.map e.toEmbedding).Adj (e u) (e v) :=
      (SimpleGraph.Iso.map e T).map_rel_iff.2 hadj
    let φ : (T.deleteEdges {s(u, v)}) ≃g
        ((T.map e.toEmbedding).deleteEdges {s(e u, e v)}) :=
      { toEquiv := e
        map_rel_iff' := by
          intro x y
          simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
          refine and_congr (SimpleGraph.Iso.map e T).map_rel_iff (not_congr ?_)
          change Sym2.map e s(x, y) = Sym2.map e s(u, v) ↔ s(x, y) = s(u, v)
          exact (Sym2.map.injective e.injective).eq_iff }
    have hut₀' : ((T.map e.toEmbedding).deleteEdges {s(e u, e v)}).Reachable (e u) (e t₀) := by
      obtain ⟨p⟩ := hut₀
      exact ⟨p.map φ.toHom⟩
    have := h hadj' hut₀'
    rwa [treeDecompSide_map, treeDecompSide_map] at this
  · intro h u' v' hadj' hut₀'
    obtain ⟨u, rfl⟩ := e.surjective u'
    obtain ⟨v, rfl⟩ := e.surjective v'
    have hadj : T.Adj u v := (SimpleGraph.Iso.map e T).map_rel_iff.1 hadj'
    let φ : (T.deleteEdges {s(u, v)}) ≃g
        ((T.map e.toEmbedding).deleteEdges {s(e u, e v)}) :=
      { toEquiv := e
        map_rel_iff' := by
          intro x y
          simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
          refine and_congr (SimpleGraph.Iso.map e T).map_rel_iff (not_congr ?_)
          change Sym2.map e s(x, y) = Sym2.map e s(u, v) ↔ s(x, y) = s(u, v)
          exact (Sym2.map.injective e.injective).eq_iff }
    have hut₀ : (T.deleteEdges {s(u, v)}).Reachable u t₀ := by
      obtain ⟨p⟩ := hut₀'
      exact ⟨(p.map φ.symm.toHom).copy (e.symm_apply_apply _) (e.symm_apply_apply _)⟩
    rw [treeDecompSide_map, treeDecompSide_map]
    exact h hadj hut₀

/-- **Graph Minors X, (10.3)** (page 181):
"Let $\mathscr{T}_1, \dots, \mathscr{T}_n$ be mutually distinguishable tangles in a
hypergraph $G$ with $n \ge 1$, and let $\lambda$ be a tie-breaker. Then there is a
tree-decomposition $(T, \tau)$ of $G$, where $V(T) = \{t_1, \dots, t_n\}$, with the
following properties:* (i) *For every $e \in E(T)$ and for $1 \le i \le n$, if $T_1, T_2$
are the components of $T \setminus e$ and $t_i \in V(T_1)$ then* $$ \left( \bigcup_{t \in
V(T_1)} \tau(t), \bigcup_{t \in V(T_2)} \tau(t) \right) \notin \mathscr{T}_i. $$ (ii) *For
all $i \ne j$ with $1 \le i, j \le n$, let $e$ be the edge of the path of $T$ between $t_i$
and $t_j$ making separations of smallest $\lambda$-order; then these separations are the
$(\mathscr{T}_i, \mathscr{T}_j)$- and $(\mathscr{T}_j, \mathscr{T}_i)$-distinctions." -/
theorem theorem_10_3_proof [LinearOrder Λ] {n : ℕ}
    (G : Hypergraph α β) (lam : Hypergraph α β × Hypergraph α β → Λ)
    (θ : Fin n → ℕ) (𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β))
    (hn : 1 ≤ n)
    (hTB : IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, IsTangle G (θ i) (𝒯 i))
    (hdist : ∀ i j : Fin n, i ≠ j → AreDistinguishable (𝒯 i) (𝒯 j)) :
    ∃ (T : SimpleGraph (Fin n)) (τ : Fin n → Hypergraph α β),
      IsStandardTreeDecomposition G lam 𝒯 T τ := by
  classical
  let 𝒮 : Set (Hypergraph α β × Hypergraph α β) :=
    {p | ∃ i j : Fin n, i ≠ j ∧ IsDistinction lam (𝒯 i) (𝒯 j) p.1 p.2}
  have hsep : ∀ p ∈ 𝒮, G.IsSeparation p.1 p.2 := by
    rintro ⟨A, B⟩ ⟨i, _, _, h⟩
    exact (h𝒯 i).isSeparation h.1.1
  have hlam : IsLaminar 𝒮 := by
    rintro ⟨A₁, B₁⟩ ⟨i₁, j₁, _, hd₁⟩ ⟨A₂, B₂⟩ ⟨i₂, j₂, _, hd₂⟩
    exact theorem_9_4_proof hTB
      (theorem_10_2_proof G lam (θ i₁) (θ j₁) (𝒯 i₁) (𝒯 j₁) A₁ B₁ hTB (h𝒯 i₁) (h𝒯 j₁) hd₁)
      (theorem_10_2_proof G lam (θ i₂) (θ j₂) (𝒯 i₂) (𝒯 j₂) A₂ B₂ hTB (h𝒯 i₂) (h𝒯 j₂) hd₂)
  obtain ⟨ι, hfin_ι, T, τ, hTD, huniq_S, hevery_S, _⟩ :=
    theorem_9_1_exists_treeDecomposition hsep hlam
  have hex_dist : ∀ i j : Fin n, i ≠ j →
      ∃ A B : Hypergraph α β, IsDistinction lam (𝒯 i) (𝒯 j) A B :=
    fun i j hij ↦ (exists_isDistinction_iff (h𝒯 i) (h𝒯 j)).2 (hdist i j hij)
  have hex_edge : ∀ i j : Fin n, i ≠ j →
      ∃ e ∈ T.edgeSet, ∃ A B, MakesSeparation T τ e A B ∧ IsDistinction lam (𝒯 i) (𝒯 j) A B := by
    intro i j hij
    obtain ⟨A, B, hd⟩ := hex_dist i j hij
    obtain ⟨e, ⟨he, hmk⟩, _⟩ := huniq_S (A, B) ⟨i, j, hij, hd⟩
    exact ⟨e, he, A, B, hmk, hd⟩
  have huniq_edge : ∀ i j : Fin n, i ≠ j → ∀ A B : Hypergraph α β,
      IsDistinction lam (𝒯 i) (𝒯 j) A B →
      ∃! e : Sym2 ι, e ∈ T.edgeSet ∧ MakesSeparation T τ e A B :=
    fun i j hij A B hd ↦ huniq_S (A, B) ⟨i, j, hij, hd⟩
  have hevery_edge : ∀ e ∈ T.edgeSet,
      ∃ i j : Fin n, i ≠ j ∧ ∃ A B, MakesSeparation T τ e A B ∧ IsDistinction lam (𝒯 i) (𝒯 j) A B
        := by
    intro e he
    obtain ⟨⟨A, B⟩, ⟨i, j, hij, hd⟩, hmk⟩ := hevery_S e he
    exact ⟨i, j, hij, A, B, hmk, hd⟩
  have hex_home : ∀ i : Fin n, ∃ t : ι, IsHome T τ (𝒯 i) t :=
    fun i ↦ theorem_10_3_claim_3_nonempty hTD (h𝒯 i)
  choose home hhome using hex_home
  have hhome_inj : Function.Injective home := by
    intro i j heq
    by_contra hij
    obtain ⟨e, _, A, B, hmk, hd⟩ := hex_edge i j hij
    exact theorem_10_3_claim_1 hTD hmk hd.1 (home i) ⟨hhome i, heq ▸ hhome j⟩
  have hhome_surj : Function.Surjective home := by
    intro t₀
    obtain ⟨i, hi⟩ := theorem_10_3_claim_7 hn hTB h𝒯 hTD huniq_edge hevery_edge t₀
    exact ⟨i, theorem_10_3_claim_6 hTB h𝒯 hTD hex_edge hevery_edge i (hhome i) hi⟩
  let e_equiv : ι ≃ Fin n := (Equiv.ofBijective home ⟨hhome_inj, hhome_surj⟩).symm
  have he_apply : ∀ i : Fin n, e_equiv (home i) = i :=
    fun i ↦ (Equiv.ofBijective home ⟨hhome_inj, hhome_surj⟩).symm_apply_apply i
  let T₀ : SimpleGraph (Fin n) := T.map e_equiv.toEmbedding
  let τ₀ : Fin n → Hypergraph α β := τ ∘ e_equiv.symm
  have hTD₀ : IsTreeDecomposition G T₀ τ₀ := hTD.relabel e_equiv
  refine ⟨T₀, τ₀, ⟨hTD₀, ?_, ?_⟩⟩
  · intro i
    have h1 : IsHome T₀ τ₀ (𝒯 i) (e_equiv (home i)) :=
      (isHome_map T τ e_equiv (𝒯 i) (home i)).2 (hhome i)
    rwa [he_apply i] at h1
  · intro i j hij
    obtain ⟨f, hf_mem, A, B, hmk_f, hd_ij⟩ := hex_edge i j hij
    have hd_ji : IsDistinction lam (𝒯 j) (𝒯 i) B A :=
      (isDistinction_comm hTB (h𝒯 i) (h𝒯 j)).1 hd_ij
    let e₀ : Sym2 (Fin n) := f.map e_equiv
    have he₀_mem : e₀ ∈ T₀.edgeSet := by
      induction f using Sym2.ind with | _ u v =>
      have hadj : T.Adj u v := hf_mem
      exact (SimpleGraph.Iso.map e_equiv T).map_rel_iff.2 hadj
    have hmk_e₀ : MakesSeparation T₀ τ₀ e₀ A B :=
      (makesSeparation_map T τ e_equiv f A B).2 hmk_f
    have hf_claim5 := (theorem_10_3_claim_5 hTD (h𝒯 i) (h𝒯 j) (hhome i) (hhome j) hf_mem).1
      ⟨A, B, hmk_f, hd_ij.1⟩
    have he₀_on_path : ∀ p : T₀.Walk i j, p.IsPath → e₀ ∈ p.edges := by
      intro p hp
      let φ : T ≃g T₀ := mapIso T e_equiv
      have hi' : φ.symm.toHom i = home i := rfl
      have hj' : φ.symm.toHom j = home j := rfl
      let q : T.Walk (home i) (home j) := (p.map φ.symm.toHom).copy hi' hj'
      have hq : q.IsPath := by
        dsimp only [q]
        rw [Walk.isPath_copy]
        exact hp.map φ.symm.injective
      have hf_in_q : f ∈ q.edges := hf_claim5.1 q hq
      dsimp only [q] at hf_in_q
      rw [Walk.edges_copy, Walk.edges_map, List.mem_map] at hf_in_q
      obtain ⟨e', he', heq⟩ := hf_in_q
      have he₀_eq : e₀ = e' := by
        change f.map e_equiv = e'
        rw [← heq]
        induction e' using Sym2.ind with | _ x y =>
        exact Sym2.eq_iff.2 (Or.inl ⟨e_equiv.apply_symm_apply x, e_equiv.apply_symm_apply y⟩)
      exact he₀_eq ▸ he'
    refine ⟨e₀, he₀_mem, he₀_on_path, ?_, A, B, hmk_e₀, hd_ij, hd_ji⟩
    intro e' he'_mem he'_path A₁ B₁ A' B' hmk₁ hmk'
    have hlam₁ : lam (A₁, B₁) = lam (A, B) := by
      obtain ⟨u, v, hadj, heq, rfl, rfl⟩ := hmk_e₀
      obtain ⟨u', v', hadj', heq', rfl, rfl⟩ := hmk₁
      rcases Sym2.eq_iff.1 (heq.symm.trans heq') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · simpa [Sym2.eq_swap] using
          hTB.lam_swap (hTD₀.isSeparation_treeDecompSide hadj)
    rw [hlam₁]
    by_contra! hlt
    obtain ⟨f', rfl⟩ : ∃ f' : Sym2 ι, f'.map e_equiv = e' := by
      induction e' using Sym2.ind with | _ x y =>
      exact ⟨s(e_equiv.symm x, e_equiv.symm y), by simp⟩
    have hf'_mem : f' ∈ T.edgeSet := by
      induction f' using Sym2.ind with | _ u v =>
      have hadj' : T₀.Adj (e_equiv u) (e_equiv v) := he'_mem
      exact (SimpleGraph.Iso.map e_equiv T).map_rel_iff.1 hadj'
    have hmk_f' : MakesSeparation T τ f' A' B' :=
      (makesSeparation_map T τ e_equiv f' A' B').1 hmk'
    have hord'_le : separationOrder A' B' ≤ separationOrder A B := by
      by_contra! hgt
      exact not_lt_of_ge hlt.le
        (hTB.axiom3 (hmk_f.isSeparation hTD) (hmk_f'.isSeparation hTD) hgt)
    have hord_i : separationOrder A B < θ i := (h𝒯 i).order_lt hd_ij.1.1
    have hord_j : separationOrder A B < θ j := by
      rw [separationOrder_comm]
      exact (h𝒯 j).order_lt hd_ij.1.2
    have hf'_rel_i : IsRelevantEdge T τ (θ i) f' := by
      obtain ⟨u, v, hadj, heq, rfl, rfl⟩ := hmk_f'
      exact ⟨u, v, hadj, heq, hord'_le.trans_lt hord_i⟩
    have hf'_rel_j : IsRelevantEdge T τ (θ j) f' := by
      obtain ⟨u, v, hadj, heq, rfl, rfl⟩ := hmk_f'
      exact ⟨u, v, hadj, heq, hord'_le.trans_lt hord_j⟩
    have hf'_on_path : ∀ q : T.Walk (home i) (home j), q.IsPath → f' ∈ q.edges := by
      intro q hq
      let φ : T ≃g T₀ := mapIso T e_equiv
      have hi' : φ.toHom (home i) = i := he_apply i
      have hj' : φ.toHom (home j) = j := he_apply j
      let p : T₀.Walk i j := (q.map φ.toHom).copy hi' hj'
      have hp : p.IsPath := by
        dsimp only [p]
        rw [Walk.isPath_copy]
        exact hq.map φ.injective
      have he'_in_p : f'.map e_equiv ∈ p.edges := he'_path p hp
      dsimp only [p] at he'_in_p
      rw [Walk.edges_copy, Walk.edges_map, List.mem_map] at he'_in_p
      obtain ⟨f'', hf'', heq⟩ := he'_in_p
      have hf'_eq : f'' = f' :=
        Sym2.map.injective e_equiv.injective heq
      exact hf'_eq ▸ hf''
    obtain ⟨C, D, hmk_CD, hCD_dist⟩ :=
      (theorem_10_3_claim_5 hTD (h𝒯 i) (h𝒯 j) (hhome i) (hhome j) hf'_mem).2
        ⟨hf'_on_path, hf'_rel_i, hf'_rel_j⟩
    have hlam_CD : lam (C, D) = lam (A', B') := by
      obtain ⟨u, v, hadj, heq, rfl, rfl⟩ := hmk_CD
      obtain ⟨u', v', _, heq', rfl, rfl⟩ := hmk_f'
      rcases Sym2.eq_iff.1 (heq.symm.trans heq') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · simpa [Sym2.eq_swap] using (hTB.lam_swap (hTD.isSeparation_treeDecompSide hadj)).symm
    exact not_lt_of_ge (hd_ij.2 hCD_dist) (hlam_CD ▸ hlt)

/-! ## Proof of Graph Minors X, (10.4) -/

/-- A tangle `𝒯` in a hypergraph `G` is a *maximal tangle* if it is a tangle in `G` and is not a
proper subset (truncation) of any tangle in `G` (Graph Minors X, Section 1, page 155, and
Section 10, (10.4), page 184). -/
def IsMaximalTangle (G : Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  (∃ θ, IsTangle G θ 𝒯) ∧
    ∀ ⦃𝒯' : Set (Hypergraph α β × Hypergraph α β)⦄,
      (∃ θ', IsTangle G θ' 𝒯') → 𝒯 ⊆ 𝒯' → 𝒯' = 𝒯

/-- The set of all maximal tangles in a hypergraph `G` (Graph Minors X, Section 10, (10.4),
page 184). -/
def maximalTangles (G : Hypergraph α β) :
    Set (Set (Hypergraph α β × Hypergraph α β)) :=
  {𝒯 | IsMaximalTangle G 𝒯}

/-- Distinct maximal tangles in `G` are distinguishable (Graph Minors X, Section 10, proof of
(10.4), page 184). -/
theorem IsMaximalTangle.areDistinguishable {G : Hypergraph α β}
    {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)}
    (h₁ : IsMaximalTangle G 𝒯₁) (h₂ : IsMaximalTangle G 𝒯₂) (hne : 𝒯₁ ≠ 𝒯₂) :
    AreDistinguishable 𝒯₁ 𝒯₂ := by
  rintro (hsub | hsub)
  · exact hne (h₁.2 h₂.1 hsub).symm
  · exact hne (h₂.2 h₁.1 hsub)

/-- In a standard tree-decomposition `(T, τ)` of `G` relative to `𝒯₁, …, 𝒯ₙ`, for every adjacent
pair `T.Adj u v`, the separation `(treeDecompSide T τ s(u, v) u, treeDecompSide T τ s(u, v) v)` is
the `(𝒯 v, 𝒯 u)`-distinction (Graph Minors X, Section 10, (10.3), page 181). -/
theorem IsStandardTreeDecomposition.isDistinction_of_adj {n : ℕ} {Λ : Type*} [LinearOrder Λ]
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (hstd : IsStandardTreeDecomposition G lam 𝒯 T τ)
    {u v : Fin n} (hadj : T.Adj u v) :
    IsDistinction lam (𝒯 v) (𝒯 u)
      (treeDecompSide T τ s(u, v) u) (treeDecompSide T τ s(u, v) v) := by
  obtain ⟨e, _, he_path, _, A, B, hmk, hd_uv, hd_vu⟩ :=
    hstd.path_min_isDistinction hadj.ne
  let p : T.Walk u v := Walk.cons hadj Walk.nil
  have hp : p.IsPath := by simp [p, hadj.ne]
  have he_mem : e ∈ p.edges := he_path p hp
  simp only [p, Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at he_mem
  subst he_mem
  obtain ⟨u', v', _, heq, rfl, rfl⟩ := hmk
  rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exfalso
    exact hstd.isHome u hadj (Reachable.refl u) hd_uv.1.1
  · simpa [Sym2.eq_swap] using hd_vu

/-- Strict vertex-set inclusion in the proof of **Graph Minors X, (10.4)** (page 184):
"Let $e, f \in E(T)$ be distinct, making separations $(A, B)$ and $(C, D)$, say, where $A
\subseteq C$ and $D \subseteq B$. If $V(A) = V(C)$ then it follows easily that $A = C$, $B =
D$, a contradiction; thus $V(A) \subset V(C)$ and similarly $V(D) \subset V(B)$."
(We deduce `V(A) ⊂ V(C)` directly from `(2.9)(ii)` and `(10.3)(i)`, which avoids assuming `G` has
no edges with ends in `V(A ∩ B)`.) -/
theorem theorem_10_4_strict_inclusion {n : ℕ} {Λ : Type*} [LinearOrder Λ]
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : Fin n → ℕ} {𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : ∀ i : Fin n, IsTangle G (θ i) (𝒯 i))
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (hstd : IsStandardTreeDecomposition G lam 𝒯 T τ)
    {u v x y : Fin n} (hadj_uv : T.Adj u v) (hadj_xy : T.Adj x y)
    (hvx : (T.deleteEdges {s(u, v)}).Reachable v x)
    (hxu : (T.deleteEdges {s(x, y)}).Reachable x u) :
    (treeDecompSide T τ s(u, v) u).vertexSet ⊂ (treeDecompSide T τ s(x, y) x).vertexSet ∧
      (treeDecompSide T τ s(x, y) y).vertexSet ⊂ (treeDecompSide T τ s(u, v) v).vertexSet := by
  have hTD := hstd.isTreeDecomposition
  have hle := treeDecompSide_le_of_distinct_edges hTD hadj_uv hadj_xy hvx hxu
  have hne_edge : s(u, v) ≠ s(x, y) := by
    intro heq
    have hnot_uv := not_reachable_deleteEdges hTD.isTree hadj_uv
    rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hnot_uv hvx.symm
    · exact not_reachable_deleteEdges hTD.isTree hadj_xy hxu
  have hstrict : ∀ {u₁ v₁ x₁ y₁ : Fin n},
      T.Adj u₁ v₁ → T.Adj x₁ y₁ → s(u₁, v₁) ≠ s(x₁, y₁) →
      (T.deleteEdges {s(x₁, y₁)}).Reachable x₁ u₁ →
      treeDecompSide T τ s(u₁, v₁) u₁ ≤ treeDecompSide T τ s(x₁, y₁) x₁ →
      treeDecompSide T τ s(x₁, y₁) y₁ ≤ treeDecompSide T τ s(u₁, v₁) v₁ →
      (treeDecompSide T τ s(u₁, v₁) u₁).vertexSet ⊂
        (treeDecompSide T τ s(x₁, y₁) x₁).vertexSet := by
    intro u₁ v₁ x₁ y₁ hadj₁ hadj₂ hne hx₁u₁ hAC hDB
    refine ssubset_of_subset_of_ne hAC.vertexSet_subset ?_
    intro hV_eq
    let A := treeDecompSide T τ s(u₁, v₁) u₁
    let B := treeDecompSide T τ s(u₁, v₁) v₁
    let C := treeDecompSide T τ s(x₁, y₁) x₁
    let D := treeDecompSide T τ s(x₁, y₁) y₁
    have hAB_mem : (A, B) ∈ 𝒯 v₁ := (hstd.isDistinction_of_adj hadj₁).1.1
    have hsep_CD : G.IsSeparation C D := hTD.isSeparation_treeDecompSide hadj₂
    have hCD_sub_AB : (C ∩ D).vertexSet ⊆ (A ∩ B).vertexSet := by
      change C.vertexSet ∩ D.vertexSet ⊆ A.vertexSet ∩ B.vertexSet
      rw [← hV_eq]
      exact Set.inter_subset_inter_right _ hDB.vertexSet_subset
    have hord_le : separationOrder C D ≤ separationOrder A B :=
      Set.ncard_le_ncard hCD_sub_AB (A ∩ B).vertexSet_finite
    have hord_CD : separationOrder C D < θ v₁ :=
      hord_le.trans_lt ((h𝒯 v₁).order_lt hAB_mem)
    have hCD_mem : (C, D) ∈ 𝒯 v₁ :=
      theorem_2_9_proof (h𝒯 v₁) hAB_mem hsep_CD hord_CD (Or.inr (Or.inl hV_eq.symm.subset))
    have hadj₁_in_2 : (T.deleteEdges {s(x₁, y₁)}).Adj u₁ v₁ :=
      deleteEdges_adj.mpr ⟨hadj₁, hne⟩
    have hx₁v₁ : (T.deleteEdges {s(x₁, y₁)}).Reachable x₁ v₁ :=
      hx₁u₁.trans hadj₁_in_2.reachable
    exact hstd.isHome v₁ hadj₂ hx₁v₁ hCD_mem
  refine ⟨hstrict hadj_uv hadj_xy hne_edge hxu hle.1 hle.2, ?_⟩
  have hadj_uv_in_xy : (T.deleteEdges {s(u, v)}).Adj x y :=
    deleteEdges_adj.mpr ⟨hadj_xy, hne_edge.symm⟩
  have hvy : (T.deleteEdges {s(u, v)}).Reachable v y :=
    hvx.trans hadj_uv_in_xy.reachable
  have h := hstrict hadj_xy.symm hadj_uv.symm
    (by intro heq; exact hne_edge (by simpa [Sym2.eq_swap] using heq.symm))
    (by simpa [Sym2.eq_swap] using hvy)
    (by simpa [Sym2.eq_swap] using hle.2)
    (by simpa [Sym2.eq_swap] using hle.1)
  simpa [Sym2.eq_swap] using h

/-- In a standard tree-decomposition `(T, τ)` of `G` relative to `𝒯₁, …, 𝒯ₙ`, for every edge
`T.Adj t p`, `(τ t).vertexSet` is not contained in `(τ p).vertexSet`. -/
theorem IsStandardTreeDecomposition.not_bag_vertexSet_subset_of_adj
    {n : ℕ} {Λ : Type*} [LinearOrder Λ]
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : Fin n → ℕ} {𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : ∀ i : Fin n, IsTangle G (θ i) (𝒯 i))
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (hstd : IsStandardTreeDecomposition G lam 𝒯 T τ)
    {t p : Fin n} (hadj_tp : T.Adj t p) :
    ¬ (τ t).vertexSet ⊆ (τ p).vertexSet := by
  classical
  intro hsub
  have hTD := hstd.isTreeDecomposition
  let A := treeDecompSide T τ s(t, p) t
  let B := treeDecompSide T τ s(t, p) p
  have hsep_AB : G.IsSeparation A B := hTD.isSeparation_treeDecompSide hadj_tp
  have hBA_mem : (B, A) ∈ 𝒯 t := by
    have hd := hstd.isDistinction_of_adj hadj_tp.symm
    simpa [A, B, Sym2.eq_swap] using hd.1.1
  have hAB_not : (A, B) ∉ 𝒯 t := theorem_2_1_proof (h𝒯 t) hBA_mem
  have hord_AB : separationOrder A B < θ t := by
    rw [separationOrder_comm]
    exact (h𝒯 t).order_lt hBA_mem
  have hτt_le_A : τ t ≤ A := le_treeDecompSide hTD (Reachable.refl t)
  have hτp_le_B : τ p ≤ B := le_treeDecompSide hTD (Reachable.refl p)
  have hτt_sub_B : (τ t).vertexSet ⊆ B.vertexSet :=
    hsub.trans hτp_le_B.vertexSet_subset
  have hτt_sub_AB : (τ t).vertexSet ⊆ (A ∩ B).vertexSet :=
    Set.subset_inter hτt_le_A.vertexSet_subset hτt_sub_B
  let S : Finset (Fin n) := Finset.univ.filter (fun u ↦ T.Adj u t ∧ u ≠ p)
  let Au : Fin n → Hypergraph α β := fun u ↦ treeDecompSide T τ s(u, t) u
  let Bu : Fin n → Hypergraph α β := fun u ↦ treeDecompSide T τ s(u, t) t
  have hAu_mem : ∀ u ∈ S, (Au u, Bu u) ∈ 𝒯 t := by
    intro u hu
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact (hstd.isDistinction_of_adj hu.1).1.1
  have hAuBu_sub_τt : ∀ u ∈ S, (Au u ∩ Bu u).vertexSet ⊆ (τ t).vertexSet := by
    intro u hu x ⟨hxA, hxB⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Au, Bu, treeDecompSide, biUnion, Set.mem_iUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at hxA hxB
    obtain ⟨w₁, hw₁, hxw₁⟩ := hxA
    obtain ⟨w₂, hw₂, hxw₂⟩ := hxB
    have hon : OnTreePath T w₂ w₁ t :=
      onTreePath_of_reachable_deleteEdges hTD.isTree hu.1.symm
        (by simpa [Sym2.eq_swap] using hw₂)
        (by simpa [Sym2.eq_swap] using hw₁)
    exact (hTD.inter_le hon).vertexSet_subset ⟨hxw₂, hxw₁⟩
  -- Combine `(Au u, Bu u)` over `F ⊆ S` by induction on `F`:
  have hcombine : ∀ (F : Finset (Fin n)), F ⊆ S → F.Nonempty →
      ∃ C D : Hypergraph α β, (C, D) ∈ 𝒯 t ∧
        (∀ x ∈ D.vertexSet, ∀ u ∈ F, x ∈ (Bu u).vertexSet) ∧
        (C ∩ D).vertexSet ⊆ (τ t).vertexSet := by
    intro F hFS hFne
    induction F using Finset.cons_induction with
    | empty => exact (Finset.not_nonempty_empty hFne).elim
    | @cons a s ha_notMem ih =>
      have haS : a ∈ S := hFS (Finset.mem_cons_self a s)
      have hsS : s ⊆ S := (Finset.subset_cons ha_notMem).trans hFS
      rcases s.eq_empty_or_nonempty with rfl | hs_ne
      · refine ⟨Au a, Bu a, hAu_mem a haS, ?_, hAuBu_sub_τt a haS⟩
        intro x hx u hu
        simp only [Finset.cons_empty, Finset.mem_singleton] at hu
        exact hu ▸ hx
      · obtain ⟨C, D, hCD_mem, hD_mem, hCD_sub⟩ := ih hsS hs_ne
        let C' := C ∪ Au a
        let D' := D ∩ Bu a
        have hC'D'_sub : (C' ∩ D').vertexSet ⊆ (τ t).vertexSet := by
          intro x hx
          change (x ∈ C.vertexSet ∨ x ∈ (Au a).vertexSet) ∧
            (x ∈ D.vertexSet ∧ x ∈ (Bu a).vertexSet) at hx
          rcases hx with ⟨hxC | hxAa, hxD, hxBa⟩
          · exact hCD_sub ⟨hxC, hxD⟩
          · exact hAuBu_sub_τt a haS ⟨hxAa, hxBa⟩
        have hord_C'D' : separationOrder C' D' < θ t := by
          have hle : separationOrder C' D' ≤ separationOrder A B :=
            Set.ncard_le_ncard (hC'D'_sub.trans hτt_sub_AB) (A ∩ B).vertexSet_finite
          exact hle.trans_lt hord_AB
        have hC'D'_mem : (C', D') ∈ 𝒯 t :=
          theorem_2_2_proof (h𝒯 t) hCD_mem (hAu_mem a haS) hord_C'D'
        refine ⟨C', D', hC'D'_mem, ?_, hC'D'_sub⟩
        intro x hx u hu
        rcases Finset.mem_cons.1 hu with rfl | hus
        · exact hx.2
        · exact hD_mem x hx.1 u hus
  -- Any vertex `x ∈ V(G)` that belongs to `Bu u` for all `u ∈ S` must belong to `B`:
  have h_in_B : ∀ x ∈ G.vertexSet, (∀ u ∈ S, x ∈ (Bu u).vertexSet) → x ∈ B.vertexSet := by
    intro x hxG hxBu
    by_contra hx_notB
    have hxA : x ∈ A.vertexSet :=
      (hsep_AB.vertexSet_union.symm ▸ hxG).resolve_right hx_notB
    simp only [A, treeDecompSide, biUnion, Set.mem_iUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at hxA
    obtain ⟨w, htw, hxw⟩ := hxA
    have hwt_ne : w ≠ t := by
      rintro rfl
      exact hx_notB (hτt_sub_B hxw)
    obtain ⟨q, hq⟩ := htw.exists_isPath
    cases q with
    | nil => exact (hwt_ne rfl).elim
    | @cons _ u _ hstep q' =>
      rcases deleteEdges_adj.1 hstep with ⟨hadj_tu, hne_edge⟩
      have hu_ne_p : u ≠ p := by
        rintro rfl
        exact hne_edge rfl
      have huS : u ∈ S := by
        simp [S, hadj_tu.symm, hu_ne_p]
      rw [Walk.cons_isPath_iff] at hq
      let q'_T : T.Walk u w := q'.map (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le {s(t, p)}))
      have ht_notMem : t ∉ q'_T.support := by
        simpa [q'_T] using hq.2
      have huw : (T.deleteEdges {s(u, t)}).Reachable u w := by
        simpa [Sym2.eq_swap] using
          (reachable_deleteEdges_of_notMem_support (w := u) q'_T ht_notMem)
      have hx_Bu : x ∈ (Bu u).vertexSet := hxBu u huS
      simp only [Bu, treeDecompSide, biUnion, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and] at hx_Bu
      obtain ⟨w', htw', hxw'⟩ := hx_Bu
      have hon : OnTreePath T w' w t :=
        onTreePath_of_reachable_deleteEdges hTD.isTree hadj_tu
          (by simpa [Sym2.eq_swap] using htw')
          (by simpa [Sym2.eq_swap] using huw)
      have hx_τt : x ∈ (τ t).vertexSet :=
        (hTD.inter_le hon).vertexSet_subset ⟨hxw', hxw⟩
      exact hx_notB (hτt_sub_B hx_τt)
  rcases S.eq_empty_or_nonempty with hS_empty | hS_ne
  · have hB_eq_G : B.vertexSet = G.vertexSet := by
      refine Set.Subset.antisymm hsep_AB.right_le.vertexSet_subset (fun x hxG ↦ ?_)
      exact h_in_B x hxG (fun u hu ↦ by simp [hS_empty] at hu)
    exact (h𝒯 t).axiom3 hBA_mem hB_eq_G
  · obtain ⟨C, D, hCD_mem, hD_mem, _⟩ := hcombine S (Finset.Subset.refl S) hS_ne
    have hD_sub_B : D.vertexSet ⊆ B.vertexSet := by
      intro x hxD
      exact h_in_B x (((h𝒯 t).isSeparation hCD_mem).right_le.vertexSet_subset hxD) (hD_mem x hxD)
    have hAB_mem : (A, B) ∈ 𝒯 t :=
      theorem_2_9_case_1 (h𝒯 t) hCD_mem hsep_AB hord_AB hD_sub_B
    exact hAB_not hAB_mem

/-- In a standard tree-decomposition `(T, τ)` of `G` relative to `n` tangles `𝒯₁, …, 𝒯ₙ`,
`n ≤ |V(G)|` (Graph Minors X, Section 10, (10.4), page 184). -/
theorem IsStandardTreeDecomposition.card_le_ncard_vertexSet
    {n : ℕ} {Λ : Type*} [LinearOrder Λ]
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : Fin n → ℕ} {𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : ∀ i : Fin n, IsTangle G (θ i) (𝒯 i))
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (hstd : IsStandardTreeDecomposition G lam 𝒯 T τ) :
    n ≤ G.vertexSet.ncard := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  let r₀ : Fin n := ⟨0, hn⟩
  by_cases hn2 : 2 ≤ n
  · have hTD := hstd.isTreeDecomposition
    -- `V(τ r₀)` is nonempty since `r₀` has a neighbor in `T`:
    have hτ_r₀_ne : (τ r₀).vertexSet.Nonempty := by
      obtain ⟨t₁, hne⟩ : ∃ t₁ : Fin n, r₀ ≠ t₁ :=
        ⟨⟨1, hn2⟩, by simp [r₀, Fin.ext_iff]⟩
      obtain ⟨q, _, _⟩ := hTD.isTree.existsUnique_path r₀ t₁
      cases q with
      | nil => exact (hne rfl).elim
      | @cons _ u _ hadj _ =>
        have hnot := hstd.not_bag_vertexSet_subset_of_adj h𝒯 hadj
        obtain ⟨x, hx, _⟩ := Set.not_subset.1 hnot
        exact ⟨x, hx⟩
    -- For every `t ≠ r₀`, choose the neighbor `p` of `t` on the path from `t` to `r₀`:
    have hparent : ∀ t : Fin n, t ≠ r₀ →
        ∃ p : Fin n, T.Adj t p ∧ (T.deleteEdges {s(t, p)}).Reachable p r₀ := by
      intro t hne
      obtain ⟨q, hq, _⟩ := hTD.isTree.existsUnique_path t r₀
      cases q with
      | nil => exact (hne rfl).elim
      | @cons _ p _ hadj q' =>
        rw [Walk.cons_isPath_iff] at hq
        exact ⟨p, hadj, reachable_deleteEdges_of_notMem_support q' hq.2⟩
    choose parent hadj_parent hreach_parent using hparent
    have hvertex_exists : ∀ t : Fin n,
        ∃ x ∈ (τ t).vertexSet, ∀ h : t ≠ r₀, x ∉ (τ (parent t h)).vertexSet := by
      intro t
      by_cases ht : t = r₀
      · subst ht
        obtain ⟨x, hx⟩ := hτ_r₀_ne
        exact ⟨x, hx, fun h ↦ (h rfl).elim⟩
      · have hnot := hstd.not_bag_vertexSet_subset_of_adj h𝒯 (hadj_parent t ht)
        obtain ⟨x, hxt, hxp⟩ := Set.not_subset.1 hnot
        exact ⟨x, hxt, fun _ ↦ hxp⟩
    choose f hf_mem hf_notMem using hvertex_exists
    have hf_in_G : Set.range f ⊆ G.vertexSet := by
      rintro x ⟨t, rfl⟩
      exact (hTD.le t).vertexSet_subset (hf_mem t)
    have hf_inj : Function.Injective f := by
      intro t₁ t₂ hfeq
      by_contra hne
      -- Helper: if `ht : tᵢ ≠ r₀` and `tⱼ` is in the `parent tᵢ ht`-component of
      -- `T \ s(tᵢ, parent tᵢ ht)`, we get a contradiction from `(T3)`.
      have h_contra : ∀ (a b : Fin n) (ha : a ≠ r₀),
          f a = f b →
          (T.deleteEdges {s(a, parent a ha)}).Reachable (parent a ha) b → False := by
        intro a b ha hfab hr_pb
        have hon : OnTreePath T b a (parent a ha) :=
          onTreePath_of_reachable_deleteEdges hTD.isTree (hadj_parent a ha).symm
            (by simpa [Sym2.eq_swap] using hr_pb)
            (by simp)
        have hmem_p : f a ∈ (τ (parent a ha)).vertexSet :=
          (hTD.inter_le hon).vertexSet_subset ⟨hfab ▸ hf_mem b, hf_mem a⟩
        exact hf_notMem a ha hmem_p
      by_cases ht₁ : t₁ = r₀
      · subst ht₁
        have ht₂ : t₂ ≠ r₀ := Ne.symm hne
        exact h_contra t₂ r₀ ht₂ hfeq.symm (hreach_parent t₂ ht₂)
      · by_cases ht₂ : t₂ = r₀
        · subst ht₂
          exact h_contra t₁ r₀ ht₁ hfeq (hreach_parent t₁ ht₁)
        · rcases reachable_deleteEdges_or hTD.isTree.connected
            (u := t₁) (v := parent t₁ ht₁) t₂ with hr₁ | hr₁
          · rcases reachable_deleteEdges_or hTD.isTree.connected
              (u := t₂) (v := parent t₂ ht₂) t₁ with hr₂ | hr₂
            · -- Neither `parent t₁` nor `parent t₂` separates `t₁` and `t₂`, impossible:
              have hnot₁ : ¬ (T.deleteEdges {s(t₁, parent t₁ ht₁)}).Reachable (parent t₁ ht₁) t₂ :=
                fun h ↦ not_reachable_deleteEdges hTD.isTree (hadj_parent t₁ ht₁)
                  (hr₁.trans h.symm)
              have hr_p₁_r₀ :
                  (T.deleteEdges {s(t₂, parent t₂ ht₂)}).Reachable (parent t₁ ht₁) r₀ :=
                reachable_deleteEdges_of_not_reachable (hreach_parent t₁ ht₁) hnot₁
              have hne_edge : s(t₁, parent t₁ ht₁) ≠ s(t₂, parent t₂ ht₂) := by
                intro heq
                rcases Sym2.eq_iff.1 heq with ⟨h1, _⟩ | ⟨h1, h2⟩
                · exact hne h1
                · subst h2
                  exact not_reachable_deleteEdges hTD.isTree (hadj_parent t₁ ht₁) hr₁
              have hadj₁_in_2 :
                  (T.deleteEdges {s(t₂, parent t₂ ht₂)}).Adj t₁ (parent t₁ ht₁) :=
                deleteEdges_adj.mpr ⟨hadj_parent t₁ ht₁, hne_edge⟩
              have hr_t₂_r₀ : (T.deleteEdges {s(t₂, parent t₂ ht₂)}).Reachable t₂ r₀ :=
                hr₂.trans (hadj₁_in_2.reachable.trans hr_p₁_r₀)
              exact not_reachable_deleteEdges hTD.isTree (hadj_parent t₂ ht₂)
                (hr_t₂_r₀.trans (hreach_parent t₂ ht₂).symm)
            · exact (h_contra t₂ t₁ ht₂ hfeq.symm hr₂).elim
          · exact (h_contra t₁ t₂ ht₁ hfeq hr₁).elim
    have hcard_range : (Set.range f).ncard = n := by
      rw [Set.ncard_range_of_injective hf_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [← hcard_range]
    exact Set.ncard_le_ncard hf_in_G G.vertexSet_finite
  · have hn1 : n = 1 := by omega
    rw [hn1]
    exact (h𝒯 r₀).one_le.trans (h𝒯 r₀).order_le_ncard_vertexSet

/-- In a standard tree-decomposition `(T, τ)` of `G` relative to `n ≥ 1` tangles `𝒯₁, …, 𝒯ₙ`,
`|E(T)| ≤ |V(G)| - 1` (Graph Minors X, Section 10, proof of (10.4), page 184). -/
theorem IsStandardTreeDecomposition.ncard_edgeSet_le
    {n : ℕ} {Λ : Type*} [LinearOrder Λ]
    {G : Hypergraph α β} {lam : Hypergraph α β × Hypergraph α β → Λ}
    {θ : Fin n → ℕ} {𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    (hn : 1 ≤ n) (h𝒯 : ∀ i : Fin n, IsTangle G (θ i) (𝒯 i))
    {T : SimpleGraph (Fin n)} {τ : Fin n → Hypergraph α β}
    (hstd : IsStandardTreeDecomposition G lam 𝒯 T τ) :
    T.edgeSet.ncard ≤ G.vertexSet.ncard - 1 := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have htree := hstd.isTreeDecomposition.isTree.card_edgeFinset
  rw [Fintype.card_fin] at htree
  rw [Set.ncard_eq_toFinset_card']
  change T.edgeFinset.card ≤ G.vertexSet.ncard - 1
  have hle := hstd.card_le_ncard_vertexSet h𝒯
  omega

/-- Any family of `n` mutually distinguishable tangles in a hypergraph `G` has `n ≤ |V(G)|`
(Graph Minors X, Section 10, (10.4), page 184). -/
theorem card_le_of_mutually_distinguishable {n : ℕ} (G : Hypergraph α β)
    {θ : Fin n → ℕ} {𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : ∀ i : Fin n, IsTangle G (θ i) (𝒯 i))
    (hdist : ∀ i j : Fin n, i ≠ j → AreDistinguishable (𝒯 i) (𝒯 j)) :
    n ≤ G.vertexSet.ncard := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  obtain ⟨lam, hTB⟩ := theorem_9_2_proof G
  obtain ⟨T, τ, hstd⟩ := theorem_10_3_proof G lam θ 𝒯 hn hTB h𝒯 hdist
  exact hstd.card_le_ncard_vertexSet h𝒯

/-- The set of all maximal tangles in `G` is finite (Graph Minors X, Section 10, (10.4),
page 184). -/
theorem maximalTangles_finite (G : Hypergraph α β) :
    (maximalTangles G).Finite := by
  have hsep_fin : {p : Hypergraph α β × Hypergraph α β | G.IsSeparation p.1 p.2}.Finite :=
    finite_of_forall_isSeparation (G := G) (fun _ h ↦ h)
  refine hsep_fin.finite_subsets.subset ?_
  intro 𝒯 h𝒯 p hp
  obtain ⟨θ, hT⟩ := h𝒯.1
  exact hT.isSeparation hp

/-- **Graph Minors X, (10.4)** (page 184):
"In any hypergraph $G$ there are at most $|V(G)|$ maximal tangles." -/
theorem theorem_10_4_proof (G : Hypergraph α β) :
    (maximalTangles G).ncard ≤ G.vertexSet.ncard := by
  classical
  have hfin := maximalTangles_finite G
  let n := (maximalTangles G).ncard
  have hcard : Fintype.card hfin.toFinset = n := by
    rw [Fintype.card_coe, ← Set.ncard_eq_toFinset_card (maximalTangles G) hfin]
  let e : Fin n ≃ hfin.toFinset := (Fintype.equivFinOfCardEq hcard).symm
  let 𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β) := fun i ↦ (e i).1
  have hmax : ∀ i : Fin n, IsMaximalTangle G (𝒯 i) := by
    intro i
    exact (hfin.mem_toFinset).1 (e i).2
  choose θ h𝒯 using fun i ↦ (hmax i).1
  have hdist : ∀ i j : Fin n, i ≠ j → AreDistinguishable (𝒯 i) (𝒯 j) := by
    intro i j hij
    refine (hmax i).areDistinguishable (hmax j) ?_
    intro heq
    exact hij (e.injective (Subtype.ext heq))
  exact card_le_of_mutually_distinguishable G h𝒯 hdist


end GraphMinor.GM10
