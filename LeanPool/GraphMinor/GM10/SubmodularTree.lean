/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.SubmodularBasic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Tree Constructions for Submodular Labellings: Graph Minors X, Section 3

This file provides the tree constructions used in the proofs of `(3.4)` and `(3.6)` of
Robertson and Seymour, *Graph Minors. X. Obstructions to tree-decomposition*,
J. Combin. Theory Ser. B 52 (1991) 153–190 (pages 162–164):
- Local neighborhood equivalences (`NeighborEquiv`) transferring degree, leaf status, degree-3
  union, and fork exactness between tree-labellings.
- Base-case trees on `Fin 2` and `Fin 4` for `(3.4)`.
- Splicing a tree `S = T₁ \ t₀` onto a bad leaf `t₁` of `T₂` for the inductive step of `(3.4)`.
- Suppressing a leaf `v₀` with `α(v₀, e₀) = E` and its degree-3 neighbor `v` for `(3.6)`.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph

variable {β : Type*} {ι ι' : Type*}

/-! ## Local neighborhood equivalences -/

/-- Given an equivalence between the neighbors of `u'` in `T'` and the neighbors of `u` in `T`,
their degrees are equal. -/
theorem degree_eq_of_neighborEquiv [Fintype ι'] [Fintype ι]
    {T' : SimpleGraph ι'} {T : SimpleGraph ι} {u' : ι'} {u : ι}
    (e : {w' // T'.Adj u' w'} ≃ {w // T.Adj u w}) :
    by classical exact T'.degree u' = T.degree u := by
  classical
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact Fintype.card_congr e

/-- Given an equivalence between the neighbors of `u'` in `T'` and the neighbors of `u` in `T`,
`u'` is a leaf of `T'` if and only if `u` is a leaf of `T`. -/
theorem isLeaf_iff_of_neighborEquiv [Fintype ι'] [Fintype ι]
    {T' : SimpleGraph ι'} {T : SimpleGraph ι} {u' : ι'} {u : ι}
    (e : {w' // T'.Adj u' w'} ≃ {w // T.Adj u w}) :
    IsLeaf T' u' ↔ IsLeaf T u := by
  classical
  simp only [IsLeaf, degree_eq_of_neighborEquiv e]

/-- Transfer the degree-3 union property along a neighbor equivalence where each label at `u'`
contains the corresponding label at `u`. -/
theorem degree_three_union_eq_of_neighborEquiv [Fintype ι]
    {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    {T' : SimpleGraph ι'} {T : SimpleGraph ι}
    {α' : ι' → Sym2 ι' → Set β} {α : ι → Sym2 ι → Set β}
    (hα : IsTreeLabelling E κ 𝒜 T α) {u' : ι'} {u : ι}
    (e : {w' // T'.Adj u' w'} ≃ {w // T.Adj u w})
    (hsub : ∀ w' (hw' : T'.Adj u' w'), α u s(u, (e ⟨w', hw'⟩).1) ⊆ α' u' s(u', w'))
    (hsubE : ∀ w' (_hw' : T'.Adj u' w'), α' u' s(u', w') ⊆ E)
    {f₁' f₂' f₃' : Sym2 ι'}
    (hf₁' : IsTreeIncidence T' u' f₁') (hf₂' : IsTreeIncidence T' u' f₂')
    (hf₃' : IsTreeIncidence T' u' f₃')
    (h12' : f₁' ≠ f₂') (h13' : f₁' ≠ f₃') (h23' : f₂' ≠ f₃') :
    α' u' f₁' ∪ α' u' f₂' ∪ α' u' f₃' = E := by
  obtain ⟨w₁', hw₁', rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf₁'
  obtain ⟨w₂', hw₂', rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf₂'
  obtain ⟨w₃', hw₃', rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf₃'
  have hne12 : w₁' ≠ w₂' := fun h ↦ h12' (by rw [h])
  have hne13 : w₁' ≠ w₃' := fun h ↦ h13' (by rw [h])
  have hne23 : w₂' ≠ w₃' := fun h ↦ h23' (by rw [h])
  let w₁ := e ⟨w₁', hw₁'⟩
  let w₂ := e ⟨w₂', hw₂'⟩
  let w₃ := e ⟨w₃', hw₃'⟩
  have hw12 : w₁.1 ≠ w₂.1 := fun h ↦ hne12 (Subtype.ext_iff.1 (e.injective (Subtype.ext h)))
  have hw13 : w₁.1 ≠ w₃.1 := fun h ↦ hne13 (Subtype.ext_iff.1 (e.injective (Subtype.ext h)))
  have hw23 : w₂.1 ≠ w₃.1 := fun h ↦ hne23 (Subtype.ext_iff.1 (e.injective (Subtype.ext h)))
  have hf₁ : IsTreeIncidence T u s(u, w₁.1) := isTreeIncidence_iff_adj.2 w₁.2
  have hf₂ : IsTreeIncidence T u s(u, w₂.1) := isTreeIncidence_iff_adj.2 w₂.2
  have hf₃ : IsTreeIncidence T u s(u, w₃.1) := isTreeIncidence_iff_adj.2 w₃.2
  have he12 : s(u, w₁.1) ≠ s(u, w₂.1) := sym2_mk_eq_left_iff.not.2 hw12
  have he13 : s(u, w₁.1) ≠ s(u, w₃.1) := sym2_mk_eq_left_iff.not.2 hw13
  have he23 : s(u, w₂.1) ≠ s(u, w₃.1) := sym2_mk_eq_left_iff.not.2 hw23
  have hunion := hα.degree_three_union_eq hf₁ hf₂ hf₃ he12 he13 he23
  refine Set.Subset.antisymm
    (Set.union_subset (Set.union_subset (hsubE w₁' hw₁') (hsubE w₂' hw₂')) (hsubE w₃' hw₃')) ?_
  intro x hx
  rw [← hunion] at hx
  rcases hx with (hx | hx) | hx
  · exact Or.inl (Or.inl (hsub w₁' hw₁' hx))
  · exact Or.inl (Or.inr (hsub w₂' hw₂' hx))
  · exact Or.inr (hsub w₃' hw₃' hx)

/-- Transfer fork exactness along a neighbor equivalence preserving edge labels. -/
theorem isExactFork_of_neighborEquiv
    {T' : SimpleGraph ι'} {T : SimpleGraph ι}
    {α' : ι' → Sym2 ι' → Set β} {α : ι → Sym2 ι → Set β}
    {u' : ι'} {u : ι}
    (e : {w' // T'.Adj u' w'} ≃ {w // T.Adj u w})
    (heq : ∀ w' (hw' : T'.Adj u' w'), α' u' s(u', w') = α u s(u, (e ⟨w', hw'⟩).1))
    (hex : ∀ ⦃f₁ f₂ : Sym2 ι⦄, IsFork T u f₁ f₂ → IsExactFork α u f₁ f₂)
    {f₁' f₂' : Sym2 ι'} (hf' : IsFork T' u' f₁' f₂') :
    IsExactFork α' u' f₁' f₂' := by
  obtain ⟨w₁', hw₁', rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf'.1
  obtain ⟨w₂', hw₂', rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf'.2.1
  have hne : w₁' ≠ w₂' := fun h ↦ hf'.2.2 (by rw [h])
  let w₁ := e ⟨w₁', hw₁'⟩
  let w₂ := e ⟨w₂', hw₂'⟩
  have hw12 : w₁.1 ≠ w₂.1 := fun h ↦ hne (Subtype.ext_iff.1 (e.injective (Subtype.ext h)))
  have hf : IsFork T u s(u, w₁.1) s(u, w₂.1) :=
    ⟨isTreeIncidence_iff_adj.2 w₁.2, isTreeIncidence_iff_adj.2 w₂.2,
     sym2_mk_eq_left_iff.not.2 hw12⟩
  dsimp [IsExactFork]
  rw [heq w₁' hw₁', heq w₂' hw₂']
  exact hex hf

/-! ## Base-case trees on `Fin 2` and `Fin 4` for (3.4) -/

private theorem degree_eq_degree {V : Type*} (G : SimpleGraph V) (v : V)
    (inst₁ inst₂ : Fintype (G.neighborSet v)) :
    @SimpleGraph.degree V G v inst₁ = @SimpleGraph.degree V G v inst₂ :=
  Subsingleton.elim inst₁ inst₂ ▸ rfl

/-- A 2-vertex tree-labelling when `E = ∅` and `∅` is efficient
(Graph Minors X, Section 3, proof of (3.4), page 162). -/
theorem exists_isTreeLabelling_of_empty {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    (hE : E = ∅) (heff : IsEfficient E κ ∅) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
      IsTreeLabelling E κ 𝒜 T α := by
  let T : SimpleGraph (Fin 2) := ⊤
  let α : Fin 2 → Sym2 (Fin 2) → Set β := fun _ _ ↦ ∅
  have hcard : Nat.card T.edgeSet + 1 = Nat.card (Fin 2) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← T.edgeFinset_card]
    decide
  have hT_tree : T.IsTree := isTree_iff_connected_and_card.2 ⟨connected_top, hcard⟩
  have hT : IsTernaryTree T := by
    refine ⟨hT_tree, fun v ↦ Or.inl ?_⟩
    rw [degree_eq_degree T v _ inferInstance]
    fin_cases v <;> decide
  refine ⟨Fin 2, inferInstance, T, α, hT, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    exact heff
  · intro u v _
    simp [α, hE]
  · intro v e _ _
    left
    simp [α, hE]
  · intro v e₁ e₂ e₃ _ _ _ _ _ _
    simp [α, hE]

/-- The 4-vertex star graph with center `0 : Fin 4` and leaves `1, 2, 3 : Fin 4`
(Graph Minors X, Section 3, proof of (3.4), page 162). -/
def starFourGraph : SimpleGraph (Fin 4) where
  Adj u v := (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)
  symm := ⟨by
    rintro _ _ (h | h)
    · exact Or.inr h
    · exact Or.inl h⟩
  loopless := ⟨fun _ h ↦ by rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact h rfl⟩

instance : DecidableRel starFourGraph.Adj := fun u v ↦
  inferInstanceAs (Decidable ((u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)))

theorem isTernaryTree_starFourGraph : IsTernaryTree starFourGraph := by
  have hconn : starFourGraph.Connected := by
    refine Connected.mk fun u v ↦ ?_
    have h0 : ∀ x : Fin 4, starFourGraph.Reachable 0 x := by
      intro x
      by_cases hx : x = 0
      · subst hx; exact Reachable.rfl
      · exact Adj.reachable (Or.inl ⟨rfl, hx⟩)
    exact (h0 u).symm.trans (h0 v)
  have hcard : Nat.card starFourGraph.edgeSet + 1 = Nat.card (Fin 4) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← starFourGraph.edgeFinset_card]
    decide
  refine ⟨isTree_iff_connected_and_card.2 ⟨hconn, hcard⟩, fun v ↦ ?_⟩
  rw [degree_eq_degree starFourGraph v _ inferInstance]
  fin_cases v <;> decide

/-- The 4-vertex tree-labelling when there are three efficient sets `X₁, X₂, X₃` with
`X₁ ∪ X₂ ∪ X₃ = E`, each a subset of a member of `𝒜`
(Graph Minors X, Section 3, proof of (3.4), page 162). -/
theorem exists_isTreeLabelling_of_three_sets {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    (hκ : IsConnectivityFunction E κ) (h𝒜 : ∀ A ∈ 𝒜, IsEfficient E κ A)
    {X₁ X₂ X₃ : Set β}
    (heff₁ : IsEfficient E κ X₁) (heff₂ : IsEfficient E κ X₂) (heff₃ : IsEfficient E κ X₃)
    (hsub₁ : ∃ A ∈ 𝒜, X₁ ⊆ A) (hsub₂ : ∃ A ∈ 𝒜, X₂ ⊆ A) (hsub₃ : ∃ A ∈ 𝒜, X₃ ⊆ A)
    (hunion : X₁ ∪ X₂ ∪ X₃ = E) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
      IsTreeLabelling E κ 𝒜 T α := by
  let X : Fin 4 → Set β := fun i ↦
    if i = 1 then X₁ else if i = 2 then X₂ else if i = 3 then X₃ else ∅
  have hX_eff : ∀ i : Fin 4, i ≠ 0 → IsEfficient E κ (X i) := by
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact heff₁
    · exact heff₂
    · exact heff₃
  have hX_sub : ∀ i : Fin 4, i ≠ 0 → ∃ A ∈ 𝒜, X i ⊆ A := by
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact hsub₁
    · exact hsub₂
    · exact hsub₃
  let α : Fin 4 → Sym2 (Fin 4) → Set β := fun v e ↦
    if v = 0 then
      if e = s(0, 1) then X₁ else if e = s(0, 2) then X₂ else X₃
    else
      E \ X v
  have hα0 : ∀ i : Fin 4, i ≠ 0 → α 0 s(0, i) = X i := by
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · simp [α, X]
    · simp [α, X]
    · simp [α, X]
  refine ⟨Fin 4, inferInstance, starFourGraph, α, isTernaryTree_starFourGraph, ?_, ?_, ?_, ?_⟩
  · intro v e hinc
    obtain ⟨w, hadj, rfl⟩ := isTreeIncidence_iff_exists_adj.1 hinc
    rcases hadj with ⟨rfl, hw⟩ | ⟨rfl, hv⟩
    · rw [hα0 w hw]
      exact hX_eff w hw
    · have : α v s(v, 0) = E \ X v := by simp [α, hv]
      rw [this]
      exact (hX_eff v hv).compl hκ
  · intro u v hadj
    rcases hadj with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
    · have h1 : α 0 s(0, v) = X v := hα0 v hv
      have h2 : α v s(0, v) = E \ X v := by simp [α, hv]
      rw [h1, h2, Set.sdiff_sdiff_cancel_left (hX_eff v hv).1]
    · have h1 : α u s(u, 0) = E \ X u := by simp [α, hu]
      have h2 : α 0 s(u, 0) = X u := by
        rw [Sym2.eq_swap]
        exact hα0 u hu
      rw [h1, h2]
  · intro v e hinc hleaf
    have hv0 : v ≠ 0 := by
      rintro rfl
      have hdeg3 : starFourGraph.degree (0 : Fin 4) = 3 := by decide
      dsimp [IsLeaf] at hleaf
      rw [degree_eq_degree starFourGraph 0 _ inferInstance] at hleaf
      omega
    have hαv : α v e = E \ X v := by simp [α, hv0]
    obtain ⟨A, hA_mem, hXA⟩ := hX_sub v hv0
    right
    refine ⟨A, hA_mem, ?_⟩
    rw [hαv]
    refine Set.Subset.antisymm (Set.union_subset Set.sdiff_subset (h𝒜 A hA_mem).1) ?_
    intro y hy
    by_cases hyX : y ∈ X v
    · exact Or.inr (hXA hyX)
    · exact Or.inl ⟨hy, hyX⟩
  · intro v e₁ e₂ e₃ h₁ h₂ h₃ h12 h13 h23
    have hv0 : v = 0 := by
      by_contra hv0
      obtain ⟨w₁, hw₁, rfl⟩ := isTreeIncidence_iff_exists_adj.1 h₁
      obtain ⟨w₂, hw₂, rfl⟩ := isTreeIncidence_iff_exists_adj.1 h₂
      have hw₁0 : w₁ = 0 := by
        rcases hw₁ with ⟨h, _⟩ | ⟨h, _⟩
        · exact (hv0 h).elim
        · exact h
      have hw₂0 : w₂ = 0 := by
        rcases hw₂ with ⟨h, _⟩ | ⟨h, _⟩
        · exact (hv0 h).elim
        · exact h
      exact h12 (by rw [hw₁0, hw₂0])
    subst hv0
    obtain ⟨w₁, hw₁, rfl⟩ := isTreeIncidence_iff_exists_adj.1 h₁
    obtain ⟨w₂, hw₂, rfl⟩ := isTreeIncidence_iff_exists_adj.1 h₂
    obtain ⟨w₃, hw₃, rfl⟩ := isTreeIncidence_iff_exists_adj.1 h₃
    have hw₁_ne : w₁ ≠ 0 := by
      rcases hw₁ with ⟨_, h⟩ | ⟨_, h⟩
      · exact h
      · exact (h rfl).elim
    have hw₂_ne : w₂ ≠ 0 := by
      rcases hw₂ with ⟨_, h⟩ | ⟨_, h⟩
      · exact h
      · exact (h rfl).elim
    have hw₃_ne : w₃ ≠ 0 := by
      rcases hw₃ with ⟨_, h⟩ | ⟨_, h⟩
      · exact h
      · exact (h rfl).elim
    have hne12 : w₁ ≠ w₂ := fun h ↦ h12 (by rw [h])
    have hne13 : w₁ ≠ w₃ := fun h ↦ h13 (by rw [h])
    have hne23 : w₂ ≠ w₃ := fun h ↦ h23 (by rw [h])
    rw [hα0 w₁ hw₁_ne, hα0 w₂ hw₂_ne, hα0 w₃ hw₃_ne]
    have hmem_123 : ∀ w : Fin 4, w ≠ 0 → w ∈ ({1, 2, 3} : Finset (Fin 4)) := by
      intro w hw
      fin_cases w
      · exact (hw rfl).elim
      · decide
      · decide
      · decide
    have hset : ({w₁, w₂, w₃} : Finset (Fin 4)) = {1, 2, 3} := by
      have hsub : ({w₁, w₂, w₃} : Finset (Fin 4)) ⊆ {1, 2, 3} := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with h | h | h
        · rw [h]; exact hmem_123 w₁ hw₁_ne
        · rw [h]; exact hmem_123 w₂ hw₂_ne
        · rw [h]; exact hmem_123 w₃ hw₃_ne
      have hcard : ({w₁, w₂, w₃} : Finset (Fin 4)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] <;>
          simp [hne12, hne13, hne23]
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; decide)
    have h1_mem : (1 : Fin 4) ∈ ({w₁, w₂, w₃} : Finset (Fin 4)) := by rw [hset]; decide
    have h2_mem : (2 : Fin 4) ∈ ({w₁, w₂, w₃} : Finset (Fin 4)) := by rw [hset]; decide
    have h3_mem : (3 : Fin 4) ∈ ({w₁, w₂, w₃} : Finset (Fin 4)) := by rw [hset]; decide
    refine Set.Subset.antisymm
      (Set.union_subset (Set.union_subset (hX_eff w₁ hw₁_ne).1 (hX_eff w₂ hw₂_ne).1)
        (hX_eff w₃ hw₃_ne).1) ?_
    rw [← hunion]
    have hsub_i : ∀ i : Fin 4, i ∈ ({w₁, w₂, w₃} : Finset (Fin 4)) →
        X i ⊆ X w₁ ∪ X w₂ ∪ X w₃ := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact Set.subset_union_of_subset_left Set.subset_union_left _
      · exact Set.subset_union_of_subset_left Set.subset_union_right _
      · exact Set.subset_union_right
    exact Set.union_subset (Set.union_subset (hsub_i 1 h1_mem) (hsub_i 2 h2_mem))
      (hsub_i 3 h3_mem)

/-! ## Vertex-leaf suppression for (3.6) -/

private abbrev PrunedVertices (v₀ v : ι) := {u : ι // u ≠ v₀ ∧ u ≠ v}

/-- Paths in the original tree reach the new bridging edge after deleting the leaf and its
neighbor. -/
private theorem prunedTree_connected {T : SimpleGraph ι} (hT : T.IsTree)
    {v₀ v v₁ v₂ : ι} (hv₀_adj_iff : ∀ x, T.Adj v₀ x ↔ x = v)
    (hv_adj_iff : ∀ x, T.Adj v x ↔ x = v₀ ∨ x = v₁ ∨ x = v₂)
    (h₁ : v₁ ≠ v₀ ∧ v₁ ≠ v) (h₂ : v₂ ≠ v₀ ∧ v₂ ≠ v)
    {T' : SimpleGraph (PrunedVertices v₀ v)}
    (hsub : T.induce {u | u ≠ v₀ ∧ u ≠ v} ≤ T')
    (hbridge : T'.Adj ⟨v₂, h₂⟩ ⟨v₁, h₁⟩) : T'.Connected := by
  classical
  let S : Set ι := {u | u ≠ v₀ ∧ u ≠ v}
  let v₁' : S := ⟨v₁, h₁⟩
  let v₂' : S := ⟨v₂, h₂⟩
  let G₀ : SimpleGraph S := T.induce S
  have : Nonempty S := ⟨v₁'⟩
  refine Connected.mk fun u' w' ↦ ?_
  suffices ∀ x' : S, T'.Reachable x' v₁' from (this u').trans (this w').symm
  intro x'
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath x'.1 v
  have hnot_nil : ¬ p.Nil := Walk.not_nil_of_ne x'.2.2
  let z := p.penultimate
  have hadj_z : T.Adj z v := p.adj_penultimate hnot_nil
  let q : T.Walk x'.1 z := p.dropLast
  have hp_supp : q.support ++ [v] = p.support := p.support_dropLast_concat hnot_nil
  have hnodup : (q.support ++ [v]).Nodup := hp_supp.symm ▸ hp.support_nodup
  have hv_not_q : v ∉ q.support := fun hv_q ↦
    List.disjoint_of_nodup_append hnodup hv_q (List.mem_singleton_self v)
  have hv₀_not_q : v₀ ∉ q.support := by
    intro hv₀_q
    let q₁ := q.takeUntil v₀ hv₀_q
    have hq₁_not_nil : ¬ q₁.Nil := Walk.not_nil_of_ne x'.2.1
    have hadj_pen : T.Adj q₁.penultimate v₀ := q₁.adj_penultimate hq₁_not_nil
    have hpen_eq_v : q₁.penultimate = v := (hv₀_adj_iff _).1 hadj_pen.symm
    have hv_in_q₁ : v ∈ q₁.support := hpen_eq_v ▸ q₁.getVert_mem_support (q₁.length - 1)
    exact hv_not_q (q.support_takeUntil_subset_support hv₀_q hv_in_q₁)
  have hq_in_S : ∀ y ∈ q.support, y ∈ S := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rintro rfl; exact hv₀_not_q hy
    · rintro rfl; exact hv_not_q hy
  rcases (hv_adj_iff z).1 hadj_z.symm with hzv₀ | hzv₁ | hzv₂
  · exact (hv₀_not_q (hzv₀ ▸ q.end_mem_support)).elim
  · have hreach_G₀ : G₀.Reachable x' v₁' :=
      ⟨(q.induce S hq_in_S).copy (Subtype.ext rfl) (Subtype.ext hzv₁)⟩
    exact hreach_G₀.mono hsub
  · have hreach_G₀ : G₀.Reachable x' v₂' :=
      ⟨(q.induce S hq_in_S).copy (Subtype.ext rfl) (Subtype.ext hzv₂)⟩
    exact (hreach_G₀.mono hsub).trans hbridge.reachable

private noncomputable def restoredNeighbor {v₀ v : ι}
    (v₁' v₂' u' w' : PrunedVertices v₀ v) : ι := by
  classical
  exact if (u' = v₁' ∧ w' = v₂') ∨ (u' = v₂' ∧ w' = v₁') then v else w'.1

/-- The new bridge restores the deleted middle vertex at either of its endpoints. -/
private noncomputable def prunedTree_neighborEquiv {T : SimpleGraph ι} {v₀ v v₁ v₂ : ι}
    (hv₀_adj_iff : ∀ x, T.Adj v₀ x ↔ x = v)
    (hv_adj_iff : ∀ x, T.Adj v x ↔ x = v₀ ∨ x = v₁ ∨ x = v₂)
    (hadj₁ : T.Adj v v₁) (hadj₂ : T.Adj v v₂) (hnot_adj12 : ¬ T.Adj v₁ v₂)
    (h₁ : v₁ ≠ v₀ ∧ v₁ ≠ v) (h₂ : v₂ ≠ v₀ ∧ v₂ ≠ v)
    (hv12' : v₁ ≠ v₂) {T' : SimpleGraph (PrunedVertices v₀ v)}
    (hadj_T'_iff : ∀ u' w' : PrunedVertices v₀ v,
      T'.Adj u' w' ↔ T.Adj u'.1 w'.1 ∨
        (u'.1 = v₁ ∧ w'.1 = v₂) ∨ (u'.1 = v₂ ∧ w'.1 = v₁)) :
    ∀ u' : PrunedVertices v₀ v, {w' // T'.Adj u' w'} ≃ {w // T.Adj u'.1 w} := by
  classical
  let S := PrunedVertices v₀ v
  let v₁' : S := ⟨v₁, h₁⟩
  let v₂' : S := ⟨v₂, h₂⟩
  have hv12'' : v₁' ≠ v₂' := fun heq => hv12' (congrArg Subtype.val heq)
  let origNeighbor := restoredNeighbor v₁' v₂'
  have hadj_iff (u' w' : S) :
      T'.Adj u' w' ↔ T.Adj u'.1 w'.1 ∨
        (u' = v₁' ∧ w' = v₂') ∨ (u' = v₂' ∧ w' = v₁') := by
    have hleft (x : S) : x.1 = v₁ ↔ x = v₁' :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    have hright (x : S) : x.1 = v₂ ↔ x = v₂' :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simpa only [hleft, hright] using hadj_T'_iff u' w'
  let invNeighbor (u' : S) (w : ι) : S :=
    if hw : w ≠ v₀ ∧ w ≠ v then ⟨w, hw⟩ else if u' = v₁' then v₂' else v₁'
  have horig_adj : ∀ (u' w' : S), T'.Adj u' w' → T.Adj u'.1 (origNeighbor u' w') := by
    intro u' w' hw'
    dsimp [origNeighbor, restoredNeighbor]
    split_ifs with h
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj₁.symm
      · exact hadj₂.symm
    · rcases (hadj_iff u' w').1 hw' with hadj | h1 | h2
      · exact hadj
      · exact (h (Or.inl h1)).elim
      · exact (h (Or.inr h2)).elim
  have hinv_adj : ∀ (u' : S) (w : ι), T.Adj u'.1 w → T'.Adj u' (invNeighbor u' w) := by
    intro u' w hw
    dsimp [invNeighbor]
    split_ifs with hwS hu1
    · exact (hadj_iff _ _).2 (Or.inl hw)
    · exact (hadj_iff _ _).2 (Or.inr (Or.inl ⟨hu1, rfl⟩))
    · have hwv : w = v := by
        by_contra hne_v
        apply hwS
        refine ⟨?_, hne_v⟩
        rintro rfl
        exact u'.2.2 ((hv₀_adj_iff u'.1).1 hw.symm)
      subst hwv
      refine (hadj_iff _ _).2 (Or.inr (Or.inr ⟨?_, rfl⟩))
      rcases (hv_adj_iff u'.1).1 hw.symm with h0 | h1 | h2
      · exact (u'.2.1 h0).elim
      · exact (hu1 (Subtype.ext h1)).elim
      · exact Subtype.ext h2
  intro u'
  exact
    { toFun := fun ⟨w', hw'⟩ ↦ ⟨origNeighbor u' w', horig_adj u' w' hw'⟩
      invFun := fun ⟨w, hw⟩ ↦ ⟨invNeighbor u' w, hinv_adj u' w hw⟩
      left_inv := by
        rintro ⟨w', hw'⟩
        ext
        dsimp [origNeighbor, restoredNeighbor, invNeighbor]
        by_cases hpair : (u' = v₁' ∧ w' = v₂') ∨ (u' = v₂' ∧ w' = v₁')
        · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp
          · simp [hv12''.symm]
        · simp [hpair, w'.2.1, w'.2.2]
      right_inv := by
        rintro ⟨w, hw⟩
        ext
        dsimp [origNeighbor, restoredNeighbor, invNeighbor]
        by_cases hwS : w ≠ v₀ ∧ w ≠ v
        · have hnot_pair : ¬ ((u' = v₁' ∧ (⟨w, hwS⟩ : S) = v₂') ∨
              (u' = v₂' ∧ (⟨w, hwS⟩ : S) = v₁')) := by
            rintro (⟨rfl, heq⟩ | ⟨rfl, heq⟩)
            · have : w = v₂ := congrArg Subtype.val heq
              subst this
              exact hnot_adj12 hw
            · have : w = v₁ := congrArg Subtype.val heq
              subst this
              exact hnot_adj12 hw.symm
          simp [hwS, hnot_pair]
        · have hwv : w = v := by
            by_contra hne_v
            apply hwS
            refine ⟨?_, hne_v⟩
            rintro rfl
            exact u'.2.2 ((hv₀_adj_iff u'.1).1 hw.symm)
          subst hwv
          by_cases hu1 : u' = v₁'
          · subst hu1; simp
          · have hu2 : u' = v₂' := by
              rcases (hv_adj_iff u'.1).1 hw.symm with h0 | h1 | h2
              · exact (u'.2.1 h0).elim
              · exact (hu1 (Subtype.ext h1)).elim
              · exact Subtype.ext h2
            subst hu2
            simp [hv12''.symm] }

/-- Suppressing a leaf `v₀` with `α(v₀, e₀) = E` and its degree-3 neighbor `v` in an exact
tree-labelling produces an exact tree-labelling on a strictly smaller vertex type
(Graph Minors X, Section 3, proof of (3.6), pages 163–164). -/
theorem exists_smaller_exactTreeLabelling_of_leaf_eq [Fintype ι]
    {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (hα : IsExactTreeLabelling E κ 𝒜 T α)
    {v₀ v : ι} (hleaf₀ : IsLeaf T v₀) (hadj₀ : T.Adj v₀ v)
    (hα_v₀ : α v₀ s(v₀, v) = E) (hv_not_leaf : ¬ IsLeaf T v) :
    ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (α' : ι' → Sym2 ι' → Set β),
      Fintype.card ι' < Fintype.card ι ∧ IsExactTreeLabelling E κ 𝒜 T' α' := by
  classical
  have hT := hα.isTreeLabelling.isTernaryTree
  have hne_v₀v : v₀ ≠ v := hadj₀.ne
  obtain ⟨_, _, hv₀_uniq⟩ := hT.exists_adj_of_isLeaf hleaf₀
  have hv₀_adj_iff : ∀ x, T.Adj v₀ x ↔ x = v :=
    fun x ↦ ⟨fun hx ↦ (hv₀_uniq x hx).trans (hv₀_uniq v hadj₀).symm, fun hx ↦ hx.symm ▸ hadj₀⟩
  obtain ⟨v₁, v₂, hv₀1, hv₀2, hv12, hv_adj_iff⟩ :=
    hT.exists_other_two_adj hv_not_leaf hadj₀.symm
  have hadj₁ : T.Adj v v₁ := (hv_adj_iff v₁).2 (Or.inr (Or.inl rfl))
  have hadj₂ : T.Adj v v₂ := (hv_adj_iff v₂).2 (Or.inr (Or.inr rfl))
  have hv1_ne_v : v₁ ≠ v := hadj₁.ne.symm
  have hv2_ne_v : v₂ ≠ v := hadj₂.ne.symm
  -- `v₁` and `v₂` are not adjacent in `T` since `T` is a tree and `v` is adjacent to both.
  have hnot_adj12 : ¬ T.Adj v₁ v₂ := by
    intro hadj12
    let p₁ : T.Walk v₁ v₂ := Walk.cons hadj12 Walk.nil
    let p₂ : T.Walk v₁ v₂ := Walk.cons hadj₁.symm (Walk.cons hadj₂ Walk.nil)
    have hp₁ : p₁.IsPath := Walk.IsPath.nil.cons (by simp [hv12])
    have hp₂ : p₂.IsPath := by
      rw [Walk.cons_isPath_iff]
      refine ⟨Walk.IsPath.nil.cons (by simp [hadj₂.ne]), ?_⟩
      simp [hv1_ne_v, hv12]
    have heq : p₁ = p₂ :=
      congrArg Subtype.val ((hT.isTree.isAcyclic.subsingleton_path v₁ v₂).elim ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩)
    have hlen := congrArg Walk.length heq
    simp [p₁, p₂] at hlen
  -- Define the reduced vertex type `S = {u : ι | u ≠ v₀ ∧ u ≠ v}`.
  let S : Set ι := {u : ι | u ≠ v₀ ∧ u ≠ v}
  let v₁' : S := ⟨v₁, hv₀1.symm, hv1_ne_v⟩
  let v₂' : S := ⟨v₂, hv₀2.symm, hv2_ne_v⟩
  have hv12' : v₁' ≠ v₂' := fun h ↦ hv12 (Subtype.ext_iff.1 h)
  let G₀ : SimpleGraph S := T.induce S
  let T' : SimpleGraph S := G₀ ⊔ SimpleGraph.edge v₁' v₂'
  have hadj_T'_iff : ∀ u' w' : S,
      T'.Adj u' w' ↔ T.Adj u'.1 w'.1 ∨ (u' = v₁' ∧ w' = v₂') ∨ (u' = v₂' ∧ w' = v₁') := by
    intro u' w'
    simp only [T', G₀, sup_adj, SimpleGraph.edge_adj]
    change T.Adj u'.1 w'.1 ∨ _ ↔ _
    constructor
    · rintro (h | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hv12'⟩
      · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hv12'.symm⟩
  -- Step 1: `T'` is a tree.
  have hnot_reach_G₀ : ¬ G₀.Reachable v₁' v₂' := by
    rintro ⟨w⟩
    let q := w.toPath
    let embS : G₀ ↪g T := SimpleGraph.Embedding.induce S
    let qT := q.1.map embS.toHom
    have hqT_path : qT.IsPath := q.2.map embS.injective
    let p₂ : T.Walk v₁ v₂ := Walk.cons hadj₁.symm (Walk.cons hadj₂ Walk.nil)
    have hp₂ : p₂.IsPath := by
      rw [Walk.cons_isPath_iff]
      refine ⟨Walk.IsPath.nil.cons (by simp [hadj₂.ne]), ?_⟩
      simp [hv1_ne_v, hv12]
    have heq : qT = p₂ :=
      congrArg Subtype.val
        ((hT.isTree.isAcyclic.subsingleton_path v₁ v₂).elim ⟨qT, hqT_path⟩ ⟨p₂, hp₂⟩)
    have hv_mem : v ∈ (q.1.map embS.toHom).support := by
      change v ∈ qT.support
      rw [heq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    rw [Walk.support_map] at hv_mem
    obtain ⟨u', _, hu'_eq⟩ := List.mem_map.1 hv_mem
    exact u'.2.2 hu'_eq
  have hT'_acyc : T'.IsAcyclic :=
    (hT.isTree.isAcyclic.induce S).sup_edge_of_not_reachable hnot_reach_G₀
  have hT'_conn : T'.Connected :=
    prunedTree_connected hT.isTree hv₀_adj_iff hv_adj_iff ⟨hv₀1.symm, hv1_ne_v⟩
      ⟨hv₀2.symm, hv2_ne_v⟩ le_sup_left
      ((hadj_T'_iff v₂' v₁').2 (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  have hT'_tree : T'.IsTree := ⟨hT'_conn, hT'_acyc⟩
  let origNeighbor := restoredNeighbor v₁' v₂'
  let hneigh_equiv :=
    prunedTree_neighborEquiv hv₀_adj_iff hv_adj_iff hadj₁ hadj₂ hnot_adj12
      ⟨hv₀1.symm, hv1_ne_v⟩ ⟨hv₀2.symm, hv2_ne_v⟩ hv12
      (fun u' w' => by simpa only [Subtype.ext_iff] using hadj_T'_iff u' w')
  -- Step 3: Define `α'` and show it agrees with `origNeighbor`.
  let α' (u' : S) (f' : Sym2 S) : Set β :=
    if f' = s(v₁', v₂') then
      if u' = v₁' then α v₁ s(v₁, v) else α v₂ s(v₂, v)
    else
      α u'.1 (Sym2.map Subtype.val f')
  have hα'_eq : ∀ (u' w' : S) (hw' : T'.Adj u' w'),
      α' u' s(u', w') = α u'.1 s(u'.1, (hneigh_equiv u' ⟨w', hw'⟩).1) := by
    intro u' w' hw'
    change α' u' s(u', w') = α u'.1 s(u'.1, origNeighbor u' w')
    by_cases hpair : (u' = v₁' ∧ w' = v₂') ∨ (u' = v₂' ∧ w' = v₁')
    · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [α', origNeighbor, restoredNeighbor, v₁', v₂']
      · have hswap : s(v₂', v₁') = s(v₁', v₂') := Sym2.eq_swap
        simp [α', origNeighbor, restoredNeighbor, hswap, hv12'.symm, v₁', v₂']
    · have hne_edge : s(u', w') ≠ s(v₁', v₂') := by
        intro heq
        rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hpair (Or.inl ⟨h1, h2⟩)
        · exact hpair (Or.inr ⟨h1, h2⟩)
      simp [α', origNeighbor, restoredNeighbor, hpair, hne_edge]
  -- Step 4: Verify `IsExactTreeLabelling E κ 𝒜 T' α'`.
  have hT'_ternary : IsTernaryTree T' := by
    refine ⟨hT'_tree, fun u' ↦ ?_⟩
    rw [degree_eq_of_neighborEquiv (hneigh_equiv u')]
    exact hT.degree_eq_one_or_three u'.1
  -- Key relation on the suppressed vertex `v`: `α v₁ s(v₁, v) = E \ α v₂ s(v₂, v)`.
  have hα_v1_v2_compl : α v₁ s(v₁, v) = E \ α v₂ s(v₂, v) := by
    have hα_v_e₀ : α v s(v, v₀) = ∅ := by
      rw [hα.isTreeLabelling.compl_eq hadj₀.symm, Sym2.eq_swap, hα_v₀, Set.sdiff_self]
    have hinc0 : IsTreeIncidence T v s(v, v₀) := isTreeIncidence_iff_adj.2 hadj₀.symm
    have hinc1 : IsTreeIncidence T v s(v, v₁) := isTreeIncidence_iff_adj.2 hadj₁
    have hinc2 : IsTreeIncidence T v s(v, v₂) := isTreeIncidence_iff_adj.2 hadj₂
    have he01 : s(v, v₀) ≠ s(v, v₁) := sym2_mk_eq_left_iff.not.2 hv₀1
    have he02 : s(v, v₀) ≠ s(v, v₂) := sym2_mk_eq_left_iff.not.2 hv₀2
    have he12 : s(v, v₁) ≠ s(v, v₂) := sym2_mk_eq_left_iff.not.2 hv12
    obtain ⟨hunion_v, hinter_v⟩ :=
      hα.compl_eq_union_of_degree_three hinc0 hinc1 hinc2 he01 he02 he12
    rw [hα_v_e₀, Set.sdiff_empty] at hunion_v
    have h_v2_eq : α v s(v, v₂) = E \ α v s(v, v₁) := by
      ext x
      have hx_disj : x ∈ α v s(v, v₁) → x ∉ α v s(v, v₂) := fun h1 h2 ↦
        Set.notMem_empty x (hinter_v ▸ ⟨h1, h2⟩)
      simp only [Set.mem_sdiff]
      constructor
      · intro hx2
        exact ⟨hunion_v ▸ Or.inr hx2, fun hx1 ↦ hx_disj hx1 hx2⟩
      · rintro ⟨hxE, hx1⟩
        rw [← hunion_v] at hxE
        exact hxE.resolve_left hx1
    have h1 : α v₁ s(v₁, v) = E \ α v s(v, v₁) := by
      rw [hα.isTreeLabelling.compl_eq hadj₁.symm, Sym2.eq_swap]
    have h2 : E \ α v₂ s(v₂, v) = α v s(v, v₂) := by
      rw [hα.isTreeLabelling.compl_eq hadj₂.symm, Sym2.eq_swap,
        Set.sdiff_sdiff_cancel_left (hα.isTreeLabelling.subset_of_inc hinc2)]
    rw [h1, h2, h_v2_eq]
  have htree_lab' : IsTreeLabelling E κ 𝒜 T' α' := by
    refine ⟨hT'_ternary, ?_, ?_, ?_, ?_⟩
    · intro u' f' hf'
      obtain ⟨w', hw', rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf'
      rw [hα'_eq u' w' hw']
      exact hα.isTreeLabelling.isEfficient
        (isTreeIncidence_iff_adj.2 (hneigh_equiv u' ⟨w', hw'⟩).2)
    · intro u' w' hw'
      by_cases hpair : (u' = v₁' ∧ w' = v₂') ∨ (u' = v₂' ∧ w' = v₁')
      · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [α', ↓reduceIte, hv12'.symm]
          exact hα_v1_v2_compl
        · have hswap : s(v₂', v₁') = s(v₁', v₂') := Sym2.eq_swap
          simp only [α', hswap, ↓reduceIte, hv12'.symm]
          rw [hα_v1_v2_compl, Set.sdiff_sdiff_cancel_left
            (hα.isTreeLabelling.subset_of_inc (isTreeIncidence_iff_adj.2 hadj₂.symm))]
      · have hne_edge : s(u', w') ≠ s(v₁', v₂') := by
          intro heq
          rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hpair (Or.inl ⟨h1, h2⟩)
          · exact hpair (Or.inr ⟨h1, h2⟩)
        have hadj_u_w : T.Adj u'.1 w'.1 :=
          ((hadj_T'_iff u' w').1 hw').resolve_right hpair
        simp only [α', hne_edge, ↓reduceIte]
        exact hα.isTreeLabelling.compl_eq hadj_u_w
    · intro u' f' hf' hleaf'
      obtain ⟨w', hw', rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf'
      rw [hα'_eq u' w' hw']
      have hleaf_u : IsLeaf T u'.1 := (isLeaf_iff_of_neighborEquiv (hneigh_equiv u')).1 hleaf'
      exact hα.isTreeLabelling.leaf_eq_or_union_eq
        (isTreeIncidence_iff_adj.2 (hneigh_equiv u' ⟨w', hw'⟩).2) hleaf_u
    · intro u' f₁' f₂' f₃' hf₁' hf₂' hf₃' h12' h13' h23'
      exact degree_three_union_eq_of_neighborEquiv hα.isTreeLabelling (hneigh_equiv u')
        (fun w' hw' ↦ (hα'_eq u' w' hw').symm.subset)
        (fun w' hw' ↦ (hα'_eq u' w' hw').subset.trans
          (hα.isTreeLabelling.subset_of_inc
            (isTreeIncidence_iff_adj.2 (hneigh_equiv u' ⟨w', hw'⟩).2)))
        hf₁' hf₂' hf₃' h12' h13' h23'
  have hexact' : IsExactTreeLabelling E κ 𝒜 T' α' := by
    refine ⟨htree_lab', fun u' f₁' f₂' hf' ↦ ?_⟩
    exact isExactFork_of_neighborEquiv (hneigh_equiv u') (hα'_eq u')
      (fun _ _ hf ↦ hα.isExactFork hf) hf'
  have hcard_lt : Fintype.card S < Fintype.card ι :=
    Fintype.card_subtype_lt (x := v₀) (fun h ↦ h.1 rfl)
  let eFin := Fintype.equivFin S
  refine ⟨Fin (Fintype.card S), inferInstance, T'.map eFin.toEmbedding,
    fun v e ↦ α' (eFin.symm v) (e.map eFin.symm), ?_, hexact'.relabel eFin⟩
  simpa using hcard_lt

/-! ## Tree-splicing for (3.4) -/

private abbrev SplicedVert {ι₂ ι₁ : Type*} (t₁ : ι₂) (t₀ : ι₁) : Type _ :=
  {v : ι₂ // v ≠ t₁} ⊕ {u : ι₁ // u ≠ t₀}

private def splicedBaseGraph {ι₂ ι₁ : Type*} (T₂ : SimpleGraph ι₂) (T₁ : SimpleGraph ι₁)
    (t₁ : ι₂) (t₀ : ι₁) : SimpleGraph (SplicedVert t₁ t₀) where
  Adj a b :=
    match a, b with
    | Sum.inl u, Sum.inl v => T₂.Adj u.1 v.1
    | Sum.inr u, Sum.inr v => T₁.Adj u.1 v.1
    | _, _ => False
  symm := ⟨by
    rintro (u | u) (v | v) h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨by
    rintro (u | u) h
    · exact T₂.loopless.irrefl u.1 h
    · exact T₁.loopless.irrefl u.1 h⟩

private def splicedTree {ι₂ ι₁ : Type*} (T₂ : SimpleGraph ι₂) (T₁ : SimpleGraph ι₁)
    {t₁ w₁ : ι₂} {t₀ s : ι₁} (hw₁ : w₁ ≠ t₁) (hs : s ≠ t₀) :
    SimpleGraph (SplicedVert t₁ t₀) :=
  splicedBaseGraph T₂ T₁ t₁ t₀ ⊔
    SimpleGraph.edge (Sum.inl ⟨w₁, hw₁⟩) (Sum.inr ⟨s, hs⟩)

private theorem splicedTree_adj_iff {ι₂ ι₁ : Type*} {T₂ : SimpleGraph ι₂} {T₁ : SimpleGraph ι₁}
    {t₁ w₁ : ι₂} {t₀ s : ι₁} (hw₁ : w₁ ≠ t₁) (hs : s ≠ t₀)
    (x y : SplicedVert t₁ t₀) :
    (splicedTree T₂ T₁ hw₁ hs).Adj x y ↔
      (splicedBaseGraph T₂ T₁ t₁ t₀).Adj x y ∨
        (x = Sum.inl ⟨w₁, hw₁⟩ ∧ y = Sum.inr ⟨s, hs⟩) ∨
        (x = Sum.inr ⟨s, hs⟩ ∧ y = Sum.inl ⟨w₁, hw₁⟩) := by
  simp only [splicedTree, sup_adj, SimpleGraph.edge_adj]
  constructor
  · rintro (h | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, Sum.inl_ne_inr⟩
    · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, Sum.inr_ne_inl⟩

private theorem splicedTree_connected {ι₂ ι₁ : Type*} [Fintype ι₂] [Fintype ι₁]
    {T₂ : SimpleGraph ι₂} {T₁ : SimpleGraph ι₁}
    (hT₂ : IsTernaryTree T₂) (hT₁ : IsTernaryTree T₁)
    {t₁ w₁ : ι₂} {t₀ s : ι₁}
    (ht₁_leaf : IsLeaf T₂ t₁) (ht₀_leaf : IsLeaf T₁ t₀)
    (hw₁ : w₁ ≠ t₁) (hs : s ≠ t₀) :
    (splicedTree T₂ T₁ hw₁ hs).Connected := by
  classical
  let w₁' : {v : ι₂ // v ≠ t₁} := ⟨w₁, hw₁⟩
  let s' : {u : ι₁ // u ≠ t₀} := ⟨s, hs⟩
  have hT₂'_conn : (T₂.induce {t₁}ᶜ).Connected :=
    hT₂.isTree.connected.induce_compl_singleton_of_degree_eq_one
      (hT₂.degree_eq_one_of_isLeaf ht₁_leaf)
  have hT₁'_conn : (T₁.induce {t₀}ᶜ).Connected :=
    hT₁.isTree.connected.induce_compl_singleton_of_degree_eq_one
      (hT₁.degree_eq_one_of_isLeaf ht₀_leaf)
  let emb₂ : T₂.induce {t₁}ᶜ ↪g splicedBaseGraph T₂ T₁ t₁ t₀ :=
    { toFun := Sum.inl, inj' := Sum.inl_injective, map_rel_iff' := Iff.rfl }
  let emb₁ : T₁.induce {t₀}ᶜ ↪g splicedBaseGraph T₂ T₁ t₁ t₀ :=
    { toFun := Sum.inr, inj' := Sum.inr_injective, map_rel_iff' := Iff.rfl }
  have : Nonempty (SplicedVert t₁ t₀) := ⟨Sum.inl w₁'⟩
  refine Connected.mk fun x y ↦ ?_
  have hreach_w₁' : ∀ z : SplicedVert t₁ t₀,
      (splicedTree T₂ T₁ hw₁ hs).Reachable z (Sum.inl w₁') := by
    intro z
    cases z with
    | inl v =>
      exact ((hT₂'_conn v w₁').map emb₂.toHom).mono le_sup_left
    | inr u =>
      have h1 : (splicedTree T₂ T₁ hw₁ hs).Reachable (Sum.inr u) (Sum.inr s') :=
        ((hT₁'_conn u s').map emb₁.toHom).mono le_sup_left
      have hadj_bridge : (splicedTree T₂ T₁ hw₁ hs).Adj (Sum.inr s') (Sum.inl w₁') :=
        (splicedTree_adj_iff hw₁ hs _ _).2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
      exact h1.trans hadj_bridge.reachable
  exact (hreach_w₁' x).trans (hreach_w₁' y).symm

private def splicedToNeighbor₂ {ι₂ ι₁ : Type*} (t₁ : ι₂) {t₀ : ι₁}
    (z : SplicedVert t₁ t₀) : ι₂ :=
  match z with
  | Sum.inl w => w.1
  | Sum.inr _ => t₁

private def splicedToNeighbor₁ {ι₂ ι₁ : Type*} {t₁ : ι₂} (t₀ : ι₁)
    (z : SplicedVert t₁ t₀) : ι₁ :=
  match z with
  | Sum.inr w => w.1
  | Sum.inl _ => t₀

private theorem exists_spliced_neighborEquiv₂ {ι₂ ι₁ : Type*} [Fintype ι₂]
    {T₂ : SimpleGraph ι₂} {T₁ : SimpleGraph ι₁}
    {t₁ w₁ : ι₂} {t₀ s : ι₁}
    (ht₁_leaf : IsLeaf T₂ t₁) (hadj_t₁w₁ : T₂.Adj t₁ w₁)
    (hT₂ : IsTernaryTree T₂) (hw₁ : w₁ ≠ t₁) (hs : s ≠ t₀) :
    ∃ e : ∀ v : {v : ι₂ // v ≠ t₁},
        {z : SplicedVert t₁ t₀ // (splicedTree T₂ T₁ hw₁ hs).Adj (Sum.inl v) z} ≃
          {w : ι₂ // T₂.Adj v.1 w},
      ∀ (v : {v : ι₂ // v ≠ t₁}) (z : SplicedVert t₁ t₀)
        (hz : (splicedTree T₂ T₁ hw₁ hs).Adj (Sum.inl v) z),
        (e v ⟨z, hz⟩).1 = splicedToNeighbor₂ t₁ z := by
  classical
  obtain ⟨_, _, ht₁_uniq⟩ := hT₂.exists_adj_of_isLeaf ht₁_leaf
  have ht₁_adj_iff : ∀ v, T₂.Adj t₁ v ↔ v = w₁ :=
    fun v ↦ ⟨fun hv ↦ (ht₁_uniq v hv).trans (ht₁_uniq w₁ hadj_t₁w₁).symm,
      fun hv ↦ hv.symm ▸ hadj_t₁w₁⟩
  let invNeighbor₂ (w : ι₂) : SplicedVert t₁ t₀ :=
    if hw : w ≠ t₁ then Sum.inl ⟨w, hw⟩ else Sum.inr ⟨s, hs⟩
  have hto₂_adj : ∀ (v : {v : ι₂ // v ≠ t₁}) (z : SplicedVert t₁ t₀),
      (splicedTree T₂ T₁ hw₁ hs).Adj (Sum.inl v) z → T₂.Adj v.1 (splicedToNeighbor₂ t₁ z) := by
    intro v z hz
    rcases (splicedTree_adj_iff hw₁ hs (Sum.inl v) z).1 hz with hG₀ | ⟨h1, h2⟩ | ⟨h1, _⟩
    · rcases z with w | u
      · exact hG₀
      · exact hG₀.elim
    · injection h1 with hv_eq
      subst hv_eq
      subst h2
      exact hadj_t₁w₁.symm
    · cases h1
  have hinv₂_adj : ∀ (v : {v : ι₂ // v ≠ t₁}) (w : ι₂),
      T₂.Adj v.1 w → (splicedTree T₂ T₁ hw₁ hs).Adj (Sum.inl v) (invNeighbor₂ w) := by
    intro v w hw
    by_cases hwt₁ : w = t₁
    · rw [hwt₁] at hw ⊢
      have hveq : v = ⟨w₁, hw₁⟩ := Subtype.ext ((ht₁_adj_iff v.1).1 hw.symm)
      have hinv : invNeighbor₂ t₁ = Sum.inr ⟨s, hs⟩ := by simp [invNeighbor₂]
      rw [hveq, hinv]
      exact (splicedTree_adj_iff hw₁ hs _ _).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · have hinv : invNeighbor₂ w = Sum.inl ⟨w, hwt₁⟩ := by simp [invNeighbor₂, hwt₁]
      rw [hinv]
      exact (splicedTree_adj_iff hw₁ hs _ _).2 (Or.inl hw)
  refine ⟨fun v ↦
    { toFun := fun ⟨z, hz⟩ ↦ ⟨splicedToNeighbor₂ t₁ z, hto₂_adj v z hz⟩
      invFun := fun ⟨w, hw⟩ ↦ ⟨invNeighbor₂ w, hinv₂_adj v w hw⟩
      left_inv := ?_
      right_inv := ?_ }, fun _ _ _ ↦ rfl⟩
  · rintro ⟨z, hz⟩
    ext
    dsimp [splicedToNeighbor₂, invNeighbor₂]
    rcases (splicedTree_adj_iff hw₁ hs (Sum.inl v) z).1 hz with hG₀ | ⟨_, rfl⟩ | ⟨h1, _⟩
    · rcases z with w | u
      · simp [w.2]
      · exact hG₀.elim
    · simp
    · cases h1
  · rintro ⟨w, hw⟩
    ext
    dsimp [splicedToNeighbor₂, invNeighbor₂]
    by_cases hwt₁ : w ≠ t₁
    · simp [hwt₁]
    · have hweq : w = t₁ := not_ne_iff.1 hwt₁
      subst hweq
      simp

private theorem exists_spliced_neighborEquiv₁ {ι₂ ι₁ : Type*} [Fintype ι₁]
    {T₂ : SimpleGraph ι₂} {T₁ : SimpleGraph ι₁}
    {t₁ w₁ : ι₂} {t₀ s : ι₁}
    (ht₀_leaf : IsLeaf T₁ t₀) (hadj_t₀s : T₁.Adj t₀ s)
    (hT₁ : IsTernaryTree T₁) (hw₁ : w₁ ≠ t₁) (hs : s ≠ t₀) :
    ∃ e : ∀ u : {u : ι₁ // u ≠ t₀},
        {z : SplicedVert t₁ t₀ // (splicedTree T₂ T₁ hw₁ hs).Adj (Sum.inr u) z} ≃
          {w : ι₁ // T₁.Adj u.1 w},
      ∀ (u : {u : ι₁ // u ≠ t₀}) (z : SplicedVert t₁ t₀)
        (hz : (splicedTree T₂ T₁ hw₁ hs).Adj (Sum.inr u) z),
        (e u ⟨z, hz⟩).1 = splicedToNeighbor₁ t₀ z := by
  classical
  obtain ⟨_, _, ht₀_uniq⟩ := hT₁.exists_adj_of_isLeaf ht₀_leaf
  have ht₀_adj_iff : ∀ u, T₁.Adj t₀ u ↔ u = s :=
    fun u ↦ ⟨fun hu ↦ (ht₀_uniq u hu).trans (ht₀_uniq s hadj_t₀s).symm,
      fun hu ↦ hu.symm ▸ hadj_t₀s⟩
  let invNeighbor₁ (w : ι₁) : SplicedVert t₁ t₀ :=
    if hw : w ≠ t₀ then Sum.inr ⟨w, hw⟩ else Sum.inl ⟨w₁, hw₁⟩
  have hto₁_adj : ∀ (u : {u : ι₁ // u ≠ t₀}) (z : SplicedVert t₁ t₀),
      (splicedTree T₂ T₁ hw₁ hs).Adj (Sum.inr u) z → T₁.Adj u.1 (splicedToNeighbor₁ t₀ z) := by
    intro u z hz
    rcases (splicedTree_adj_iff hw₁ hs (Sum.inr u) z).1 hz with hG₀ | ⟨h1, _⟩ | ⟨h1, h2⟩
    · rcases z with v | w
      · exact hG₀.elim
      · exact hG₀
    · cases h1
    · injection h1 with hu_eq
      subst hu_eq
      subst h2
      exact hadj_t₀s.symm
  have hinv₁_adj : ∀ (u : {u : ι₁ // u ≠ t₀}) (w : ι₁),
      T₁.Adj u.1 w → (splicedTree T₂ T₁ hw₁ hs).Adj (Sum.inr u) (invNeighbor₁ w) := by
    intro u w hw
    by_cases hwt₀ : w = t₀
    · rw [hwt₀] at hw ⊢
      have hueq : u = ⟨s, hs⟩ := Subtype.ext ((ht₀_adj_iff u.1).1 hw.symm)
      have hinv : invNeighbor₁ t₀ = Sum.inl ⟨w₁, hw₁⟩ := by simp [invNeighbor₁]
      rw [hueq, hinv]
      exact (splicedTree_adj_iff hw₁ hs _ _).2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · have hinv : invNeighbor₁ w = Sum.inr ⟨w, hwt₀⟩ := by simp [invNeighbor₁, hwt₀]
      rw [hinv]
      exact (splicedTree_adj_iff hw₁ hs _ _).2 (Or.inl hw)
  refine ⟨fun u ↦
    { toFun := fun ⟨z, hz⟩ ↦ ⟨splicedToNeighbor₁ t₀ z, hto₁_adj u z hz⟩
      invFun := fun ⟨w, hw⟩ ↦ ⟨invNeighbor₁ w, hinv₁_adj u w hw⟩
      left_inv := ?_
      right_inv := ?_ }, fun _ _ _ ↦ rfl⟩
  · rintro ⟨z, hz⟩
    ext
    dsimp [splicedToNeighbor₁, invNeighbor₁]
    rcases (splicedTree_adj_iff hw₁ hs (Sum.inr u) z).1 hz with hG₀ | ⟨h1, _⟩ | ⟨_, rfl⟩
    · rcases z with v | w
      · exact hG₀.elim
      · simp [w.2]
    · cases h1
    · simp
  · rintro ⟨w, hw⟩
    ext
    dsimp [splicedToNeighbor₁, invNeighbor₁]
    by_cases hwt₀ : w ≠ t₀
    · simp [hwt₀]
    · have hweq : w = t₀ := not_ne_iff.1 hwt₀
      subst hweq
      simp

private theorem card_subtype_ne_add_one {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    Fintype.card {x : α // x ≠ a} + 1 = Fintype.card α := by
  have h := Fintype.card_subtype_compl (fun x : α ↦ x = a)
  have h1 : Fintype.card {x : α // x = a} = 1 := Fintype.card_unique
  have hpos : 1 ≤ Fintype.card α := Fintype.card_pos_iff.2 ⟨a⟩
  change Fintype.card {x : α // x ≠ a} = Fintype.card α - Fintype.card {x : α // x = a} at h
  omega

private theorem splicedTree_isTernaryTree {ι₂ ι₁ : Type*} [Fintype ι₂] [Fintype ι₁]
    [DecidableEq ι₂] [DecidableEq ι₁]
    {T₂ : SimpleGraph ι₂} {T₁ : SimpleGraph ι₁}
    (hT₂ : IsTernaryTree T₂) (hT₁ : IsTernaryTree T₁)
    {t₁ w₁ : ι₂} {t₀ s : ι₁}
    (ht₁_leaf : IsLeaf T₂ t₁) (ht₀_leaf : IsLeaf T₁ t₀)
    (hw₁ : w₁ ≠ t₁) (hs : s ≠ t₀)
    (hneigh₂ : ∀ v : {v : ι₂ // v ≠ t₁},
      {z : SplicedVert t₁ t₀ // (splicedTree T₂ T₁ hw₁ hs).Adj (Sum.inl v) z} ≃
        {w : ι₂ // T₂.Adj v.1 w})
    (hneigh₁ : ∀ u : {u : ι₁ // u ≠ t₀},
      {z : SplicedVert t₁ t₀ // (splicedTree T₂ T₁ hw₁ hs).Adj (Sum.inr u) z} ≃
        {w : ι₁ // T₁.Adj u.1 w}) :
    IsTernaryTree (splicedTree T₂ T₁ hw₁ hs) := by
  classical
  let T' := splicedTree T₂ T₁ hw₁ hs
  have hdeg_inl : ∀ v : {v : ι₂ // v ≠ t₁}, T'.degree (Sum.inl v) = T₂.degree v.1 := fun v ↦
    degree_eq_of_neighborEquiv (hneigh₂ v)
  have hdeg_inr : ∀ u : {u : ι₁ // u ≠ t₀}, T'.degree (Sum.inr u) = T₁.degree u.1 := fun u ↦
    degree_eq_of_neighborEquiv (hneigh₁ u)
  have hT'_tree : T'.IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨splicedTree_connected hT₂ hT₁ ht₁_leaf ht₀_leaf hw₁ hs, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← T'.edgeFinset_card,
      Fintype.card_sum]
    have hsum_T' : ∑ x : SplicedVert t₁ t₀, T'.degree x = 2 * T'.edgeFinset.card :=
      T'.sum_degrees_eq_twice_card_edges
    rw [Fintype.sum_sum_type, Finset.sum_congr rfl fun v _ ↦ hdeg_inl v,
      Finset.sum_congr rfl fun u _ ↦ hdeg_inr u] at hsum_T'
    have hsum₂ : (∑ v : {v : ι₂ // v ≠ t₁}, T₂.degree v.1) + T₂.degree t₁ =
        2 * T₂.edgeFinset.card := by
      rw [← T₂.sum_degrees_eq_twice_card_edges,
        ← Finset.sum_erase_add _ _ (Finset.mem_univ t₁)]
      congr 1
      refine Finset.sum_bij (fun v _ ↦ v.1) (fun v _ ↦ Finset.mem_erase.2 ⟨v.2, Finset.mem_univ _⟩)
        (fun _ _ _ _ h ↦ Subtype.ext h)
        (fun v hv ↦ ⟨⟨v, (Finset.mem_erase.1 hv).1⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ ↦ rfl)
    have hsum₁ : (∑ u : {u : ι₁ // u ≠ t₀}, T₁.degree u.1) + T₁.degree t₀ =
        2 * T₁.edgeFinset.card := by
      rw [← T₁.sum_degrees_eq_twice_card_edges,
        ← Finset.sum_erase_add _ _ (Finset.mem_univ t₀)]
      congr 1
      refine Finset.sum_bij (fun u _ ↦ u.1) (fun u _ ↦ Finset.mem_erase.2 ⟨u.2, Finset.mem_univ _⟩)
        (fun _ _ _ _ h ↦ Subtype.ext h)
        (fun u hu ↦ ⟨⟨u, (Finset.mem_erase.1 hu).1⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ ↦ rfl)
    have hdeg_t₁ : T₂.degree t₁ = 1 := hT₂.degree_eq_one_of_isLeaf ht₁_leaf
    have hdeg_t₀ : T₁.degree t₀ = 1 := hT₁.degree_eq_one_of_isLeaf ht₀_leaf
    have hcard_V₂ : Fintype.card {v : ι₂ // v ≠ t₁} + 1 = Fintype.card ι₂ :=
      card_subtype_ne_add_one t₁
    have hcard_V₁ : Fintype.card {u : ι₁ // u ≠ t₀} + 1 = Fintype.card ι₁ :=
      card_subtype_ne_add_one t₀
    have he₂ := hT₂.isTree.card_edgeFinset
    have he₁ := hT₁.isTree.card_edgeFinset
    clear * - hsum_T' hsum₂ hsum₁ hdeg_t₁ hdeg_t₀ hcard_V₂ hcard_V₁ he₂ he₁
    omega
  refine ⟨hT'_tree, fun x ↦ ?_⟩
  cases x with
  | inl v =>
    rw [hdeg_inl v]
    exact hT₂.degree_eq_one_or_three v.1
  | inr u =>
    rw [hdeg_inr u]
    exact hT₁.degree_eq_one_or_three u.1

/-- Splicing `S = T₁ \ t₀` (where `t₀` is the unique bad leaf of `T₁`, adjacent to a degree-3
vertex `s` with `α₁(s, e₀) = X`) onto a bad leaf `t₁` of `T₂` (with `X ⊆ α₂(t₁, e₁)`) produces a
tree-labelling `(T', α')` over `𝒜₂` with strictly fewer bad leaves for `𝒜`
(Graph Minors X, Section 3, proof of (3.4), pages 162–163). -/
theorem exists_spliced_treeLabelling {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {E X : Set β} {κ : Set β → ℤ} {𝒜 𝒜₁ 𝒜₂ : Set (Set β)}
    {T₁ : SimpleGraph ι₁} {α₁ : ι₁ → Sym2 ι₁ → Set β}
    {T₂ : SimpleGraph ι₂} {α₂ : ι₂ → Sym2 ι₂ → Set β}
    (h𝒜_sub : 𝒜 ⊆ 𝒜₂)
    (hα₁ : IsTreeLabelling E κ 𝒜₁ T₁ α₁) (hα₂ : IsTreeLabelling E κ 𝒜₂ T₂ α₂)
    {t₀ s : ι₁} (ht₀_leaf : IsLeaf T₁ t₀) (hadj_t₀s : T₁.Adj t₀ s)
    (hs_not_leaf : ¬ IsLeaf T₁ s) (hα₁_s : α₁ s s(s, t₀) = X)
    (ht₀_only_bad : ∀ u e, IsTreeIncidence T₁ u e → IsLeaf T₁ u → u ≠ t₀ →
      α₁ u e = E ∨ ∃ A ∈ 𝒜, α₁ u e ∪ A = E)
    {t₁ w₁ : ι₂} (ht₁_leaf : IsLeaf T₂ t₁) (hadj_t₁w₁ : T₂.Adj t₁ w₁)
    (ht₁_bad : ¬ (α₂ t₁ s(t₁, w₁) = E ∨ ∃ A ∈ 𝒜, α₂ t₁ s(t₁, w₁) ∪ A = E))
    (hX_sub : X ⊆ α₂ t₁ s(t₁, w₁)) :
    ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (α' : ι' → Sym2 ι' → Set β),
      IsTreeLabelling E κ 𝒜₂ T' α' ∧
      {u' : ι' | IsLeaf T' u' ∧
        ∃ e', IsTreeIncidence T' u' e' ∧ ¬ (α' u' e' = E ∨ ∃ A ∈ 𝒜, α' u' e' ∪ A = E)}.ncard <
      {u : ι₂ | IsLeaf T₂ u ∧
        ∃ e, IsTreeIncidence T₂ u e ∧ ¬ (α₂ u e = E ∨ ∃ A ∈ 𝒜, α₂ u e ∪ A = E)}.ncard := by
  classical
  have hT₁ := hα₁.isTernaryTree
  have hT₂ := hα₂.isTernaryTree
  have hw₁ : w₁ ≠ t₁ := hadj_t₁w₁.ne.symm
  have hs : s ≠ t₀ := hadj_t₀s.ne.symm
  let w₁' : {v : ι₂ // v ≠ t₁} := ⟨w₁, hw₁⟩
  let s' : {u : ι₁ // u ≠ t₀} := ⟨s, hs⟩
  let T' := splicedTree T₂ T₁ hw₁ hs
  obtain ⟨hneigh₂, hneigh₂_val⟩ :=
    exists_spliced_neighborEquiv₂ ht₁_leaf hadj_t₁w₁ hT₂ hw₁ hs
  obtain ⟨hneigh₁, hneigh₁_val⟩ :=
    exists_spliced_neighborEquiv₁ ht₀_leaf hadj_t₀s hT₁ hw₁ hs
  have hT'_ternary : IsTernaryTree T' :=
    splicedTree_isTernaryTree hT₂ hT₁ ht₁_leaf ht₀_leaf hw₁ hs hneigh₂ hneigh₁
  let α' (x : SplicedVert t₁ t₀) (e : Sym2 (SplicedVert t₁ t₀)) : Set β :=
    match x with
    | Sum.inl v =>
      if e = s(Sum.inl w₁', Sum.inr s') then α₂ w₁ s(w₁, t₁)
      else α₂ v.1 (Sym2.map (splicedToNeighbor₂ t₁) e)
    | Sum.inr u =>
      if e = s(Sum.inl w₁', Sum.inr s') then α₂ t₁ s(t₁, w₁)
      else α₁ u.1 (Sym2.map (splicedToNeighbor₁ t₀) e)
  have hα'_inl : ∀ (v : {v : ι₂ // v ≠ t₁}) (z : SplicedVert t₁ t₀)
      (hz : T'.Adj (Sum.inl v) z),
      α' (Sum.inl v) s(Sum.inl v, z) = α₂ v.1 s(v.1, (hneigh₂ v ⟨z, hz⟩).1) := by
    intro v z hz
    rw [hneigh₂_val v z hz]
    rcases (splicedTree_adj_iff hw₁ hs (Sum.inl v) z).1 hz with hG₀ | ⟨h1, rfl⟩ | ⟨h1, _⟩
    · rcases z with w | u
      · have hne_br : s(Sum.inl v, Sum.inl w) ≠ s(Sum.inl w₁', Sum.inr s') := by
          intro heq
          rcases Sym2.eq_iff.1 heq with ⟨_, h⟩ | ⟨h, _⟩ <;> cases h
        simp only [α', splicedToNeighbor₂, hne_br, ↓reduceIte]
        rfl
      · exact hG₀.elim
    · injection h1 with hv_eq
      subst hv_eq
      simp [α', splicedToNeighbor₂, w₁']
    · cases h1
  have hα'_inr_ne : ∀ (u w : {u : ι₁ // u ≠ t₀}),
      α' (Sum.inr u) s(Sum.inr u, Sum.inr w) = α₁ u.1 s(u.1, w.1) := by
    intro u w
    have hne_br : s(Sum.inr u, Sum.inr w) ≠ s(Sum.inl w₁', Sum.inr s') := by
      intro heq
      rcases Sym2.eq_iff.1 heq with ⟨h, _⟩ | ⟨_, h⟩ <;> cases h
    simp only [α', splicedToNeighbor₁, hne_br, ↓reduceIte]
    rfl
  have hα'_inr_sub : ∀ (u : {u : ι₁ // u ≠ t₀}) (z : SplicedVert t₁ t₀)
      (hz : T'.Adj (Sum.inr u) z),
      α₁ u.1 s(u.1, (hneigh₁ u ⟨z, hz⟩).1) ⊆ α' (Sum.inr u) s(Sum.inr u, z) ∧
      IsEfficient E κ (α' (Sum.inr u) s(Sum.inr u, z)) := by
    intro u z hz
    rw [hneigh₁_val u z hz]
    rcases (splicedTree_adj_iff hw₁ hs (Sum.inr u) z).1 hz with hG₀ | ⟨h1, _⟩ | ⟨h1, rfl⟩
    · rcases z with v | w
      · exact hG₀.elim
      · rw [hα'_inr_ne u w]
        exact ⟨subset_rfl, hα₁.isEfficient (isTreeIncidence_iff_adj.2 hG₀)⟩
    · cases h1
    · injection h1 with hu_eq
      subst hu_eq
      have hswap : s(Sum.inr s', Sum.inl w₁') = s(Sum.inl w₁', Sum.inr s') := Sym2.eq_swap
      have hval : α' (Sum.inr s') s(Sum.inr s', Sum.inl w₁') = α₂ t₁ s(t₁, w₁) := by
        simp [α', hswap]
      rw [hval]
      refine ⟨?_, hα₂.isEfficient (isTreeIncidence_iff_adj.2 hadj_t₁w₁)⟩
      change α₁ s s(s, t₀) ⊆ α₂ t₁ s(t₁, w₁)
      rwa [hα₁_s]
  have htree_lab' : IsTreeLabelling E κ 𝒜₂ T' α' := by
    refine ⟨hT'_ternary, ?_, ?_, ?_, ?_⟩
    · intro x e he
      obtain ⟨z, hz, rfl⟩ := isTreeIncidence_iff_exists_adj.1 he
      cases x with
      | inl v =>
        rw [hα'_inl v z hz]
        exact hα₂.isEfficient (isTreeIncidence_iff_adj.2 (hneigh₂ v ⟨z, hz⟩).2)
      | inr u =>
        exact (hα'_inr_sub u z hz).2
    · intro x y hxy
      rcases (splicedTree_adj_iff hw₁ hs x y).1 hxy with hG₀ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases x with u | u <;> rcases y with v | v
        · have hne_br : s(Sum.inl u, Sum.inl v) ≠ s(Sum.inl w₁', Sum.inr s') := by
            intro heq
            rcases Sym2.eq_iff.1 heq with ⟨_, h⟩ | ⟨h, _⟩ <;> cases h
          simp only [α', splicedToNeighbor₂, hne_br, ↓reduceIte]
          exact hα₂.compl_eq hG₀
        · exact hG₀.elim
        · exact hG₀.elim
        · have hne_br : s(Sum.inr u, Sum.inr v) ≠ s(Sum.inl w₁', Sum.inr s') := by
            intro heq
            rcases Sym2.eq_iff.1 heq with ⟨h, _⟩ | ⟨_, h⟩ <;> cases h
          simp only [α', splicedToNeighbor₁, hne_br, ↓reduceIte]
          exact hα₁.compl_eq hG₀
      · simp only [α', w₁', s', ↓reduceIte]
        rw [Sym2.eq_swap (a := t₁)]
        exact hα₂.compl_eq hadj_t₁w₁.symm
      · have hswap : s(Sum.inr s', Sum.inl w₁') = s(Sum.inl w₁', Sum.inr s') := Sym2.eq_swap
        simp only [α', w₁', s', hswap, ↓reduceIte]
        rw [Sym2.eq_swap (a := w₁)]
        exact hα₂.compl_eq hadj_t₁w₁
    · intro x e he hleaf'
      obtain ⟨z, hz, rfl⟩ := isTreeIncidence_iff_exists_adj.1 he
      cases x with
      | inl v =>
        rw [hα'_inl v z hz]
        have hleaf_v : IsLeaf T₂ v.1 := (isLeaf_iff_of_neighborEquiv (hneigh₂ v)).1 hleaf'
        exact hα₂.leaf_eq_or_union_eq
          (isTreeIncidence_iff_adj.2 (hneigh₂ v ⟨z, hz⟩).2) hleaf_v
      | inr u =>
        have hleaf_u : IsLeaf T₁ u.1 := (isLeaf_iff_of_neighborEquiv (hneigh₁ u)).1 hleaf'
        have hu_ne_s : u.1 ≠ s := fun h ↦ hs_not_leaf (h ▸ hleaf_u)
        rcases (splicedTree_adj_iff hw₁ hs (Sum.inr u) z).1 hz with hG₀ | ⟨h1, _⟩ | ⟨h1, _⟩
        · rcases z with v | w
          · exact hG₀.elim
          · rw [hα'_inr_ne u w]
            rcases ht₀_only_bad u.1 s(u.1, w.1) (isTreeIncidence_iff_adj.2 hG₀) hleaf_u u.2 with
              heq | ⟨A, hA𝒜, hunion⟩
            · exact Or.inl heq
            · exact Or.inr ⟨A, h𝒜_sub hA𝒜, hunion⟩
        · cases h1
        · injection h1 with hu_eq
          exact (hu_ne_s (congrArg Subtype.val hu_eq)).elim
    · intro x f₁ f₂ f₃ hf₁ hf₂ hf₃ h12 h13 h23
      cases x with
      | inl v =>
        exact degree_three_union_eq_of_neighborEquiv hα₂ (hneigh₂ v)
          (fun z hz ↦ (hα'_inl v z hz).symm.subset)
          (fun z hz ↦ by
            rw [hα'_inl v z hz]
            exact hα₂.subset_of_inc (isTreeIncidence_iff_adj.2 (hneigh₂ v ⟨z, hz⟩).2))
          hf₁ hf₂ hf₃ h12 h13 h23
      | inr u =>
        exact degree_three_union_eq_of_neighborEquiv hα₁ (hneigh₁ u)
          (fun z hz ↦ (hα'_inr_sub u z hz).1)
          (fun z hz ↦ (hα'_inr_sub u z hz).2.1)
          hf₁ hf₂ hf₃ h12 h13 h23
  let B' : Set (SplicedVert t₁ t₀) :=
    {u' : SplicedVert t₁ t₀ | IsLeaf T' u' ∧
      ∃ e', IsTreeIncidence T' u' e' ∧ ¬ (α' u' e' = E ∨ ∃ A ∈ 𝒜, α' u' e' ∪ A = E)}
  let B₂ : Set ι₂ :=
    {u : ι₂ | IsLeaf T₂ u ∧
      ∃ e, IsTreeIncidence T₂ u e ∧ ¬ (α₂ u e = E ∨ ∃ A ∈ 𝒜, α₂ u e ∪ A = E)}
  let ψ : ι₂ → SplicedVert t₁ t₀ := fun v ↦ if hv : v ≠ t₁ then Sum.inl ⟨v, hv⟩ else Sum.inr s'
  have hB'_sub : B' ⊆ ψ '' (B₂ \ {t₁}) := by
    rintro x ⟨hleaf_x, e', he', hbad'⟩
    obtain ⟨z, hz, rfl⟩ := isTreeIncidence_iff_exists_adj.1 he'
    cases x with
    | inl v =>
      have hleaf_v : IsLeaf T₂ v.1 := (isLeaf_iff_of_neighborEquiv (hneigh₂ v)).1 hleaf_x
      rw [hα'_inl v z hz] at hbad'
      have hinc_v : IsTreeIncidence T₂ v.1 s(v.1, (hneigh₂ v ⟨z, hz⟩).1) :=
        isTreeIncidence_iff_adj.2 (hneigh₂ v ⟨z, hz⟩).2
      refine ⟨v.1, ⟨⟨hleaf_v, _, hinc_v, hbad'⟩, v.2⟩, ?_⟩
      simp [ψ, v.2]
    | inr u =>
      exfalso
      have hleaf_u : IsLeaf T₁ u.1 := (isLeaf_iff_of_neighborEquiv (hneigh₁ u)).1 hleaf_x
      have hu_ne_s : u.1 ≠ s := fun h ↦ hs_not_leaf (h ▸ hleaf_u)
      rcases (splicedTree_adj_iff hw₁ hs (Sum.inr u) z).1 hz with hG₀ | ⟨h1, _⟩ | ⟨h1, _⟩
      · rcases z with v | w
        · exact hG₀.elim
        · rw [hα'_inr_ne u w] at hbad'
          exact hbad' (ht₀_only_bad u.1 s(u.1, w.1) (isTreeIncidence_iff_adj.2 hG₀) hleaf_u u.2)
      · cases h1
      · injection h1 with hu_eq
        exact hu_ne_s (congrArg Subtype.val hu_eq)
  have ht₁_mem_B₂ : t₁ ∈ B₂ :=
    ⟨ht₁_leaf, s(t₁, w₁), isTreeIncidence_iff_adj.2 hadj_t₁w₁, ht₁_bad⟩
  have hncard_lt : B'.ncard < B₂.ncard := by
    have h1 : B'.ncard ≤ (ψ '' (B₂ \ {t₁})).ncard :=
      Set.ncard_le_ncard hB'_sub (Set.toFinite _)
    have h2 : (ψ '' (B₂ \ {t₁})).ncard ≤ (B₂ \ {t₁}).ncard :=
      Set.ncard_image_le (Set.toFinite _)
    have h3 : (B₂ \ {t₁}).ncard < B₂.ncard :=
      Set.ncard_lt_ncard (Set.sdiff_singleton_ssubset.2 ht₁_mem_B₂) (Set.toFinite _)
    exact (h1.trans h2).trans_lt h3
  exact ⟨SplicedVert t₁ t₀, inferInstance, T', α', htree_lab', hncard_lt⟩

end GraphMinor.GM10
