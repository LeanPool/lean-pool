/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.SubmodularTree

/-!
# Submodular Functions and Tree-Labellings: Graph Minors X, Section 3 (3.4)–(3.6)

This file formalizes the main theorems of Section 3 of Robertson and Seymour,
*Graph Minors. X. Obstructions to tree-decomposition*, J. Combin. Theory Ser. B 52 (1991)
153–190 (pages 162–164):
- `theorem_3_4` (3.4): If there is no bias extending `𝒜`, then there is an exact tree-labelling
  over `𝒜`.
- `theorem_3_5` (3.5): Equivalence of (i) no bias extending `𝒜`, (ii) existence of a
  tree-labelling over `𝒜`, and (iii) existence of an exact tree-labelling over `𝒜`.
- `theorem_3_6` (3.6): If there is an exact tree-labelling over `𝒜`, then either `E = ∅`, or
  `E ∈ 𝒜`, or there is an exact tree-labelling `(T, α)` over `𝒜` such that `α(v, e) ≠ E` for
  every leaf `v` and incident edge `e`.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph

variable {β : Type*} {ι : Type*}

/-! ## Uncovered efficient sets for the induction in (3.4) -/

/-- The set of efficient subsets `X ⊆ E` such that neither `X` nor `E \ X` is a subset of any
member of `𝒜` (Graph Minors X, Section 3, proof of (3.4), page 162). -/
def uncoveredEfficientSets (E : Set β) (κ : Set β → ℤ) (𝒜 : Set (Set β)) : Set (Set β) :=
  {X : Set β | IsEfficient E κ X ∧ (∀ A ∈ 𝒜, ¬ X ⊆ A) ∧ (∀ A ∈ 𝒜, ¬ E \ X ⊆ A)}

theorem uncoveredEfficientSets_finite {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    (hE : E.Finite) : (uncoveredEfficientSets E κ 𝒜).Finite :=
  hE.finite_subsets.subset fun _ hX ↦ hX.1.1

theorem uncoveredEfficientSets_anti {E : Set β} {κ : Set β → ℤ} {𝒜₁ 𝒜₂ : Set (Set β)}
    (hsub : 𝒜₁ ⊆ 𝒜₂) :
    uncoveredEfficientSets E κ 𝒜₂ ⊆ uncoveredEfficientSets E κ 𝒜₁ :=
  fun _ ⟨heff, h1, h2⟩ ↦ ⟨heff, fun A hA ↦ h1 A (hsub hA), fun A hA ↦ h2 A (hsub hA)⟩

theorem notMem_uncoveredEfficientSets_insert_left {E X : Set β} {κ : Set β → ℤ}
    {𝒜 : Set (Set β)} :
    X ∉ uncoveredEfficientSets E κ (insert X 𝒜) :=
  fun ⟨_, h1, _⟩ ↦ h1 X (Set.mem_insert X 𝒜) subset_rfl

theorem notMem_uncoveredEfficientSets_insert_right {E X : Set β} {κ : Set β → ℤ}
    {𝒜 : Set (Set β)} :
    X ∉ uncoveredEfficientSets E κ (insert (E \ X) 𝒜) :=
  fun ⟨_, _, h2⟩ ↦ h2 (E \ X) (Set.mem_insert (E \ X) 𝒜) subset_rfl

/-! ## Repeated splicing across all bad leaves of `T₂` -/

/-- Given a tree-labelling `(T₁, α₁)` with a unique bad leaf `t₀` adjacent to a degree-3 vertex `s`
with `α₁(s, s(s, t₀)) = X`, and any tree-labelling `(T₂, α₂)` over `insert (E \ X) 𝒜`, repeatedly
splicing `T₁ \ t₀` onto the bad leaves of `T₂` produces a tree-labelling over `𝒜`
(Graph Minors X, Section 3, proof of (3.4), page 163). -/
private theorem exists_treeLabelling_of_unique_bad_leaf {ι₁ : Type} [Fintype ι₁]
    {E X : Set β} {κ : Set β → ℤ} {𝒜 𝒜₁ : Set (Set β)}
    {T₁ : SimpleGraph ι₁} {α₁ : ι₁ → Sym2 ι₁ → Set β}
    (hα₁ : IsTreeLabelling E κ 𝒜₁ T₁ α₁)
    {t₀ s : ι₁} (ht₀_leaf : IsLeaf T₁ t₀) (hadj_t₀s : T₁.Adj t₀ s)
    (hs_not_leaf : ¬ IsLeaf T₁ s) (hα₁_s : α₁ s s(s, t₀) = X)
    (hX_sub_E : X ⊆ E)
    (ht₀_only_bad : ∀ u e, IsTreeIncidence T₁ u e → IsLeaf T₁ u → u ≠ t₀ →
      α₁ u e = E ∨ ∃ A ∈ 𝒜, α₁ u e ∪ A = E) :
    ∀ (k : ℕ) (ι₂ : Type) [Fintype ι₂] (T₂ : SimpleGraph ι₂) (α₂ : ι₂ → Sym2 ι₂ → Set β),
      IsTreeLabelling E κ (insert (E \ X) 𝒜) T₂ α₂ →
      {u : ι₂ | IsLeaf T₂ u ∧
        ∃ e, IsTreeIncidence T₂ u e ∧ ¬ (α₂ u e = E ∨ ∃ A ∈ 𝒜, α₂ u e ∪ A = E)}.ncard = k →
      ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (α' : ι' → Sym2 ι' → Set β),
        IsTreeLabelling E κ 𝒜 T' α' := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro ι₂ _ T₂ α₂ hα₂ hcard
    let B₂ : Set ι₂ :=
      {u : ι₂ | IsLeaf T₂ u ∧
        ∃ e, IsTreeIncidence T₂ u e ∧ ¬ (α₂ u e = E ∨ ∃ A ∈ 𝒜, α₂ u e ∪ A = E)}
    by_cases hB₂ : B₂.Nonempty
    · obtain ⟨t₁, ht₁_leaf, e₁, he₁_inc, ht₁_bad⟩ := hB₂
      obtain ⟨w₁, hadj_t₁w₁, rfl⟩ := isTreeIncidence_iff_exists_adj.1 he₁_inc
      have hX_sub : X ⊆ α₂ t₁ s(t₁, w₁) := by
        rcases hα₂.leaf_eq_or_union_eq (isTreeIncidence_iff_adj.2 hadj_t₁w₁) ht₁_leaf with
          heq | ⟨A, hA_mem, hunion⟩
        · exact (ht₁_bad (Or.inl heq)).elim
        · rcases Set.mem_insert_iff.1 hA_mem with rfl | hA𝒜
          · intro x hx
            have hxE : x ∈ α₂ t₁ s(t₁, w₁) ∪ (E \ X) := hunion.symm ▸ hX_sub_E hx
            rcases hxE with hx1 | ⟨_, hx2⟩
            · exact hx1
            · exact (hx2 hx).elim
          · exact (ht₁_bad (Or.inr ⟨A, hA𝒜, hunion⟩)).elim
      obtain ⟨ι', hfin', T', α', hα', hlt⟩ :=
        exists_spliced_treeLabelling (Set.subset_insert (E \ X) 𝒜) hα₁ hα₂
          ht₀_leaf hadj_t₀s hs_not_leaf hα₁_s ht₀_only_bad
          ht₁_leaf hadj_t₁w₁ ht₁_bad hX_sub
      rw [hcard] at hlt
      exact @ih _ hlt ι' hfin' T' α' hα' rfl
    · rw [Set.not_nonempty_iff_eq_empty] at hB₂
      refine ⟨ι₂, inferInstance, T₂, α₂, hα₂.isTernaryTree, hα₂.isEfficient, hα₂.compl_eq,
        ?_, hα₂.degree_three_union_eq⟩
      intro u e he hleaf
      by_contra hbad
      have hu_mem : u ∈ B₂ := ⟨hleaf, e, he, hbad⟩
      rw [hB₂] at hu_mem
      exact hu_mem

/-! ## Proof of (3.4) -/

/-- A deficient leaf labelled over an extension by a minimal uncovered set has that set as the
complement of its label. -/
private theorem badLeaf_complement_eq_minimal_uncovered {E X : Set β} {κ : Set β → ℤ}
    {𝒜 : Set (Set β)} (hκ : IsConnectivityFunction E κ)
    (h𝒜 : ∀ A ∈ 𝒜, IsEfficient E κ A)
    (hX_min : Minimal (· ∈ uncoveredEfficientSets E κ 𝒜) X)
    (hX_compl_not_sub : ∀ A ∈ 𝒜, ¬ E \ X ⊆ A)
    {ι₁ : Type*} [Fintype ι₁] {T₁ : SimpleGraph ι₁} {α₁ : ι₁ → Sym2 ι₁ → Set β}
    (hα₁ : IsExactTreeLabelling E κ (insert X 𝒜) T₁ α₁) :
    ∀ u e, IsTreeIncidence T₁ u e → IsLeaf T₁ u →
      ¬ (α₁ u e = E ∨ ∃ A ∈ 𝒜, α₁ u e ∪ A = E) → E \ α₁ u e = X := by
  intro u e he hleaf hbad
  have h_union_X : α₁ u e ∪ X = E := by
    rcases hα₁.isTreeLabelling.leaf_eq_or_union_eq he hleaf with heq | ⟨A, hA_mem, hunion⟩
    · exact (hbad (Or.inl heq)).elim
    · rcases Set.mem_insert_iff.1 hA_mem with rfl | hA𝒜
      · exact hunion
      · exact (hbad (Or.inr ⟨A, hA𝒜, hunion⟩)).elim
  let Y := E \ α₁ u e
  have hY_sub_X : Y ⊆ X := by
    rintro y ⟨hyE, hy_not⟩
    have hy_mem : y ∈ α₁ u e ∪ X := h_union_X.symm ▸ hyE
    exact hy_mem.resolve_left hy_not
  have hY_eff : IsEfficient E κ Y :=
    (hα₁.isTreeLabelling.isEfficient he).compl hκ
  have hY_not_sub : ∀ A ∈ 𝒜, ¬ Y ⊆ A := by
    intro A hA hYA
    apply hbad
    right
    refine ⟨A, hA, Set.Subset.antisymm
      (Set.union_subset (hα₁.isTreeLabelling.subset_of_inc he) (h𝒜 A hA).1) ?_⟩
    intro y hyE
    by_cases hyα : y ∈ α₁ u e
    · exact Or.inl hyα
    · exact Or.inr (hYA ⟨hyE, hyα⟩)
  have hY_compl_not_sub : ∀ A ∈ 𝒜, ¬ E \ Y ⊆ A := by
    intro A hA hEYA
    apply hX_compl_not_sub A hA
    intro y ⟨hyE, hyX⟩
    apply hEYA
    exact ⟨hyE, fun hyY ↦ hyX (hY_sub_X hyY)⟩
  have hY_mem : Y ∈ uncoveredEfficientSets E κ 𝒜 :=
    ⟨hY_eff, hY_not_sub, hY_compl_not_sub⟩
  exact Set.Subset.antisymm hY_sub_X (hX_min.le_of_le hY_mem hY_sub_X)

/-- **(3.4)** Let `κ` be a connectivity function on a finite set `E`, and let `𝒜` be a set of
efficient subsets of `E`. If there is no bias extending `𝒜`, then there is an exact
tree-labelling over `𝒜`
(Graph Minors X, Section 3, (3.4), page 162). -/
theorem theorem_3_4_proof {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    (hE : E.Finite) (hκ : IsConnectivityFunction E κ)
    (h𝒜 : ∀ A ∈ 𝒜, IsEfficient E κ A)
    (hno_bias : ¬ ∃ ℬ, BiasExtends E κ 𝒜 ℬ) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
      IsExactTreeLabelling E κ 𝒜 T α := by
  classical
  -- By (3.2), it suffices to construct a tree-labelling over `𝒜`.
  suffices ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
      IsTreeLabelling E κ 𝒜 T α by
    obtain ⟨ι, _, T, α, hα⟩ := this
    obtain ⟨α', hα'⟩ := theorem_3_2_proof hE hκ hα
    exact ⟨ι, inferInstance, T, α', hα'⟩
  -- Handle `E = ∅`.
  by_cases hE_empty : E = ∅
  · by_cases heff_empty : IsEfficient E κ ∅
    · exact exists_isTreeLabelling_of_empty hE_empty heff_empty
    · exfalso
      apply hno_bias
      refine ⟨∅, ⟨fun B (hB : B ∈ (∅ : Set (Set β))) ↦ hB.elim, ?_, ?_⟩, ?_⟩
      · intro X hX
        have hX_eq : X = ∅ := Set.eq_empty_of_subset hX.1 hE_empty
        exact (heff_empty (hX_eq ▸ hX)).elim
      · intro X₁ _ _ (hX₁ : X₁ ∈ (∅ : Set (Set β))) _ _
        exact hX₁.elim
      · intro A hA
        have hA_eq : A = ∅ := Set.eq_empty_of_subset (h𝒜 A hA).1 hE_empty
        exact (heff_empty (hA_eq ▸ h𝒜 A hA)).elim
  -- Now `E` is nonempty.
  have hE_ne : E.Nonempty := Set.nonempty_iff_ne_empty.2 hE_empty
  -- Induction on the number `N` of uncovered efficient sets.
  have hmain : ∀ (N : ℕ) (𝒜 : Set (Set β)),
      (∀ A ∈ 𝒜, IsEfficient E κ A) →
      (¬ ∃ ℬ, BiasExtends E κ 𝒜 ℬ) →
      (uncoveredEfficientSets E κ 𝒜).ncard = N →
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
        IsTreeLabelling E κ 𝒜 T α := by
    intro N
    induction N using Nat.strong_induction_on with
    | ind N ih =>
      intro 𝒜 h𝒜 hno_bias hcard
      -- Since `E` is nonempty and no bias extends `𝒜`, `𝒜` is nonempty.
      have h𝒜_ne : 𝒜.Nonempty := by
        by_contra h𝒜_empty
        rw [Set.not_nonempty_iff_eq_empty] at h𝒜_empty
        obtain ⟨x₀, hx₀⟩ := hE_ne
        apply hno_bias
        let ℬ : Set (Set β) := {B : Set β | IsEfficient E κ B ∧ x₀ ∉ B}
        refine ⟨ℬ, ⟨fun B hB ↦ hB.1, ?_, ?_⟩, ?_⟩
        · intro X hX
          by_cases hxX : x₀ ∈ X
          · right
            exact ⟨hX.compl hκ, fun h ↦ h.2 hxX⟩
          · left
            exact ⟨hX, hxX⟩
        · intro X₁ X₂ X₃ h₁ h₂ h₃ hunion
          have hx_mem : x₀ ∈ X₁ ∪ X₂ ∪ X₃ := hunion.symm ▸ hx₀
          rcases hx_mem with (hx₁ | hx₂) | hx₃
          · exact h₁.2 hx₁
          · exact h₂.2 hx₂
          · exact h₃.2 hx₃
        · rw [h𝒜_empty]
          exact Set.empty_subset _
      by_cases hU_ne : (uncoveredEfficientSets E κ 𝒜).Nonempty
      · -- Inductive step: `N > 0`. Choose a minimal uncovered efficient set `X`.
        obtain ⟨X, hX_min⟩ := (uncoveredEfficientSets_finite hE).exists_minimal hU_ne
        have hX_mem : X ∈ uncoveredEfficientSets E κ 𝒜 := hX_min.prop
        have hX_eff : IsEfficient E κ X := hX_mem.1
        have hX_not_sub : ∀ A ∈ 𝒜, ¬ X ⊆ A := hX_mem.2.1
        have hX_compl_not_sub : ∀ A ∈ 𝒜, ¬ E \ X ⊆ A := hX_mem.2.2
        obtain ⟨A₀, hA₀⟩ := h𝒜_ne
        have hX_ne : X.Nonempty := by
          by_contra hX_emp
          rw [Set.not_nonempty_iff_eq_empty] at hX_emp
          exact hX_not_sub A₀ hA₀ (hX_emp ▸ Set.empty_subset A₀)
        -- Apply IH to `𝒜₁ = insert X 𝒜` and `𝒜₂ = insert (E \ X) 𝒜`.
        let 𝒜₁ : Set (Set β) := insert X 𝒜
        let 𝒜₂ : Set (Set β) := insert (E \ X) 𝒜
        have h𝒜₁_eff : ∀ A ∈ 𝒜₁, IsEfficient E κ A := by
          rintro A (rfl | hA)
          · exact hX_eff
          · exact h𝒜 A hA
        have h𝒜₂_eff : ∀ A ∈ 𝒜₂, IsEfficient E κ A := by
          rintro A (rfl | hA)
          · exact hX_eff.compl hκ
          · exact h𝒜 A hA
        have hno_bias₁ : ¬ ∃ ℬ, BiasExtends E κ 𝒜₁ ℬ := by
          rintro ⟨ℬ, hbias, hsub⟩
          exact hno_bias ⟨ℬ, hbias, Set.Subset.trans (Set.subset_insert X 𝒜) hsub⟩
        have hno_bias₂ : ¬ ∃ ℬ, BiasExtends E κ 𝒜₂ ℬ := by
          rintro ⟨ℬ, hbias, hsub⟩
          exact hno_bias ⟨ℬ, hbias, Set.Subset.trans (Set.subset_insert (E \ X) 𝒜) hsub⟩
        have hlt₁ : (uncoveredEfficientSets E κ 𝒜₁).ncard < N := by
          rw [← hcard]
          refine Set.ncard_lt_ncard ⟨uncoveredEfficientSets_anti (Set.subset_insert X 𝒜), ?_⟩
            (uncoveredEfficientSets_finite hE)
          intro hsub
          exact notMem_uncoveredEfficientSets_insert_left (hsub hX_mem)
        have hlt₂ : (uncoveredEfficientSets E κ 𝒜₂).ncard < N := by
          rw [← hcard]
          refine Set.ncard_lt_ncard ⟨uncoveredEfficientSets_anti (Set.subset_insert (E \ X) 𝒜), ?_⟩
            (uncoveredEfficientSets_finite hE)
          intro hsub
          exact notMem_uncoveredEfficientSets_insert_right (hsub hX_mem)
        obtain ⟨ι₁, _, T₁, α₁₀, hα₁₀⟩ := ih _ hlt₁ 𝒜₁ h𝒜₁_eff hno_bias₁ rfl
        obtain ⟨α₁, hα₁⟩ := theorem_3_2_proof hE hκ hα₁₀
        obtain ⟨ι₂, _, T₂, α₂, hα₂⟩ := ih _ hlt₂ 𝒜₂ h𝒜₂_eff hno_bias₂ rfl
        have hbad₁_eq_X :=
          badLeaf_complement_eq_minimal_uncovered hκ h𝒜 hX_min hX_compl_not_sub hα₁
        -- Check whether `T₁` has any bad leaf.
        by_cases hex_bad₁ : ∃ t₀ e₀, IsTreeIncidence T₁ t₀ e₀ ∧ IsLeaf T₁ t₀ ∧
            ¬ (α₁ t₀ e₀ = E ∨ ∃ A ∈ 𝒜, α₁ t₀ e₀ ∪ A = E)
        · obtain ⟨t₀, e₀, he₀, ht₀_leaf, ht₀_bad⟩ := hex_bad₁
          obtain ⟨s, hadj_t₀s, rfl⟩ := isTreeIncidence_iff_exists_adj.1 he₀
          have hα₁_t₀_compl : E \ α₁ t₀ s(t₀, s) = X :=
            hbad₁_eq_X t₀ s(t₀, s) (isTreeIncidence_iff_adj.2 hadj_t₀s) ht₀_leaf ht₀_bad
          have hα₁_s : α₁ s s(s, t₀) = X := by
            rw [hα₁.isTreeLabelling.compl_eq hadj_t₀s.symm, Sym2.eq_swap, hα₁_t₀_compl]
          -- By (3.3), `t₀` is the unique bad leaf of `T₁`.
          have ht₀_only_bad : ∀ u e, IsTreeIncidence T₁ u e → IsLeaf T₁ u → u ≠ t₀ →
              α₁ u e = E ∨ ∃ A ∈ 𝒜, α₁ u e ∪ A = E := by
            intro u e he hleaf hu_ne
            by_contra hu_bad
            have hu_compl : E \ α₁ u e = X := hbad₁_eq_X u e he hleaf hu_bad
            have hT₁_tree := hα₁.isTreeLabelling.isTernaryTree
            have hT₁_conn_compl : (T₁.induce {t₀}ᶜ).Connected :=
              hT₁_tree.isTree.connected.induce_compl_singleton_of_degree_eq_one
                (hT₁_tree.degree_eq_one_of_isLeaf ht₀_leaf)
            let s' : ({t₀}ᶜ : Set ι₁) := ⟨s, hadj_t₀s.ne.symm⟩
            let u' : ({t₀}ᶜ : Set ι₁) := ⟨u, hu_ne⟩
            obtain ⟨p', hp'⟩ := hT₁_conn_compl.exists_isPath s' u'
            have hp_not_edge : s(s, t₀) ∉ (p'.map (Embedding.induce {t₀}ᶜ).toHom).edges := by
              intro hmem
              have ht₀_mem : t₀ ∈ (p'.map (Embedding.induce {t₀}ᶜ).toHom).support :=
                Walk.mem_support_of_mem_edges hmem (Sym2.mem_mk_right s t₀)
              rw [Walk.support_map] at ht₀_mem
              obtain ⟨z', _, hz'_eq⟩ := List.mem_map.1 ht₀_mem
              exact z'.2 hz'_eq
            have hreach_del : (T₁.deleteEdges {s(s, t₀)}).Reachable s u :=
              ⟨(p'.map (Embedding.induce {t₀}ᶜ).toHom).toDeleteEdges {s(s, t₀)}
                (fun e he ↦ by simp only [Set.mem_singleton_iff]; rintro rfl; exact hp_not_edge he)⟩
            obtain ⟨_, hunion_s⟩ :=
              theorem_3_3_proof hα₁ (isTreeIncidence_iff_adj.2 hadj_t₀s.symm)
            have hmem_leaf : (u, e) ∈ leafIncidencesIn T₁ s s(s, t₀) :=
              show IsTreeIncidence T₁ u e ∧ IsLeaf T₁ u ∧ u ∈ treeComponent T₁ s s(s, t₀) from
                ⟨he, hleaf, hreach_del⟩
            have hsub_s : E \ α₁ u e ⊆ E \ α₁ s s(s, t₀) := by
              rw [← hunion_s]
              exact Set.subset_biUnion_of_mem (u := fun p : ι₁ × Sym2 ι₁ ↦ E \ α₁ p.1 p.2)
                hmem_leaf
            rw [hu_compl, hα₁_s] at hsub_s
            obtain ⟨x, hx⟩ := hX_ne
            exact (hsub_s hx).2 hx
          -- Show `s` is not a leaf of `T₁`.
          have hs_not_leaf : ¬ IsLeaf T₁ s := by
            intro hs_leaf
            rcases hα₁.isTreeLabelling.leaf_eq_or_union_eq
              (isTreeIncidence_iff_adj.2 hadj_t₀s.symm) hs_leaf with heq | ⟨A, hA_mem, hunion⟩
            · rw [hα₁_s] at heq
              apply hX_compl_not_sub A₀ hA₀
              rw [heq, Set.sdiff_self]
              exact Set.empty_subset A₀
            · rw [hα₁_s] at hunion
              rcases Set.mem_insert_iff.1 hA_mem with rfl | hA𝒜
              · rw [Set.union_self] at hunion
                apply hX_compl_not_sub A₀ hA₀
                rw [hunion, Set.sdiff_self]
                exact Set.empty_subset A₀
              · apply hX_compl_not_sub A hA𝒜
                rintro y ⟨hyE, hyX⟩
                have hy_mem : y ∈ X ∪ A := hunion.symm ▸ hyE
                exact hy_mem.resolve_left hyX
          exact exists_treeLabelling_of_unique_bad_leaf hα₁.isTreeLabelling
            ht₀_leaf hadj_t₀s hs_not_leaf hα₁_s hX_eff.1 ht₀_only_bad
            _ ι₂ T₂ α₂ hα₂ rfl
        · -- `T₁` has no bad leaf, so `(T₁, α₁)` is already a tree-labelling over `𝒜`.
          refine ⟨ι₁, inferInstance, T₁, α₁, hα₁.isTreeLabelling.isTernaryTree,
            hα₁.isTreeLabelling.isEfficient, hα₁.isTreeLabelling.compl_eq, ?_,
            hα₁.isTreeLabelling.degree_three_union_eq⟩
          intro u e he hleaf
          by_contra hbad
          exact hex_bad₁ ⟨u, e, he, hleaf, hbad⟩
      · -- Base case: `uncoveredEfficientSets E κ 𝒜 = ∅`.
        rw [Set.not_nonempty_iff_eq_empty] at hU_ne
        let ℬ : Set (Set β) := {B : Set β | IsEfficient E κ B ∧ ∃ A ∈ 𝒜, B ⊆ A}
        have hℬ_sub : 𝒜 ⊆ ℬ := fun A hA ↦ ⟨h𝒜 A hA, A, hA, subset_rfl⟩
        have hℬ_ax1 : ∀ ⦃X : Set β⦄, IsEfficient E κ X → X ∈ ℬ ∨ E \ X ∈ ℬ := by
          intro X hX
          by_contra! hnot
          have hX_mem : X ∈ uncoveredEfficientSets E κ 𝒜 := by
            refine ⟨hX, fun A hA hXA ↦ hnot.1 ⟨hX, A, hA, hXA⟩,
              fun A hA hEXA ↦ hnot.2 ⟨hX.compl hκ, A, hA, hEXA⟩⟩
          rw [hU_ne] at hX_mem
          exact hX_mem
        have hnot_ax2 : ¬ ∀ ⦃X Y Z : Set β⦄, X ∈ ℬ → Y ∈ ℬ → Z ∈ ℬ → X ∪ Y ∪ Z ≠ E := by
          intro hax2
          exact hno_bias ⟨ℬ, ⟨fun B hB ↦ hB.1, hℬ_ax1, hax2⟩, hℬ_sub⟩
        push Not at hnot_ax2
        obtain ⟨X₁, X₂, X₃, ⟨heff₁, hsub₁⟩, ⟨heff₂, hsub₂⟩, ⟨heff₃, hsub₃⟩, hunion⟩ := hnot_ax2
        exact exists_isTreeLabelling_of_three_sets hκ h𝒜 heff₁ heff₂ heff₃ hsub₁ hsub₂ hsub₃ hunion
  exact hmain _ 𝒜 h𝒜 hno_bias rfl

/-! ## Proof of (3.5) and (3.6) -/

/-- **(3.5)** Let `κ` be a connectivity function on a finite set `E`, and let `𝒜` be a set of
efficient subsets of `E`. Then the following are equivalent:
(i) there is no bias extending `𝒜`;
(ii) there is a tree-labelling over `𝒜`;
(iii) there is an exact tree-labelling over `𝒜`
(Graph Minors X, Section 3, (3.5), page 163). -/
theorem theorem_3_5_proof {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    (hE : E.Finite) (hκ : IsConnectivityFunction E κ)
    (h𝒜 : ∀ A ∈ 𝒜, IsEfficient E κ A) :
    ((¬ ∃ ℬ, BiasExtends E κ 𝒜 ℬ) ↔
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
        IsTreeLabelling E κ 𝒜 T α) ∧
    ((∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
        IsTreeLabelling E κ 𝒜 T α) ↔
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
        IsExactTreeLabelling E κ 𝒜 T α) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hno_bias
    obtain ⟨ι, _, T, α, hα⟩ := theorem_3_4_proof hE hκ h𝒜 hno_bias
    exact ⟨ι, inferInstance, T, α, hα.isTreeLabelling⟩
  · rintro ⟨ι, _, T, α, hα⟩ ⟨ℬ, hbias⟩
    exact theorem_3_1_proof hbias hα
  · rintro ⟨ι, _, T, α, hα⟩
    obtain ⟨α', hα'⟩ := theorem_3_2_proof hE hκ hα
    exact ⟨ι, inferInstance, T, α', hα'⟩
  · rintro ⟨ι, _, T, α, hα⟩
    exact ⟨ι, inferInstance, T, α, hα.isTreeLabelling⟩

/-- **(3.6)** If there is an exact tree-labelling over `𝒜`, then either `E = ∅`, or `E ∈ 𝒜`, or
there is an exact tree-labelling `(T, α)` over `𝒜` such that `α(v, e) ≠ E` for each leaf `v` and
incident edge `e`
(Graph Minors X, Section 3, (3.6), pages 163–164). -/
theorem theorem_3_6_proof [Fintype ι] {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    (_h𝒜 : ∀ A ∈ 𝒜, IsEfficient E κ A)
    {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (hα : IsExactTreeLabelling E κ 𝒜 T α) :
    E = ∅ ∨ E ∈ 𝒜 ∨
      ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (α' : ι' → Sym2 ι' → Set β),
        IsExactTreeLabelling E κ 𝒜 T' α' ∧
        ∀ v e, IsTreeIncidence T' v e → IsLeaf T' v → α' v e ≠ E := by
  classical
  have hmain : ∀ (n : ℕ) (ι₀ : Type) [Fintype ι₀] (T₀ : SimpleGraph ι₀)
      (α₀ : ι₀ → Sym2 ι₀ → Set β),
      Fintype.card ι₀ = n →
      IsExactTreeLabelling E κ 𝒜 T₀ α₀ →
      E = ∅ ∨ E ∈ 𝒜 ∨
        ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (α' : ι' → Sym2 ι' → Set β),
          IsExactTreeLabelling E κ 𝒜 T' α' ∧
          ∀ v e, IsTreeIncidence T' v e → IsLeaf T' v → α' v e ≠ E := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro ι₀ _ T₀ α₀ hcard hα₀
      by_cases hex : ∃ v₀ e₀, IsTreeIncidence T₀ v₀ e₀ ∧ IsLeaf T₀ v₀ ∧ α₀ v₀ e₀ = E
      · obtain ⟨v₀, e₀, he₀, hleaf₀, hα_v₀⟩ := hex
        obtain ⟨v, hadj₀, rfl⟩ := isTreeIncidence_iff_exists_adj.1 he₀
        by_cases hv_leaf : IsLeaf T₀ v
        · have hα_v : α₀ v s(v, v₀) = ∅ := by
            rw [hα₀.isTreeLabelling.compl_eq hadj₀.symm, Sym2.eq_swap, hα_v₀, Set.sdiff_self]
          rcases hα₀.isTreeLabelling.leaf_eq_or_union_eq
            (isTreeIncidence_iff_adj.2 hadj₀.symm) hv_leaf with heq | ⟨A, hA_mem, hunion⟩
          · rw [hα_v] at heq
            exact Or.inl heq.symm
          · rw [hα_v, Set.empty_union] at hunion
            exact Or.inr (Or.inl (hunion ▸ hA_mem))
        · obtain ⟨ι', hfin', T', α', hlt, hexact'⟩ :=
            exists_smaller_exactTreeLabelling_of_leaf_eq hα₀ hleaf₀ hadj₀ hα_v₀ hv_leaf
          rw [hcard] at hlt
          exact @ih _ hlt ι' hfin' T' α' rfl hexact'
      · push Not at hex
        exact Or.inr (Or.inr ⟨ι₀, inferInstance, T₀, α₀, hα₀, hex⟩)
  let eFin := Fintype.equivFin ι
  exact hmain (Fintype.card (Fin (Fintype.card ι))) (Fin (Fintype.card ι))
    (T.map eFin.toEmbedding) (fun v e ↦ α (eFin.symm v) (e.map eFin.symm)) rfl (hα.relabel eFin)

end GraphMinor.GM10
