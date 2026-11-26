/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Order.Preorder.Finite

/-!
# Submodular Functions and Tree-Labellings: Graph Minors X, Section 3 (3.1)–(3.3)

This file formalizes the first half of Section 3 (pages 159–162) of Robertson and Seymour,
*Graph Minors. X. Obstructions to tree-decomposition*, J. Combin. Theory Ser. B 52 (1991) 153–190:
- Basic properties of ternary trees, incidences, forks, connectivity functions, and biases.
- `(3.1)` (`theorem_3_1`): If there is a bias extending `𝒜` then there is no tree-labelling over
`𝒜`.
- `(3.2)` (`theorem_3_2`): If there is a tree-labelling over `𝒜` then there is an exact
  tree-labelling over `𝒜`, using the same tree.
- `(3.3)` (`theorem_3_3`): Disjointness and union of `E \ α(v, e)` over leaf incidences in a
  component of `T \ f` for an exact tree-labelling.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph

variable {β : Type*} {ι : Type*}

/-! ## Connectivity functions, efficient sets, and biases -/

theorem IsConnectivityFunction.empty_eq (E : Set β) (κ : Set β → ℤ)
    (hκ : IsConnectivityFunction E κ) : κ ∅ = κ E := by
  simpa using hκ.compl_eq (Set.empty_subset E)

theorem IsConnectivityFunction.compl_compl {E X : Set β} {κ : Set β → ℤ}
    (_hκ : IsConnectivityFunction E κ) (hX : X ⊆ E) : E \ (E \ X) = X :=
  Set.sdiff_sdiff_cancel_left hX

theorem IsEfficient.compl {E X : Set β} {κ : Set β → ℤ}
    (hκ : IsConnectivityFunction E κ) (hX : IsEfficient E κ X) :
    IsEfficient E κ (E \ X) :=
  ⟨Set.sdiff_subset, by rw [← hκ.compl_eq hX.1]; exact hX.2⟩

theorem IsBias.notMem_self {E : Set β} {κ : Set β → ℤ} {ℬ : Set (Set β)}
    (hℬ : IsBias E κ ℬ) : E ∉ ℬ := by
  intro hE
  apply hℬ.union_ne hE hE hE
  simp

theorem IsBias.notMem_of_union_eq {E X Y : Set β} {κ : Set β → ℤ} {ℬ : Set (Set β)}
    (hℬ : IsBias E κ ℬ) (hX : X ∈ ℬ) (hY : Y ∈ ℬ) : X ∪ Y ≠ E := by
  intro hXY
  apply hℬ.union_ne hX hY hY
  rw [Set.union_assoc, Set.union_self, hXY]

theorem IsBias.compl_notMem {E X : Set β} {κ : Set β → ℤ} {ℬ : Set (Set β)}
    (hℬ : IsBias E κ ℬ) (hX : X ∈ ℬ) : E \ X ∉ ℬ := by
  intro hcompl
  have hsub : X ⊆ E := (hℬ.isEfficient hX).1
  exact hℬ.notMem_of_union_eq hX hcompl (Set.union_sdiff_cancel hsub)

/-! ## Ternary trees and incidences -/

theorem isTreeIncidence_iff_adj {T : SimpleGraph ι} {u v : ι} :
    IsTreeIncidence T u s(u, v) ↔ T.Adj u v := by
  simp [IsTreeIncidence, mem_incidenceSet]

theorem isTreeIncidence_symm {T : SimpleGraph ι} {u v : ι} (h : T.Adj u v) :
    IsTreeIncidence T v s(u, v) := by
  rw [Sym2.eq_swap]
  exact isTreeIncidence_iff_adj.2 h.symm

theorem isTreeIncidence_iff_exists_adj {T : SimpleGraph ι} {v : ι} {e : Sym2 ι} :
    IsTreeIncidence T v e ↔ ∃ w, T.Adj v w ∧ e = s(v, w) := by
  constructor
  · intro h
    rcases e with ⟨a, b⟩
    have hadj : T.Adj a b := T.mem_edgeSet.1 h.1
    have hmem : v ∈ s(a, b) := h.2
    rcases Sym2.mem_iff.1 hmem with rfl | rfl
    · exact ⟨b, hadj, rfl⟩
    · exact ⟨a, hadj.symm, Sym2.eq_swap⟩
  · rintro ⟨w, hadj, rfl⟩
    exact isTreeIncidence_iff_adj.2 hadj

theorem IsTernaryTree.degree_eq_one_of_isLeaf [Fintype ι] {T : SimpleGraph ι}
    (hT : IsTernaryTree T) {v : ι} (hv : IsLeaf T v) :
    by classical exact T.degree v = 1 := by
  classical
  rcases hT.degree_eq_one_or_three v with h1 | h3
  · exact h1
  · exfalso
    have : T.degree v ≤ 1 := hv
    omega

theorem IsTernaryTree.degree_eq_three_of_not_isLeaf [Fintype ι] {T : SimpleGraph ι}
    (hT : IsTernaryTree T) {v : ι} (hv : ¬ IsLeaf T v) :
    by classical exact T.degree v = 3 := by
  classical
  rcases hT.degree_eq_one_or_three v with h1 | h3
  · exact (hv h1.le).elim
  · exact h3

theorem IsTernaryTree.exists_adj_of_isLeaf [Fintype ι] {T : SimpleGraph ι}
    (hT : IsTernaryTree T) {v : ι} (hv : IsLeaf T v) :
    ∃! w, T.Adj v w := by
  classical
  have h1 : T.degree v = 1 := hT.degree_eq_one_of_isLeaf hv
  exact (degree_eq_one_iff_existsUnique_adj (G := T) (v := v)).1 h1

theorem IsTernaryTree.exists_three_adj_of_not_isLeaf [Fintype ι] {T : SimpleGraph ι}
    (hT : IsTernaryTree T) {v : ι} (hv : ¬ IsLeaf T v) :
    ∃ w₁ w₂ w₃, w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃ ∧
      ∀ w, T.Adj v w ↔ w = w₁ ∨ w = w₂ ∨ w = w₃ := by
  classical
  have h3 : (T.neighborFinset v).card = 3 := by
    rw [card_neighborFinset_eq_degree]
    exact hT.degree_eq_three_of_not_isLeaf hv
  obtain ⟨w₁, w₂, w₃, h12, h13, h23, heq⟩ := Finset.card_eq_three.1 h3
  refine ⟨w₁, w₂, w₃, h12, h13, h23, fun w ↦ ?_⟩
  rw [← mem_neighborFinset, heq]
  simp

theorem IsTernaryTree.exists_other_two_adj [Fintype ι] {T : SimpleGraph ι}
    (hT : IsTernaryTree T) {v w : ι} (hv : ¬ IsLeaf T v) (hadj : T.Adj v w) :
    ∃ w₁ w₂, w ≠ w₁ ∧ w ≠ w₂ ∧ w₁ ≠ w₂ ∧
      ∀ x, T.Adj v x ↔ x = w ∨ x = w₁ ∨ x = w₂ := by
  obtain ⟨a, b, c, hab, hac, hbc, hiff⟩ := hT.exists_three_adj_of_not_isLeaf hv
  rcases (hiff w).1 hadj with rfl | rfl | rfl
  · exact ⟨b, c, hab, hac, hbc, hiff⟩
  · refine ⟨a, c, hab.symm, hbc, hac, fun x ↦ ?_⟩
    rw [hiff x]
    tauto
  · refine ⟨a, b, hac.symm, hbc.symm, hab, fun x ↦ ?_⟩
    rw [hiff x]
    tauto

theorem sym2_mk_eq_left_iff {v w₁ w₂ : ι} : s(v, w₁) = s(v, w₂) ↔ w₁ = w₂ := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h1, h2⟩)
    · exact h
    · exact h2.trans h1
  · rintro rfl
    exact Or.inl ⟨rfl, rfl⟩

theorem IsTernaryTree.not_isLeaf_of_isFork [Fintype ι] {T : SimpleGraph ι}
    (hT : IsTernaryTree T) {t : ι} {e₁ e₂ : Sym2 ι} (hf : IsFork T t e₁ e₂) :
    ¬ IsLeaf T t := by
  intro hleaf
  obtain ⟨w, _, hw_uniq⟩ := hT.exists_adj_of_isLeaf hleaf
  obtain ⟨w₁, hw₁, rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf.1
  obtain ⟨w₂, hw₂, rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf.2.1
  have h1 : w₁ = w := hw_uniq w₁ hw₁
  have h2 : w₂ = w := hw_uniq w₂ hw₂
  exact hf.2.2 (by rw [h1, h2])

/-! ## Basic properties of tree-labellings -/

theorem IsTreeLabelling.subset_of_inc [Fintype ι] {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β} (hα : IsTreeLabelling E κ 𝒜 T α)
    {v : ι} {e : Sym2 ι} (he : IsTreeIncidence T v e) : α v e ⊆ E :=
  (hα.isEfficient he).1

theorem IsTreeLabelling.compl_eq' [Fintype ι] {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β} (hα : IsTreeLabelling E κ 𝒜 T α)
    {u v : ι} (hadj : T.Adj u v) : α v s(u, v) = E \ α u s(u, v) := by
  rw [Sym2.eq_swap]
  exact hα.compl_eq hadj.symm

theorem IsTreeLabelling.union_adj_eq [Fintype ι] {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β} (hα : IsTreeLabelling E κ 𝒜 T α)
    {u v : ι} (hadj : T.Adj u v) : α u s(u, v) ∪ α v s(u, v) = E := by
  rw [hα.compl_eq' hadj]
  exact Set.union_sdiff_cancel (hα.subset_of_inc (isTreeIncidence_iff_adj.2 hadj))

theorem IsTreeLabelling.inter_adj_eq_empty [Fintype ι] {E : Set β} {κ : Set β → ℤ}
    {𝒜 : Set (Set β)} {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (hα : IsTreeLabelling E κ 𝒜 T α) {u v : ι} (hadj : T.Adj u v) :
    α u s(u, v) ∩ α v s(u, v) = ∅ := by
  rw [hα.compl_eq' hadj]
  exact Set.inter_sdiff_self _ _

/-! ## Proof of (3.1) -/

/-- **Graph Minors X, (3.1)** (page 160):
"If there is a bias extending $\mathscr{A}$ then there is no tree-labelling over $\mathscr{A}$." -/
theorem theorem_3_1_proof [Fintype ι] {E : Set β} {κ : Set β → ℤ} {𝒜 ℬ : Set (Set β)}
    {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (hℬ_ext : BiasExtends E κ 𝒜 ℬ) (hα : IsTreeLabelling E κ 𝒜 T α) : False := by
  classical
  obtain ⟨hℬ, h𝒜ℬ⟩ := hℬ_ext
  have hT := hα.isTernaryTree
  -- For each edge `e ∈ E(T)`, at most one end of `e` is passive.
  have huniq_passive : ∀ {e : Sym2 ι} {v₁ v₂ : ι},
      IsPassiveIncidence T α ℬ v₁ e → IsPassiveIncidence T α ℬ v₂ e → v₁ = v₂ := by
    intro e v₁ v₂ hp₁ hp₂
    obtain ⟨w₁, hadj₁, rfl⟩ := isTreeIncidence_iff_exists_adj.1 hp₁.1
    have hmem₂ : v₂ ∈ s(v₁, w₁) := hp₂.1.2
    rcases Sym2.mem_iff.1 hmem₂ with rfl | rfl
    · rfl
    · exfalso
      have heff : IsEfficient E κ (α v₁ s(v₁, v₂)) :=
        hα.isEfficient (isTreeIncidence_iff_adj.2 hadj₁)
      rcases hℬ.mem_or_compl_mem heff with h1 | h2
      · exact hp₁.2 h1
      · rw [← hα.compl_eq' hadj₁] at h2
        exact hp₂.2 h2
  -- If every vertex `v` were in a passive incidence, we would have an injection `ι → T.edgeFinset`.
  have hex_no_passive : ∃ v : ι, ∀ e : Sym2 ι, IsTreeIncidence T v e → α v e ∈ ℬ := by
    by_contra! hall
    choose f hf using hall
    have hf_mem : ∀ v : ι, f v ∈ T.edgeFinset := fun v ↦
      T.mem_edgeFinset.2 (hf v).1.1
    let g : ι → {e // e ∈ T.edgeFinset} := fun v ↦ ⟨f v, hf_mem v⟩
    have hg_inj : Function.Injective g := by
      intro v₁ v₂ heq
      have hfeq : f v₁ = f v₂ := Subtype.ext_iff.1 heq
      exact huniq_passive (hf v₁) (hfeq ▸ hf v₂)
    have hcard_le := Fintype.card_le_of_injective g hg_inj
    rw [Fintype.card_coe] at hcard_le
    have hcard_tree : T.edgeFinset.card + 1 = Fintype.card ι := hT.isTree.card_edgeFinset
    omega
  obtain ⟨v, hv_active⟩ := hex_no_passive
  by_cases hleaf : IsLeaf T v
  · obtain ⟨w, hadj, _⟩ := hT.exists_adj_of_isLeaf hleaf
    have hinc : IsTreeIncidence T v s(v, w) := isTreeIncidence_iff_adj.2 hadj
    have hmem : α v s(v, w) ∈ ℬ := hv_active s(v, w) hinc
    rcases hα.leaf_eq_or_union_eq hinc hleaf with heq | ⟨X, hX𝒜, hunion⟩
    · rw [heq] at hmem
      exact hℬ.notMem_self hmem
    · exact hℬ.notMem_of_union_eq hmem (h𝒜ℬ hX𝒜) hunion
  · obtain ⟨w₁, w₂, w₃, h12, h13, h23, hiff⟩ := hT.exists_three_adj_of_not_isLeaf hleaf
    have hadj₁ : T.Adj v w₁ := (hiff w₁).2 (Or.inl rfl)
    have hadj₂ : T.Adj v w₂ := (hiff w₂).2 (Or.inr (Or.inl rfl))
    have hadj₃ : T.Adj v w₃ := (hiff w₃).2 (Or.inr (Or.inr rfl))
    have hinc₁ : IsTreeIncidence T v s(v, w₁) := isTreeIncidence_iff_adj.2 hadj₁
    have hinc₂ : IsTreeIncidence T v s(v, w₂) := isTreeIncidence_iff_adj.2 hadj₂
    have hinc₃ : IsTreeIncidence T v s(v, w₃) := isTreeIncidence_iff_adj.2 hadj₃
    have he12 : s(v, w₁) ≠ s(v, w₂) := sym2_mk_eq_left_iff.not.2 h12
    have he13 : s(v, w₁) ≠ s(v, w₃) := sym2_mk_eq_left_iff.not.2 h13
    have he23 : s(v, w₂) ≠ s(v, w₃) := sym2_mk_eq_left_iff.not.2 h23
    have hunion := hα.degree_three_union_eq hinc₁ hinc₂ hinc₃ he12 he13 he23
    exact hℬ.union_ne (hv_active _ hinc₁) (hv_active _ hinc₂) (hv_active _ hinc₃) hunion

/-! ## Proof of (3.2) -/

open Classical in
/-- The finite set of all incidences `(v, e)` in `T`. -/
noncomputable def incidencesFinset [Fintype ι] (T : SimpleGraph ι) : Finset (ι × Sym2 ι) :=
  Finset.univ.filter fun p ↦ IsTreeIncidence T p.1 p.2

open Classical in
/-- The sum `∑_{(v, e)} κ(α(v, e))` over all incidences `(v, e)` of `T`
(Graph Minors X, Section 3, proof of (3.2), condition (2), page 160). -/
noncomputable def kappaSum [Fintype ι] (κ : Set β → ℤ) (T : SimpleGraph ι)
    (α : ι → Sym2 ι → Set β) : ℤ :=
  ∑ p ∈ incidencesFinset T, κ (α p.1 p.2)

open Classical in
/-- The finite set of ordered non-exact forks `(t, e₁, e₂)` in `T` for `α`.
Each unordered non-exact fork `{e₁, e₂}` with nub `t` corresponds to the two ordered pairs
`(t, e₁, e₂)` and `(t, e₂, e₁)`, so minimizing the sum over ordered non-exact forks is equivalent
to minimizing the sum over unordered non-exact forks. -/
noncomputable def nonExactForksFinset [Fintype ι] (T : SimpleGraph ι)
    (α : ι → Sym2 ι → Set β) : Finset (ι × Sym2 ι × Sym2 ι) :=
  Finset.univ.filter fun f ↦ IsFork T f.1 f.2.1 f.2.2 ∧ ¬ IsExactFork α f.1 f.2.1 f.2.2

open Classical in
/-- The scaled distance weight `∑ 3^{|V(T)| - d(t)}` summed over all ordered non-exact forks,
which is `2 · 3^{|V(T)|} · ∑ 3^{-d(t)}` (since `d(t) < |V(T)|` for every vertex `t` in a tree `T`)
(Graph Minors X, Section 3, proof of (3.2), condition (3), page 160). -/
noncomputable def forkWeight [Fintype ι] (T : SimpleGraph ι) (t₀ : ι)
    (α : ι → Sym2 ι → Set β) : ℕ :=
  ∑ f ∈ nonExactForksFinset T α, 3 ^ (Fintype.card ι - T.dist t₀ f.1)

open Classical in
/-- The modified labelling `α'` in the proof of (3.2) (Graph Minors X, page 161):
for an edge `e₁ = s(t, t₁)` and set `A₂ = α(t, e₂)`,
`α'(t, e₁) = α(t, e₁) \ A₂`, `α'(t₁, e₁) = E \ (α(t, e₁) \ A₂)`, and `α'(v, e) = α(v, e)`
elsewhere. -/
noncomputable def updateLabelling (E : Set β) (α : ι → Sym2 ι → Set β)
    (t t₁ : ι) (A₂ : Set β) (v : ι) (e : Sym2 ι) : Set β :=
  if v = t ∧ e = s(t, t₁) then α t s(t, t₁) \ A₂
  else if v = t₁ ∧ e = s(t, t₁) then E \ (α t s(t, t₁) \ A₂)
  else α v e

private theorem updateLabelling_self_left (E : Set β) (α : ι → Sym2 ι → Set β)
    (t t₁ : ι) (A₂ : Set β) :
    updateLabelling E α t t₁ A₂ t s(t, t₁) = α t s(t, t₁) \ A₂ := by
  classical
  simp [updateLabelling]

private theorem updateLabelling_self_right (E : Set β) (α : ι → Sym2 ι → Set β)
    {t t₁ : ι} (hne : t ≠ t₁) (A₂ : Set β) :
    updateLabelling E α t t₁ A₂ t₁ s(t, t₁) = E \ (α t s(t, t₁) \ A₂) := by
  classical
  simp [updateLabelling, hne.symm]

private theorem updateLabelling_eq_of_ne {E : Set β} {α : ι → Sym2 ι → Set β}
    {t t₁ : ι} {A₂ : Set β} {v : ι} {e : Sym2 ι}
    (h1 : ¬ (v = t ∧ e = s(t, t₁))) (h2 : ¬ (v = t₁ ∧ e = s(t, t₁))) :
    updateLabelling E α t t₁ A₂ v e = α v e := by
  classical
  dsimp [updateLabelling]
  rw [ite_eq_right_iff.2 fun h ↦ (h1 h).elim, ite_eq_right_iff.2 fun h ↦ (h2 h).elim]

private theorem updateLabelling_isTreeLabelling [Fintype ι] {E : Set β} {κ : Set β → ℤ}
    {𝒜 : Set (Set β)} {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (hκ : IsConnectivityFunction E κ) (hα : IsTreeLabelling E κ 𝒜 T α)
    {t t₁ t₂ : ι} (hadj₁ : T.Adj t t₁) (hadj₂ : T.Adj t t₂) (hne12 : t₁ ≠ t₂)
    (heff : IsEfficient E κ (α t s(t, t₁) \ α t s(t, t₂))) :
    IsTreeLabelling E κ 𝒜 T (updateLabelling E α t t₁ (α t s(t, t₂))) := by
  classical
  let e₁ := s(t, t₁)
  let e₂ := s(t, t₂)
  let A₁ := α t e₁
  let A₂ := α t e₂
  have hne_tt₁ : t ≠ t₁ := hadj₁.ne
  have hα_t₁_sub : α t₁ e₁ ⊆ updateLabelling E α t t₁ A₂ t₁ e₁ := by
    intro x hx
    rw [updateLabelling_self_right E α hne_tt₁ A₂]
    rw [hα.compl_eq' hadj₁] at hx
    exact ⟨hx.1, fun h ↦ hx.2 h.1⟩
  refine ⟨hα.isTernaryTree, ?_, ?_, ?_, ?_⟩
  · intro v e hinc
    by_cases h1 : v = t ∧ e = e₁
    · rcases h1 with ⟨hvt, hfe⟩
      subst hvt hfe
      rw [updateLabelling_self_left]
      exact heff
    by_cases h2 : v = t₁ ∧ e = e₁
    · rcases h2 with ⟨hvt₁, hfe⟩
      subst hvt₁ hfe
      rw [updateLabelling_self_right E α hne_tt₁ A₂]
      exact heff.compl hκ
    · rw [updateLabelling_eq_of_ne h1 h2]
      exact hα.isEfficient hinc
  · intro u v hadj
    by_cases he : s(u, v) = e₁
    · have hmem : u ∈ s(t, t₁) ∧ v ∈ s(t, t₁) := by
        change u ∈ e₁ ∧ v ∈ e₁
        rw [← he]
        exact ⟨Sym2.mem_mk_left u v, Sym2.mem_mk_right u v⟩
      rcases Sym2.mem_iff.1 hmem.1 with h1 | h1 <;>
        rcases Sym2.mem_iff.1 hmem.2 with h2 | h2
      · subst h1 h2; exact (hadj.ne rfl).elim
      · subst h1 h2
        rw [updateLabelling_self_left, updateLabelling_self_right E α hne_tt₁ A₂,
          Set.sdiff_sdiff_cancel_left heff.1]
      · subst h1 h2
        rw [he, updateLabelling_self_left, updateLabelling_self_right E α hne_tt₁ A₂]
      · subst h1 h2; exact (hadj.ne rfl).elim
    · rw [updateLabelling_eq_of_ne (fun h ↦ he h.2) (fun h ↦ he h.2),
        updateLabelling_eq_of_ne (fun h ↦ he h.2) (fun h ↦ he h.2)]
      exact hα.compl_eq hadj
  · intro v e hinc hleaf
    have ht_not_leaf : ¬ IsLeaf T t :=
      hα.isTernaryTree.not_isLeaf_of_isFork
        ⟨isTreeIncidence_iff_adj.2 hadj₁, isTreeIncidence_iff_adj.2 hadj₂,
         sym2_mk_eq_left_iff.not.2 hne12⟩
    have hvt : v ≠ t := by rintro rfl; exact ht_not_leaf hleaf
    by_cases h2 : v = t₁ ∧ e = e₁
    · rcases h2 with ⟨hvt₁, hfe⟩
      subst hvt₁ hfe
      rcases hα.leaf_eq_or_union_eq hinc hleaf with heq | ⟨X, hX, hunion⟩
      · left
        refine Set.Subset.antisymm ?_ ?_
        · rw [updateLabelling_self_right E α hne_tt₁ A₂]; exact Set.sdiff_subset
        · have hsub := hα_t₁_sub
          rwa [heq] at hsub
      · right
        refine ⟨X, hX, Set.Subset.antisymm ?_ ?_⟩
        · refine Set.union_subset ?_ (hunion ▸ Set.subset_union_right)
          rw [updateLabelling_self_right E α hne_tt₁ A₂]; exact Set.sdiff_subset
        · have hsub := Set.union_subset_union_left X hα_t₁_sub
          rwa [hunion] at hsub
    · rw [updateLabelling_eq_of_ne (fun h ↦ hvt h.1) h2]
      exact hα.leaf_eq_or_union_eq hinc hleaf
  · intro v f₁ f₂ f₃ hf₁ hf₂ hf₃ h12 h13 h23
    have hsub_all : ∀ f, IsTreeIncidence T v f → updateLabelling E α t t₁ A₂ v f ⊆ E := by
      intro f hf
      by_cases a : v = t ∧ f = e₁
      · rcases a with ⟨hvt, hfe⟩; subst hvt hfe; rw [updateLabelling_self_left]; exact heff.1
      by_cases b : v = t₁ ∧ f = e₁
      · rcases b with ⟨hvt₁, hfe⟩; subst hvt₁ hfe
        rw [updateLabelling_self_right E α hne_tt₁ A₂]; exact Set.sdiff_subset
      · rw [updateLabelling_eq_of_ne a b]; exact hα.subset_of_inc hf
    refine Set.Subset.antisymm
      (Set.union_subset (Set.union_subset (hsub_all f₁ hf₁) (hsub_all f₂ hf₂)) (hsub_all f₃ hf₃))
      ?_
    intro x hx
    rw [← hα.degree_three_union_eq hf₁ hf₂ hf₃ h12 h13 h23] at hx
    by_cases hvt : v = t
    · subst hvt
      have ht_not_leaf : ¬ IsLeaf T v :=
        hα.isTernaryTree.not_isLeaf_of_isFork ⟨hf₁, hf₂, h12⟩
      have he₂_mem : e₂ = f₁ ∨ e₂ = f₂ ∨ e₂ = f₃ := by
        by_contra! hnot
        have hinc_e₂ : e₂ ∈ T.incidenceFinset v :=
          T.mem_incidenceFinset.2 (isTreeIncidence_iff_adj.2 hadj₂)
        have hinc_f₁ : f₁ ∈ T.incidenceFinset v := T.mem_incidenceFinset.2 hf₁
        have hinc_f₂ : f₂ ∈ T.incidenceFinset v := T.mem_incidenceFinset.2 hf₂
        have hinc_f₃ : f₃ ∈ T.incidenceFinset v := T.mem_incidenceFinset.2 hf₃
        have hcard3 : (T.incidenceFinset v).card = 3 := by
          rw [card_incidenceFinset_eq_degree]
          exact hα.isTernaryTree.degree_eq_three_of_not_isLeaf ht_not_leaf
        have hsub4 : ({e₂, f₁, f₂, f₃} : Finset (Sym2 ι)) ⊆ T.incidenceFinset v := by
          intro g hg
          simp only [Finset.mem_insert, Finset.mem_singleton] at hg
          rcases hg with rfl | rfl | rfl | rfl <;> assumption
        have hcard4 : ({e₂, f₁, f₂, f₃} : Finset (Sym2 ι)).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem, Finset.card_singleton] <;>
            simp [hnot.1, hnot.2.1, hnot.2.2, h12, h13, h23]
        have := Finset.card_le_card hsub4
        omega
      have hsub_at_t : ∀ f, α v f ⊆ updateLabelling E α v t₁ A₂ v f ∪ A₂ := by
        intro f y hy
        by_cases hfe : f = e₁
        · subst hfe
          rw [updateLabelling_self_left]
          by_cases hy2 : y ∈ A₂
          · exact Or.inr hy2
          · exact Or.inl ⟨hy, hy2⟩
        · rw [updateLabelling_eq_of_ne (fun h ↦ hfe h.2) (fun h ↦ hfe h.2)]
          exact Or.inl hy
      have hA₂_in : A₂ ⊆
          updateLabelling E α v t₁ A₂ v f₁ ∪
          updateLabelling E α v t₁ A₂ v f₂ ∪
          updateLabelling E α v t₁ A₂ v f₃ := by
        have he₂_ne_e₁ : e₂ ≠ e₁ := sym2_mk_eq_left_iff.not.2 hne12.symm
        have hα'_e₂ : updateLabelling E α v t₁ A₂ v e₂ = A₂ :=
          updateLabelling_eq_of_ne (fun h ↦ he₂_ne_e₁ h.2) (fun h ↦ he₂_ne_e₁ h.2)
        rcases he₂_mem with rfl | rfl | rfl
        · rw [hα'_e₂]; exact Set.subset_union_of_subset_left Set.subset_union_left _
        · rw [hα'_e₂]; exact Set.subset_union_of_subset_left Set.subset_union_right _
        · rw [hα'_e₂]; exact Set.subset_union_right
      rcases hx with (hx | hx) | hx
      · rcases hsub_at_t f₁ hx with hx' | hx2
        · exact Or.inl (Or.inl hx')
        · exact hA₂_in hx2
      · rcases hsub_at_t f₂ hx with hx' | hx2
        · exact Or.inl (Or.inr hx')
        · exact hA₂_in hx2
      · rcases hsub_at_t f₃ hx with hx' | hx2
        · exact Or.inr hx'
        · exact hA₂_in hx2
    · have hsub_not_t : ∀ f, α v f ⊆ updateLabelling E α t t₁ A₂ v f := by
        intro f
        by_cases h2 : v = t₁ ∧ f = e₁
        · rcases h2 with ⟨hvt₁, hfe⟩
          subst hvt₁ hfe
          exact hα_t₁_sub
        · rw [updateLabelling_eq_of_ne (fun h ↦ hvt h.1) h2]
      rcases hx with (hx | hx) | hx
      · exact Or.inl (Or.inl (hsub_not_t f₁ hx))
      · exact Or.inl (Or.inr (hsub_not_t f₂ hx))
      · exact Or.inr (hsub_not_t f₃ hx)

private theorem kappaSum_updateLabelling [Fintype ι] {E : Set β} {κ : Set β → ℤ}
    {𝒜 : Set (Set β)} {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (hκ : IsConnectivityFunction E κ) (hα : IsTreeLabelling E κ 𝒜 T α)
    {t t₁ t₂ : ι} (hadj₁ : T.Adj t t₁) :
    kappaSum κ T (updateLabelling E α t t₁ (α t s(t, t₂))) - kappaSum κ T α =
      2 * (κ (α t s(t, t₁) \ α t s(t, t₂)) - κ (α t s(t, t₁))) := by
  classical
  let e₁ := s(t, t₁)
  let A₁ := α t e₁
  let A₂ := α t s(t, t₂)
  let α' := updateLabelling E α t t₁ A₂
  have hne : t ≠ t₁ := hadj₁.ne
  have hp₁ : (t, e₁) ∈ incidencesFinset T := by
    simp [incidencesFinset, e₁, isTreeIncidence_iff_adj.2 hadj₁]
  have hp₂ : (t₁, e₁) ∈ incidencesFinset T := by
    simp [incidencesFinset, e₁, isTreeIncidence_symm hadj₁]
  have hp_ne : (t, e₁) ≠ (t₁, e₁) := fun h ↦ hne (Prod.ext_iff.1 h).1
  have hsum : ∀ β_lab : ι → Sym2 ι → Set β,
      kappaSum κ T β_lab =
        κ (β_lab t e₁) + κ (β_lab t₁ e₁) +
          ∑ p ∈ (incidencesFinset T).erase (t₁, e₁) |>.erase (t, e₁), κ (β_lab p.1 p.2) := by
    intro β_lab
    unfold kappaSum
    have hp₁' : (t, e₁) ∈ (incidencesFinset T).erase (t₁, e₁) :=
      Finset.mem_erase.2 ⟨hp_ne, hp₁⟩
    rw [← Finset.add_sum_erase _ _ hp₂, ← Finset.add_sum_erase _ _ hp₁']
    dsimp only
    omega
  have hrest_eq :
      ∑ p ∈ (incidencesFinset T).erase (t₁, e₁) |>.erase (t, e₁), κ (α' p.1 p.2) =
      ∑ p ∈ (incidencesFinset T).erase (t₁, e₁) |>.erase (t, e₁), κ (α p.1 p.2) := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hne1 : p ≠ (t, e₁) := (Finset.mem_erase.1 hp).1
    have hne2 : p ≠ (t₁, e₁) := (Finset.mem_erase.1 (Finset.mem_erase.1 hp).2).1
    dsimp only [α']
    rw [updateLabelling_eq_of_ne (fun h ↦ hne1 (Prod.ext h.1 h.2))
      (fun h ↦ hne2 (Prod.ext h.1 h.2))]
  have hA₁_sub : A₁ ⊆ E := hα.subset_of_inc (isTreeIncidence_iff_adj.2 hadj₁)
  have hA₁_diff_sub : A₁ \ A₂ ⊆ E := Set.sdiff_subset.trans hA₁_sub
  have hα'_t : α' t e₁ = A₁ \ A₂ := by simp [α', updateLabelling, e₁, A₁, A₂]
  have hα'_t₁ : α' t₁ e₁ = E \ (A₁ \ A₂) := by
    simp [α', updateLabelling, e₁, A₁, A₂, hne.symm]
  have hκ_α_t₁ : κ (α t₁ e₁) = κ A₁ := by
    rw [hα.compl_eq' hadj₁, ← hκ.compl_eq hA₁_sub]
  have hκ_α'_t₁ : κ (α' t₁ e₁) = κ (A₁ \ A₂) := by
    rw [hα'_t₁, ← hκ.compl_eq hA₁_diff_sub]
  change kappaSum κ T α' - kappaSum κ T α = 2 * (κ (A₁ \ A₂) - κ A₁)
  rw [hsum α', hsum α, hrest_eq, hα'_t, hκ_α'_t₁, hκ_α_t₁]
  dsimp only [A₁]
  omega

private theorem dist_lt_card_of_isTree [Fintype ι] {T : SimpleGraph ι} (hT : T.IsTree)
    (u v : ι) : T.dist u v < Fintype.card ι := by
  obtain ⟨p, hp, hp_len⟩ := (hT.connected u v).exists_path_of_dist
  have hlen : p.support.length = p.length + 1 := Walk.length_support p
  have hle : p.support.length ≤ Fintype.card ι := hp.support_nodup.length_le_card
  omega

private theorem forkWeight_updateLabelling_lt [Fintype ι] {E : Set β}
    {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β} (hT : IsTernaryTree T) (t₀ : ι)
    {t t₁ t₂ : ι} (hadj₁ : T.Adj t t₁) (hadj₂ : T.Adj t t₂) (hne12 : t₁ ≠ t₂)
    (hnon_exact : ¬ IsExactFork α t s(t, t₁) s(t, t₂))
    (hdist : T.dist t₀ t + 1 = T.dist t₀ t₁) :
    forkWeight T t₀ (updateLabelling E α t t₁ (α t s(t, t₂))) < forkWeight T t₀ α := by
  classical
  let e₁ := s(t, t₁)
  let e₂ := s(t, t₂)
  let A₂ := α t e₂
  let α' := updateLabelling E α t t₁ A₂
  have hne_tt₁ : t ≠ t₁ := hadj₁.ne
  have he12 : e₁ ≠ e₂ := sym2_mk_eq_left_iff.not.2 hne12
  have hinc₁ : IsTreeIncidence T t e₁ := isTreeIncidence_iff_adj.2 hadj₁
  have hinc₂ : IsTreeIncidence T t e₂ := isTreeIncidence_iff_adj.2 hadj₂
  let count (β_lab : ι → Sym2 ι → Set β) (v : ι) : ℕ :=
    (Finset.univ.filter fun p : Sym2 ι × Sym2 ι ↦
      IsFork T v p.1 p.2 ∧ ¬ IsExactFork β_lab v p.1 p.2).card
  -- Decompose the sum over vertices `v : ι`
  have hsum_by_vert : ∀ β_lab : ι → Sym2 ι → Set β,
      forkWeight T t₀ β_lab =
        ∑ v : ι, count β_lab v * 3 ^ (Fintype.card ι - T.dist t₀ v) := by
    intro β_lab
    unfold forkWeight nonExactForksFinset
    rw [← Finset.univ_product_univ, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    dsimp only [count]
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  -- For `v ≠ t` and `v ≠ t₁`, `count α' v = count α v`
  have hcount_other : ∀ v : ι, v ≠ t → v ≠ t₁ → count α' v = count α v := by
    intro v hvt hvt₁
    dsimp [count]
    congr 1
    ext ⟨f₁, f₂⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : α' v f₁ = α v f₁ :=
      updateLabelling_eq_of_ne (fun h ↦ hvt h.1) (fun h ↦ hvt₁ h.1)
    have h2 : α' v f₂ = α v f₂ :=
      updateLabelling_eq_of_ne (fun h ↦ hvt h.1) (fun h ↦ hvt₁ h.1)
    simp [IsExactFork, h1, h2]
  -- At `v = t`, `count α' t + 2 ≤ count α t`
  have hcount_t : count α' t + 2 ≤ count α t := by
    let S' := Finset.univ.filter fun p : Sym2 ι × Sym2 ι ↦
      IsFork T t p.1 p.2 ∧ ¬ IsExactFork α' t p.1 p.2
    let S := Finset.univ.filter fun p : Sym2 ι × Sym2 ι ↦
      IsFork T t p.1 p.2 ∧ ¬ IsExactFork α t p.1 p.2
    have hsub_at_t : ∀ f, α' t f ⊆ α t f := by
      intro f
      by_cases hfe : f = e₁
      · subst hfe
        have : α' t e₁ = α t e₁ \ A₂ := by simp [α', updateLabelling, e₁, A₂]
        rw [this]
        exact Set.sdiff_subset
      · dsimp only [α']
        rw [updateLabelling_eq_of_ne (fun h ↦ hfe h.2) (fun h ↦ hfe h.2)]
    have hS'_sub : S' ⊆ S := by
      intro ⟨f₁, f₂⟩ hp
      simp only [S', S, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      refine ⟨hp.1, fun hex ↦ hp.2 ?_⟩
      exact Set.Subset.antisymm
        ((Set.inter_subset_inter (hsub_at_t f₁) (hsub_at_t f₂)).trans hex.subset)
        (Set.empty_subset _)
    have hp12_S : (e₁, e₂) ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hinc₁, hinc₂, he12⟩, hnon_exact⟩
    have hp21_S : (e₂, e₁) ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨hinc₂, hinc₁, he12.symm⟩, ?_⟩
      simpa [IsExactFork, Set.inter_comm] using hnon_exact
    have hα'_t_e₁ : α' t e₁ = α t e₁ \ A₂ := by simp [α', updateLabelling, e₁, A₂]
    have hα'_t_e₂ : α' t e₂ = A₂ :=
      updateLabelling_eq_of_ne (fun h ↦ he12.symm h.2) (fun h ↦ he12.symm h.2)
    have hp12_not_S' : (e₁, e₂) ∉ S' := by
      intro hm
      apply (Finset.mem_filter.1 hm).2.2
      simp [IsExactFork, hα'_t_e₁, hα'_t_e₂]
    have hp21_not_S' : (e₂, e₁) ∉ S' := by
      intro hm
      apply (Finset.mem_filter.1 hm).2.2
      simp [IsExactFork, hα'_t_e₁, hα'_t_e₂]
    have hins : Insert.insert (e₁, e₂) (Insert.insert (e₂, e₁) S') ⊆ S := by
      intro p hp
      simp only [Finset.mem_insert] at hp
      rcases hp with rfl | rfl | hp
      · exact hp12_S
      · exact hp21_S
      · exact hS'_sub hp
    have hne_pair : (e₁, e₂) ≠ (e₂, e₁) := fun h ↦ he12 (Prod.ext_iff.1 h).1
    have hcard_ins :
        (Insert.insert (e₁, e₂) (Insert.insert (e₂, e₁) S')).card = S'.card + 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne_pair, hp12_not_S']),
        Finset.card_insert_of_notMem hp21_not_S']
    have := Finset.card_le_card hins
    change S'.card + 2 ≤ S.card
    omega
  -- At `v = t₁`, `count α' t₁ ≤ count α t₁ + 4`
  have hcount_t₁ : count α' t₁ ≤ count α t₁ + 4 := by
    let S' := Finset.univ.filter fun p : Sym2 ι × Sym2 ι ↦
      IsFork T t₁ p.1 p.2 ∧ ¬ IsExactFork α' t₁ p.1 p.2
    let S := Finset.univ.filter fun p : Sym2 ι × Sym2 ι ↦
      IsFork T t₁ p.1 p.2 ∧ ¬ IsExactFork α t₁ p.1 p.2
    by_cases hleaf₁ : IsLeaf T t₁
    · have hS'_empty : S' = ∅ := by
        ext ⟨f₁, f₂⟩
        simp only [S', Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        intro hf
        exact (hT.not_isLeaf_of_isFork hf hleaf₁).elim
      change S'.card ≤ S.card + 4
      rw [hS'_empty]
      simp
    · obtain ⟨w₁, w₂, hw₁, hw₂, hw12, hiff⟩ := hT.exists_other_two_adj hleaf₁ hadj₁.symm
      let g₁ := s(t₁, w₁)
      let g₂ := s(t₁, w₂)
      let P : Finset (Sym2 ι × Sym2 ι) := {(e₁, g₁), (g₁, e₁), (e₁, g₂), (g₂, e₁)}
      have hP_card : P.card ≤ 4 :=
        (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
          ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right
            ((Finset.card_insert_le _ _).trans (by simp)) 1)) 1)
      have hS'_sub_SP : S' ⊆ S ∪ P := by
        intro ⟨f₁, f₂⟩ hp
        simp only [S', S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        have hf_cases : ∀ f, IsTreeIncidence T t₁ f → f = e₁ ∨ f = g₁ ∨ f = g₂ := by
          intro f hf
          obtain ⟨w, hadj_w, rfl⟩ := isTreeIncidence_iff_exists_adj.1 hf
          rcases (hiff w).1 hadj_w with rfl | rfl | rfl
          · exact Or.inl Sym2.eq_swap
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
        by_cases hfe : f₁ = e₁ ∨ f₂ = e₁
        · right
          rcases hfe with rfl | rfl
          · rcases hf_cases f₂ hp.1.2.1 with rfl | rfl | rfl
            · exact (hp.1.2.2 rfl).elim
            · simp [P]
            · simp [P]
          · rcases hf_cases f₁ hp.1.1 with rfl | rfl | rfl
            · exact (hp.1.2.2 rfl).elim
            · simp [P]
            · simp [P]
        · left
          have h1 : α' t₁ f₁ = α t₁ f₁ :=
            updateLabelling_eq_of_ne (fun h ↦ hfe (Or.inl h.2)) (fun h ↦ hfe (Or.inl h.2))
          have h2 : α' t₁ f₂ = α t₁ f₂ :=
            updateLabelling_eq_of_ne (fun h ↦ hfe (Or.inr h.2)) (fun h ↦ hfe (Or.inr h.2))
          refine ⟨hp.1, ?_⟩
          simpa [IsExactFork, h1, h2] using hp.2
      have hle := (Finset.card_le_card hS'_sub_SP).trans (Finset.card_union_le S P)
      change S'.card ≤ S.card + 4
      omega
  -- Combine the vertex contributions
  let term (β_lab : ι → Sym2 ι → Set β) (v : ι) : ℕ :=
    count β_lab v * 3 ^ (Fintype.card ι - T.dist t₀ v)
  have hsum_split : ∀ β_lab : ι → Sym2 ι → Set β,
      forkWeight T t₀ β_lab =
        term β_lab t + term β_lab t₁ +
          ∑ v ∈ (Finset.univ.erase t₁).erase t, term β_lab v := by
    intro β_lab
    rw [hsum_by_vert β_lab]
    have ht₁_mem : t₁ ∈ (Finset.univ : Finset ι) := Finset.mem_univ t₁
    have ht_mem : t ∈ (Finset.univ : Finset ι).erase t₁ :=
      Finset.mem_erase.2 ⟨hne_tt₁, Finset.mem_univ t⟩
    rw [← Finset.add_sum_erase _ _ ht₁_mem, ← Finset.add_sum_erase _ _ ht_mem]
    dsimp only [term]
    omega
  have hrest_eq :
      ∑ v ∈ (Finset.univ.erase t₁).erase t, term α' v =
      ∑ v ∈ (Finset.univ.erase t₁).erase t, term α v := by
    refine Finset.sum_congr rfl fun v hv ↦ ?_
    have hvt : v ≠ t := (Finset.mem_erase.1 hv).1
    have hvt₁ : v ≠ t₁ := (Finset.mem_erase.1 (Finset.mem_erase.1 hv).2).1
    dsimp only [term]
    rw [hcount_other v hvt hvt₁]
  change forkWeight T t₀ α' < forkWeight T t₀ α
  rw [hsum_split α', hsum_split α, hrest_eq]
  have hd_lt : T.dist t₀ t₁ < Fintype.card ι := dist_lt_card_of_isTree hT.isTree t₀ t₁
  have hexp : Fintype.card ι - T.dist t₀ t = (Fintype.card ι - T.dist t₀ t₁) + 1 := by omega
  let w := 3 ^ (Fintype.card ι - T.dist t₀ t₁)
  have hw_pos : 0 < w := Nat.pos_of_ne_zero (pow_ne_zero _ (by decide))
  have hw_eq : 3 ^ (Fintype.card ι - T.dist t₀ t) = 3 * w := by
    change 3 ^ (Fintype.card ι - T.dist t₀ t) = 3 * 3 ^ (Fintype.card ι - T.dist t₀ t₁)
    rw [hexp, pow_succ, Nat.mul_comm]
  dsimp only [term]
  rw [hw_eq]
  change count α' t * (3 * w) + count α' t₁ * w + _ <
    count α t * (3 * w) + count α t₁ * w + _
  rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.add_mul, ← Nat.add_mul]
  have hlin : count α' t * 3 + count α' t₁ < count α t * 3 + count α t₁ := by omega
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right hlin hw_pos) _

/-- **Graph Minors X, (3.2)** (page 160):
"If there is a tree-labelling over $\mathscr{A}$ then there is an exact tree-labelling over
$\mathscr{A}$, using the same tree." -/
theorem theorem_3_2_proof [Fintype ι] {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    {T : SimpleGraph ι} {α₀ : ι → Sym2 ι → Set β}
    (hE : E.Finite) (hκ : IsConnectivityFunction E κ) (hα₀ : IsTreeLabelling E κ 𝒜 T α₀) :
    ∃ α, IsExactTreeLabelling E κ 𝒜 T α := by
  classical
  have hT := hα₀.isTernaryTree
  obtain ⟨t₀⟩ := hT.isTree.connected.nonempty
  -- Step 1: Choose a tree-labelling minimizing `kappaSum κ T α`.
  let S₁ : Set (ι → Sym2 ι → Set β) := {α | IsTreeLabelling E κ 𝒜 T α}
  have hS₁_ne : S₁.Nonempty := ⟨α₀, hα₀⟩
  have hS₁_img_fin : (kappaSum κ T '' S₁).Finite := by
    let F : Finset (ι × Sym2 ι) := incidencesFinset T
    let subFin : Set (Set β) := {X | X ⊆ E}
    have hsubFin : subFin.Finite := hE.finite_subsets
    have hmapFin : {f : F → Set β | ∀ p, f p ∈ subFin}.Finite :=
      Set.Finite.pi' fun _ ↦ hsubFin
    have himg_sub : kappaSum κ T '' S₁ ⊆
        (fun f : F → Set β ↦ ∑ p : F, κ (f p)) '' {f : F → Set β | ∀ p, f p ∈ subFin} := by
      rintro _ ⟨α, hα, rfl⟩
      refine ⟨fun p ↦ α p.1.1 p.1.2, fun p ↦ ?_, ?_⟩
      · have hp : IsTreeIncidence T p.1.1 p.1.2 := (Finset.mem_filter.1 p.2).2
        exact hα.subset_of_inc hp
      · exact Finset.sum_attach F fun p ↦ κ (α p.1 p.2)
    exact (hmapFin.image _).subset himg_sub
  obtain ⟨α₁, hα₁_mem, hα₁_min⟩ :=
    Set.Finite.exists_minimalFor' (kappaSum κ T) S₁ hS₁_img_fin hS₁_ne
  -- Step 2: Subject to minimizing `kappaSum`, minimize `forkWeight T t₀ α`.
  let S₂ : Set (ι → Sym2 ι → Set β) :=
    {α | IsTreeLabelling E κ 𝒜 T α ∧ kappaSum κ T α = kappaSum κ T α₁}
  have hS₂_ne : S₂.Nonempty := ⟨α₁, hα₁_mem, rfl⟩
  have hS₂_img_fin : (forkWeight T t₀ '' S₂).Finite := by
    let P := (Finset.univ : Finset (ι × Sym2 ι × Sym2 ι)).powerset
    have himg_sub : forkWeight T t₀ '' S₂ ⊆
        (fun s : Finset (ι × Sym2 ι × Sym2 ι) ↦
          ∑ f ∈ s, 3 ^ (Fintype.card ι - T.dist t₀ f.1)) '' (P : Set _) := by
      rintro _ ⟨α, _, rfl⟩
      exact ⟨nonExactForksFinset T α, Finset.mem_powerset.2 (Finset.subset_univ _), rfl⟩
    exact (P.finite_toSet.image _).subset himg_sub
  obtain ⟨α, ⟨hα_tree, hα_ksum⟩, hα_min⟩ :=
    Set.Finite.exists_minimalFor' (forkWeight T t₀) S₂ hS₂_img_fin hS₂_ne
  have hα_kmin : ∀ α', IsTreeLabelling E κ 𝒜 T α' → kappaSum κ T α ≤ kappaSum κ T α' := by
    intro α' hα'
    rw [hα_ksum]
    exact not_lt.1 fun hlt ↦ not_lt_of_ge (hα₁_min hα' hlt.le) hlt
  refine ⟨α, hα_tree, ?_⟩
  intro t e₁ e₂ hfork
  by_contra hnon_exact
  obtain ⟨t₁, hadj₁, rfl⟩ := isTreeIncidence_iff_exists_adj.1 hfork.1
  obtain ⟨t₂, hadj₂, rfl⟩ := isTreeIncidence_iff_exists_adj.1 hfork.2.1
  have hne12 : t₁ ≠ t₂ := fun h ↦ hfork.2.2 (by rw [h])
  -- Claim: for any two distinct neighbors `a, b` of `t`, `κ (α t s(t, a)) ≤ κ (α t s(t, a) \ α t
  -- s(t, b))`.
  have hclaim : ∀ {a b : ι}, T.Adj t a → T.Adj t b → a ≠ b →
      κ (α t s(t, a)) ≤ κ (α t s(t, a) \ α t s(t, b)) := by
    intro a b ha hb hab
    have hA_eff : IsEfficient E κ (α t s(t, a)) :=
      hα_tree.isEfficient (isTreeIncidence_iff_adj.2 ha)
    by_cases hk_le : κ (α t s(t, a) \ α t s(t, b)) ≤ 0
    · have heff' : IsEfficient E κ (α t s(t, a) \ α t s(t, b)) :=
        ⟨Set.sdiff_subset.trans hA_eff.1, hk_le⟩
      have htree' := updateLabelling_isTreeLabelling hκ hα_tree ha hb hab heff'
      have hle_sum := hα_kmin _ htree'
      have hdiff_sum := kappaSum_updateLabelling (t₂ := b) hκ hα_tree ha
      omega
    · have := hA_eff.2
      omega
  have hle1 : κ (α t s(t, t₁)) ≤ κ (α t s(t, t₁) \ α t s(t, t₂)) := hclaim hadj₁ hadj₂ hne12
  have hle2 : κ (α t s(t, t₂)) ≤ κ (α t s(t, t₂) \ α t s(t, t₁)) := hclaim hadj₂ hadj₁ hne12.symm
  -- Submodularity inequality: `κ (A₂ \ A₁) + κ (A₁ \ A₂) ≤ κ A₁ + κ A₂`.
  have hA₁_sub : α t s(t, t₁) ⊆ E := hα_tree.subset_of_inc (isTreeIncidence_iff_adj.2 hadj₁)
  have hA₂_sub : α t s(t, t₂) ⊆ E := hα_tree.subset_of_inc (isTreeIncidence_iff_adj.2 hadj₂)
  have hsubmod := hκ.submodular hA₁_sub (Set.sdiff_subset (s := E) (t := α t s(t, t₂)))
  have hinter_eq : α t s(t, t₁) ∩ (E \ α t s(t, t₂)) = α t s(t, t₁) \ α t s(t, t₂) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sdiff]
    exact ⟨fun ⟨hx1, _, hx2⟩ ↦ ⟨hx1, hx2⟩, fun ⟨hx1, hx2⟩ ↦ ⟨hx1, hA₁_sub hx1, hx2⟩⟩
  have hunion_compl_eq :
      E \ (α t s(t, t₁) ∪ (E \ α t s(t, t₂))) = α t s(t, t₂) \ α t s(t, t₁) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, not_or, not_and, not_not]
    exact ⟨fun ⟨hxE, hx1, hx2⟩ ↦ ⟨hx2 hxE, hx1⟩,
      fun ⟨hx2, hx1⟩ ↦ ⟨hA₂_sub hx2, hx1, fun _ ↦ hx2⟩⟩
  have hκ_union :
      κ (α t s(t, t₁) ∪ (E \ α t s(t, t₂))) = κ (α t s(t, t₂) \ α t s(t, t₁)) := by
    rw [hκ.compl_eq (Set.union_subset hA₁_sub Set.sdiff_subset), hunion_compl_eq]
  have hκ_compl2 : κ (E \ α t s(t, t₂)) = κ (α t s(t, t₂)) := (hκ.compl_eq hA₂_sub).symm
  rw [hinter_eq, hκ_union, hκ_compl2] at hsubmod
  -- Hence equality holds throughout!
  have heq1 : κ (α t s(t, t₁) \ α t s(t, t₂)) = κ (α t s(t, t₁)) := by omega
  have heq2 : κ (α t s(t, t₂) \ α t s(t, t₁)) = κ (α t s(t, t₂)) := by omega
  -- At least one of `t₁, t₂` has distance `T.dist t₀ t + 1`.
  have hdist_or : T.dist t₀ t + 1 = T.dist t₀ t₁ ∨ T.dist t₀ t + 1 = T.dist t₀ t₂ := by
    rcases hT.isTree.dist_eq_dist_add_one_of_adj t₀ hadj₁ with hd1 | hd1
    · rcases hT.isTree.dist_eq_dist_add_one_of_adj t₀ hadj₂ with hd2 | hd2
      · exfalso
        obtain ⟨p, hp, hp_len⟩ := (hT.isTree.connected t₀ t).exists_path_of_dist
        obtain ⟨q₁, hq₁, hq₁_len⟩ := (hT.isTree.connected t₀ t₁).exists_path_of_dist
        obtain ⟨q₂, hq₂, hq₂_len⟩ := (hT.isTree.connected t₀ t₂).exists_path_of_dist
        have ht_not_q₁ : t ∉ q₁.support := by
          intro ht
          have := congrArg Walk.length (hT.isTree.isAcyclic.path_concat hp hq₁ hadj₁ ht)
          rw [Walk.length_concat, hp_len, hq₁_len] at this
          omega
        have ht_not_q₂ : t ∉ q₂.support := by
          intro ht
          have := congrArg Walk.length (hT.isTree.isAcyclic.path_concat hp hq₂ hadj₂ ht)
          rw [Walk.length_concat, hp_len, hq₂_len] at this
          omega
        have ht₁_p : t₁ ∈ p.support :=
          hT.isTree.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
            hp hq₁ hadj₁ ht_not_q₁
        have ht₂_p : t₂ ∈ p.support :=
          hT.isTree.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
            hp hq₂ hadj₂ ht_not_q₂
        have hpen₁ : t₁ = p.penultimate :=
          hT.isTree.isAcyclic.eq_penultimate_of_adj_end hp hadj₁ ht₁_p
        have hpen₂ : t₂ = p.penultimate :=
          hT.isTree.isAcyclic.eq_penultimate_of_adj_end hp hadj₂ ht₂_p
        exact hne12 (hpen₁.trans hpen₂.symm)
      · exact Or.inr hd2.symm
    · exact Or.inl hd1.symm
  -- Apply the perturbation to whichever of `t₁, t₂` has larger distance from `t₀`.
  have hcontra : ∀ {a b : ι}, T.Adj t a → T.Adj t b → a ≠ b →
      ¬ IsExactFork α t s(t, a) s(t, b) →
      κ (α t s(t, a) \ α t s(t, b)) = κ (α t s(t, a)) →
      T.dist t₀ t + 1 = T.dist t₀ a → False := by
    intro a b ha hb hab hne_ex hkeq hda
    have hA_eff : IsEfficient E κ (α t s(t, a)) :=
      hα_tree.isEfficient (isTreeIncidence_iff_adj.2 ha)
    have heff' : IsEfficient E κ (α t s(t, a) \ α t s(t, b)) :=
      ⟨Set.sdiff_subset.trans hA_eff.1, hkeq.trans_le hA_eff.2⟩
    let α' := updateLabelling E α t a (α t s(t, b))
    have htree' : IsTreeLabelling E κ 𝒜 T α' :=
      updateLabelling_isTreeLabelling hκ hα_tree ha hb hab heff'
    have hksum' : kappaSum κ T α' = kappaSum κ T α₁ := by
      have hdiff : kappaSum κ T α' - kappaSum κ T α =
          2 * (κ (α t s(t, a) \ α t s(t, b)) - κ (α t s(t, a))) :=
        kappaSum_updateLabelling (t₂ := b) hκ hα_tree ha
      omega
    have hα'_S₂ : α' ∈ S₂ := ⟨htree', hksum'⟩
    have hfw_lt : forkWeight T t₀ α' < forkWeight T t₀ α :=
      forkWeight_updateLabelling_lt hT t₀ ha hb hab hne_ex hda
    have hfw_ge : forkWeight T t₀ α ≤ forkWeight T t₀ α' := hα_min hα'_S₂ hfw_lt.le
    omega
  rcases hdist_or with hd1 | hd2
  · exact hcontra hadj₁ hadj₂ hne12 hnon_exact heq1 hd1
  · have hnon_exact' : ¬ IsExactFork α t s(t, t₂) s(t, t₁) := by
      simpa [IsExactFork, Set.inter_comm] using hnon_exact
    exact hcontra hadj₂ hadj₁ hne12.symm hnon_exact' heq2 hd2

/-! ## Proof of (3.3) -/

/-- The vertex set of the component `T₀` of `T \ f` containing `u`
(Graph Minors X, Section 3, (3.3), page 161). -/
@[expose] def treeComponent (T : SimpleGraph ι) (u : ι) (f : Sym2 ι) : Set ι :=
  {x : ι | (T.deleteEdges {f}).Reachable u x}

/-- The set of leaf incidences `(v, e)` in `T` with `v` in the component of `T \ f` containing `u`
(Graph Minors X, Section 3, (3.3), page 161). -/
@[expose] def leafIncidencesIn [Fintype ι] (T : SimpleGraph ι) (u : ι) (f : Sym2 ι) :
    Set (ι × Sym2 ι) :=
  {p : ι × Sym2 ι | IsTreeIncidence T p.1 p.2 ∧ IsLeaf T p.1 ∧ p.1 ∈ treeComponent T u f}

theorem reachable_deleteEdges_iff_notMem_edges {T : SimpleGraph ι} (hT : T.IsTree)
    {u w x : ι} {p : T.Walk u x} (hp : p.IsPath) :
    (T.deleteEdges {s(u, w)}).Reachable u x ↔ s(u, w) ∉ p.edges := by
  rw [reachable_deleteEdges_iff_exists_walk]
  constructor
  · rintro ⟨q, hq⟩
    classical
    have hqp : q.toPath.val = p :=
      congrArg Subtype.val ((hT.isAcyclic.subsingleton_path u x).elim q.toPath ⟨p, hp⟩)
    intro hmem
    rw [← hqp] at hmem
    exact hq (Walk.edges_toPath_subset_edges q hmem)
  · intro hnot
    exact ⟨p, hnot⟩

theorem mem_edges_iff_mem_support_of_adj {T : SimpleGraph ι} (hT : T.IsTree)
    {u w x : ι} (hadj : T.Adj u w) {p : T.Walk u x} (hp : p.IsPath) :
    s(u, w) ∈ p.edges ↔ w ∈ p.support := by
  constructor
  · intro hmem
    rw [Sym2.eq_swap] at hmem
    exact Walk.fst_mem_support_of_mem_edges p hmem
  · intro hw
    have hwsnd : w = p.snd := hT.isAcyclic.eq_snd_of_adj_start hp hadj hw
    rw [hwsnd]
    cases p with
    | nil =>
      rw [Walk.support_nil, List.mem_singleton] at hw
      exact (hadj.ne hw.symm).elim
    | cons _ _ => simp

theorem mem_treeComponent_iff_notMem_support {T : SimpleGraph ι} (hT : T.IsTree)
    {u w x : ι} (hadj : T.Adj u w) {p : T.Walk u x} (hp : p.IsPath) :
    x ∈ treeComponent T u s(u, w) ↔ w ∉ p.support := by
  change (T.deleteEdges {s(u, w)}).Reachable u x ↔ w ∉ p.support
  rw [reachable_deleteEdges_iff_notMem_edges hT hp,
    mem_edges_iff_mem_support_of_adj hT hadj hp]

theorem notMem_treeComponent_iff {T : SimpleGraph ι} (hT : T.IsTree)
    {u w x : ι} (hadj : T.Adj u w) :
    x ∉ treeComponent T u s(u, w) ↔ x ∈ treeComponent T w s(w, u) := by
  constructor
  · intro hnot
    obtain ⟨p, hp⟩ := hT.connected.exists_isPath u x
    have hw : w ∈ p.support := by
      by_contra hwnot
      exact hnot ((mem_treeComponent_iff_notMem_support hT hadj hp).2 hwnot)
    have hwsnd : w = p.snd := hT.isAcyclic.eq_snd_of_adj_start hp hadj hw
    cases p with
    | nil =>
      rw [Walk.support_nil, List.mem_singleton] at hw
      exact (hadj.ne hw.symm).elim
    | cons hadj' q =>
      simp only [Walk.snd_cons] at hwsnd
      subst hwsnd
      rw [Walk.cons_isPath_iff] at hp
      exact (mem_treeComponent_iff_notMem_support hT hadj.symm hp.1).2 hp.2
  · intro hx_w hx_u
    have hx_w' : (T.deleteEdges {s(u, w)}).Reachable w x := by
      simpa [treeComponent, Sym2.eq_swap] using hx_w
    have huw : (T.deleteEdges {s(u, w)}).Reachable u w := hx_u.trans hx_w'.symm
    have hp_edge : (Walk.cons hadj Walk.nil).IsPath := Walk.IsPath.nil.cons (by simp [hadj.ne])
    have hnot_edge := (reachable_deleteEdges_iff_notMem_edges hT hp_edge).1 huw
    exact hnot_edge (by simp)

theorem not_reachable_deleteEdges_iff_treeComponent {T : SimpleGraph ι} (hT : T.IsTree)
    {u w t₁ t₂ : ι} (hadj : T.Adj u w) :
    ¬ (T.deleteEdges {s(u, w)}).Reachable t₁ t₂ ↔
      (t₁ ∈ treeComponent T u s(u, w) ∧ t₂ ∈ treeComponent T w s(w, u)) ∨
      (t₁ ∈ treeComponent T w s(w, u) ∧ t₂ ∈ treeComponent T u s(u, w)) := by
  have h1 := notMem_treeComponent_iff hT hadj (x := t₁)
  have h2 := notMem_treeComponent_iff hT hadj (x := t₂)
  constructor
  · intro hnot
    by_cases ht₁ : t₁ ∈ treeComponent T u s(u, w)
    · refine Or.inl ⟨ht₁, h2.1 fun ht₂ ↦ hnot (ht₁.symm.trans ht₂)⟩
    · refine Or.inr ⟨h1.1 ht₁, ?_⟩
      by_contra ht₂
      have ht₁' : (T.deleteEdges {s(u, w)}).Reachable w t₁ := by
        simpa [treeComponent, Sym2.eq_swap] using h1.1 ht₁
      have ht₂' : (T.deleteEdges {s(u, w)}).Reachable w t₂ := by
        simpa [treeComponent, Sym2.eq_swap] using h2.1 ht₂
      exact hnot (ht₁'.symm.trans ht₂')
  · rintro (⟨ht₁, ht₂⟩ | ⟨ht₁, ht₂⟩) hreach
    · exact (h2.2 ht₂) (ht₁.trans hreach)
    · exact (h1.2 ht₁) (ht₂.trans hreach.symm)

theorem treeComponent_eq_singleton_of_isLeaf [Fintype ι] {T : SimpleGraph ι}
    (hT : IsTernaryTree T) {u w : ι} (hadj : T.Adj u w) (hleaf : IsLeaf T u) :
    treeComponent T u s(u, w) = {u} := by
  ext x
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    obtain ⟨p, hp⟩ := hT.isTree.connected.exists_isPath u x
    have hw_not : w ∉ p.support := (mem_treeComponent_iff_notMem_support hT.isTree hadj hp).1 hx
    have hnot_nil : ¬ p.Nil := Walk.not_nil_of_ne (Ne.symm hne)
    have hadj_snd : T.Adj u p.snd := p.adj_snd hnot_nil
    obtain ⟨z, _, hz_uniq⟩ := hT.exists_adj_of_isLeaf hleaf
    have hw_eq : p.snd = w := (hz_uniq p.snd hadj_snd).trans (hz_uniq w hadj).symm
    exact hw_not (hw_eq ▸ p.snd_mem_tail_support hnot_nil |> List.mem_of_mem_tail)
  · rintro rfl
    exact Reachable.rfl

theorem treeComponent_split_of_not_isLeaf [Fintype ι] {T : SimpleGraph ι}
    (hT : IsTernaryTree T) {u w u₁ u₂ : ι} (hadj : T.Adj u w)
    (hw₁ : w ≠ u₁) (hw₂ : w ≠ u₂) (hu12 : u₁ ≠ u₂)
    (hiff : ∀ x, T.Adj u x ↔ x = w ∨ x = u₁ ∨ x = u₂) :
    treeComponent T u s(u, w) =
      {u} ∪ treeComponent T u₁ s(u₁, u) ∪ treeComponent T u₂ s(u₂, u) ∧
    treeComponent T u₁ s(u₁, u) ∩ treeComponent T u₂ s(u₂, u) = ∅ ∧
    u ∉ treeComponent T u₁ s(u₁, u) ∧
    u ∉ treeComponent T u₂ s(u₂, u) := by
  have hadj₁ : T.Adj u u₁ := (hiff u₁).2 (Or.inr (Or.inl rfl))
  have hadj₂ : T.Adj u u₂ := (hiff u₂).2 (Or.inr (Or.inr rfl))
  have hmem_sub : ∀ {v : ι} (hadj_v : T.Adj u v) (hwv : w ≠ v) (x : ι),
      x ∈ treeComponent T v s(v, u) ↔
        ∃ (p : T.Walk v x), p.IsPath ∧ u ∉ p.support := by
    intro v hadj_v _ x
    obtain ⟨p, hp⟩ := hT.isTree.connected.exists_isPath v x
    rw [mem_treeComponent_iff_notMem_support hT.isTree hadj_v.symm hp]
    exact ⟨fun h ↦ ⟨p, hp, h⟩, fun ⟨q, hq, huq⟩ ↦ by
      have hqp : q = p :=
        congrArg Subtype.val ((hT.isTree.isAcyclic.subsingleton_path v x).elim ⟨q, hq⟩ ⟨p, hp⟩)
      rwa [← hqp]⟩
  have hu_not₁ : u ∉ treeComponent T u₁ s(u₁, u) := by
    rw [hmem_sub hadj₁ hw₁ u]
    rintro ⟨p, _, hu⟩
    exact hu p.end_mem_support
  have hu_not₂ : u ∉ treeComponent T u₂ s(u₂, u) := by
    rw [hmem_sub hadj₂ hw₂ u]
    rintro ⟨p, _, hu⟩
    exact hu p.end_mem_support
  have hsub₁ : treeComponent T u₁ s(u₁, u) ⊆ treeComponent T u s(u, w) := by
    intro x hx
    obtain ⟨p₁, hp₁, hu_not⟩ := (hmem_sub hadj₁ hw₁ x).1 hx
    have hp : (Walk.cons hadj₁ p₁).IsPath := (Walk.cons_isPath_iff hadj₁ p₁).2 ⟨hp₁, hu_not⟩
    rw [mem_treeComponent_iff_notMem_support hT.isTree hadj hp]
    intro hw_mem
    have hwsnd := hT.isTree.isAcyclic.eq_snd_of_adj_start hp hadj hw_mem
    simp only [Walk.snd_cons] at hwsnd
    exact hw₁ hwsnd
  have hsub₂ : treeComponent T u₂ s(u₂, u) ⊆ treeComponent T u s(u, w) := by
    intro x hx
    obtain ⟨p₂, hp₂, hu_not⟩ := (hmem_sub hadj₂ hw₂ x).1 hx
    have hp : (Walk.cons hadj₂ p₂).IsPath := (Walk.cons_isPath_iff hadj₂ p₂).2 ⟨hp₂, hu_not⟩
    rw [mem_treeComponent_iff_notMem_support hT.isTree hadj hp]
    intro hw_mem
    have hwsnd := hT.isTree.isAcyclic.eq_snd_of_adj_start hp hadj hw_mem
    simp only [Walk.snd_cons] at hwsnd
    exact hw₂ hwsnd
  have hdisj : treeComponent T u₁ s(u₁, u) ∩ treeComponent T u₂ s(u₂, u) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx₁, hx₂⟩
    obtain ⟨p₁, hp₁, hu₁⟩ := (hmem_sub hadj₁ hw₁ x).1 hx₁
    obtain ⟨p₂, hp₂, hu₂⟩ := (hmem_sub hadj₂ hw₂ x).1 hx₂
    have hpath₁ : (Walk.cons hadj₁ p₁).IsPath := (Walk.cons_isPath_iff hadj₁ p₁).2 ⟨hp₁, hu₁⟩
    have hpath₂ : (Walk.cons hadj₂ p₂).IsPath := (Walk.cons_isPath_iff hadj₂ p₂).2 ⟨hp₂, hu₂⟩
    have heq : Walk.cons hadj₁ p₁ = Walk.cons hadj₂ p₂ :=
      congrArg Subtype.val
        ((hT.isTree.isAcyclic.subsingleton_path u x).elim ⟨_, hpath₁⟩ ⟨_, hpath₂⟩)
    have hsnd := congrArg Walk.snd heq
    simp only [Walk.snd_cons] at hsnd
    exact hu12 hsnd
  refine ⟨?_, hdisj, hu_not₁, hu_not₂⟩
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_cases hxu : x = u
    · exact Or.inl (Or.inl hxu)
    · obtain ⟨p, hp⟩ := hT.isTree.connected.exists_isPath u x
      have hw_not : w ∉ p.support := (mem_treeComponent_iff_notMem_support hT.isTree hadj hp).1 hx
      cases p with
      | nil => exact (hxu rfl).elim
      | @cons _ v _ hadj_v p' =>
        obtain ⟨hp', hu_not_p'⟩ := (Walk.cons_isPath_iff hadj_v p').1 hp
        rcases (hiff v).1 hadj_v with rfl | rfl | rfl
        · exact (hw_not (List.mem_cons_of_mem u p'.start_mem_support)).elim
        · exact Or.inl (Or.inr ((hmem_sub hadj₁ hw₁ x).2 ⟨p', hp', hu_not_p'⟩))
        · exact Or.inr ((hmem_sub hadj₂ hw₂ x).2 ⟨p', hp', hu_not_p'⟩)
  · rintro ((rfl | hx₁) | hx₂)
    · exact Reachable.rfl
    · exact hsub₁ hx₁
    · exact hsub₂ hx₂

theorem exists_leaf_in_treeComponent [Fintype ι] {T : SimpleGraph ι}
    (hT : IsTernaryTree T) {u w : ι} (hadj : T.Adj u w) :
    ∃ t ∈ leafSet T, t ∈ treeComponent T u s(u, w) := by
  suffices ∀ n : ℕ, ∀ u w : ι, T.Adj u w → (treeComponent T u s(u, w)).ncard = n →
      ∃ t ∈ leafSet T, t ∈ treeComponent T u s(u, w) from
    this (treeComponent T u s(u, w)).ncard u w hadj rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro u w hadj hcard
    by_cases hleaf : IsLeaf T u
    · exact ⟨u, hleaf, Reachable.rfl⟩
    · obtain ⟨u₁, u₂, hw₁, hw₂, hu12, hiff⟩ := hT.exists_other_two_adj hleaf hadj
      have hadj₁ : T.Adj u u₁ := (hiff u₁).2 (Or.inr (Or.inl rfl))
      obtain ⟨hcomp_eq, _, hu_not₁, _⟩ :=
        treeComponent_split_of_not_isLeaf hT hadj hw₁ hw₂ hu12 hiff
      have hsub₁ : treeComponent T u₁ s(u₁, u) ⊆ treeComponent T u s(u, w) := by
        rw [hcomp_eq]
        exact Set.subset_union_of_subset_left Set.subset_union_right _
      have hlt₁ : (treeComponent T u₁ s(u₁, u)).ncard < n := by
        rw [← hcard]
        refine Set.ncard_lt_ncard ⟨hsub₁, fun h ↦ hu_not₁ (h Reachable.rfl)⟩ (Set.toFinite _)
      obtain ⟨t, ht_leaf, ht_mem⟩ := ih _ hlt₁ u₁ u hadj₁.symm rfl
      exact ⟨t, ht_leaf, hsub₁ ht_mem⟩

theorem IsTernaryTree.two_le_ncard_leafSet [Fintype ι] {T : SimpleGraph ι}
    (hT : IsTernaryTree T) : 2 ≤ (leafSet T).ncard := by
  classical
  obtain ⟨u⟩ := hT.isTree.connected.nonempty
  have hex_adj : ∃ w, T.Adj u w := by
    by_cases hleaf : IsLeaf T u
    · obtain ⟨w, hw, _⟩ := hT.exists_adj_of_isLeaf hleaf
      exact ⟨w, hw⟩
    · obtain ⟨w₁, _, _, _, _, _, hiff⟩ := hT.exists_three_adj_of_not_isLeaf hleaf
      exact ⟨w₁, (hiff w₁).2 (Or.inl rfl)⟩
  obtain ⟨w, hadj⟩ := hex_adj
  obtain ⟨t₁, ht₁_leaf, ht₁_comp⟩ := exists_leaf_in_treeComponent hT hadj
  obtain ⟨t₂, ht₂_leaf, ht₂_comp⟩ := exists_leaf_in_treeComponent hT hadj.symm
  have hne : t₁ ≠ t₂ := fun h ↦
    (notMem_treeComponent_iff hT.isTree hadj).2 (h ▸ ht₂_comp) ht₁_comp
  have hsub : ({t₁, t₂} : Set ι) ⊆ leafSet T := by
    rintro x (rfl | rfl) <;> assumption
  have hcard : ({t₁, t₂} : Set ι).ncard = 2 := Set.ncard_pair hne
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem IsExactTreeLabelling.compl_eq_union_of_degree_three [Fintype ι] {E : Set β}
    {κ : Set β → ℤ} {𝒜 : Set (Set β)} {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (hα : IsExactTreeLabelling E κ 𝒜 T α) {u : ι} {f f₁ f₂ : Sym2 ι}
    (hf : IsTreeIncidence T u f) (hf₁ : IsTreeIncidence T u f₁) (hf₂ : IsTreeIncidence T u f₂)
    (hne1 : f ≠ f₁) (hne2 : f ≠ f₂) (hne12 : f₁ ≠ f₂) :
    α u f₁ ∪ α u f₂ = E \ α u f ∧ α u f₁ ∩ α u f₂ = ∅ := by
  have hunion := hα.isTreeLabelling.degree_three_union_eq hf hf₁ hf₂ hne1 hne2 hne12
  have hdisj1 : α u f ∩ α u f₁ = ∅ := hα.isExactFork ⟨hf, hf₁, hne1⟩
  have hdisj2 : α u f ∩ α u f₂ = ∅ := hα.isExactFork ⟨hf, hf₂, hne2⟩
  have hdisj12 : α u f₁ ∩ α u f₂ = ∅ := hα.isExactFork ⟨hf₁, hf₂, hne12⟩
  refine ⟨?_, hdisj12⟩
  ext x
  have hx1 : x ∈ α u f → x ∉ α u f₁ := fun h1 h2 ↦
    Set.notMem_empty x (hdisj1 ▸ ⟨h1, h2⟩)
  have hx2 : x ∈ α u f → x ∉ α u f₂ := fun h1 h2 ↦
    Set.notMem_empty x (hdisj2 ▸ ⟨h1, h2⟩)
  simp only [Set.mem_union, Set.mem_sdiff]
  constructor
  · rintro (h | h)
    · exact ⟨hunion ▸ Or.inl (Or.inr h), fun hf_mem ↦ hx1 hf_mem h⟩
    · exact ⟨hunion ▸ Or.inr h, fun hf_mem ↦ hx2 hf_mem h⟩
  · rintro ⟨hxE, hnot⟩
    rw [← hunion] at hxE
    rcases hxE with (h | h) | h
    · exact (hnot h).elim
    · exact Or.inl h
    · exact Or.inr h

/-- **Graph Minors X, (3.3)** (page 161):
"Let $(T, \alpha)$ be an exact tree-labelling over $\mathscr{A}$, and let $(u, f)$ be an
incidence in $T$. Let $T_0$ be the component of $T \setminus f$ which contains $u$. Then, as
$(v, e)$ ranges over all incidences of $T$ such that $v$ is a leaf of $T$ and $v \in
V(T_0)$, the sets $E - \alpha(v, e)$ are mutually disjoint and have union $E - \alpha(u,
f)$." -/
theorem theorem_3_3_proof [Fintype ι] {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (hα : IsExactTreeLabelling E κ 𝒜 T α) {u : ι} {f : Sym2 ι} (huf : IsTreeIncidence T u f) :
    (leafIncidencesIn T u f).PairwiseDisjoint (fun p ↦ E \ α p.1 p.2) ∧
    (⋃ p ∈ leafIncidencesIn T u f, (E \ α p.1 p.2)) = E \ α u f := by
  have hT := hα.isTreeLabelling.isTernaryTree
  suffices ∀ n : ℕ, ∀ u : ι, ∀ f : Sym2 ι, IsTreeIncidence T u f →
      (treeComponent T u f).ncard = n →
      (leafIncidencesIn T u f).PairwiseDisjoint (fun p ↦ E \ α p.1 p.2) ∧
      (⋃ p ∈ leafIncidencesIn T u f, (E \ α p.1 p.2)) = E \ α u f by
    exact this (treeComponent T u f).ncard u f huf rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro u f huf hcard
    obtain ⟨w, hadj, rfl⟩ := isTreeIncidence_iff_exists_adj.1 huf
    by_cases hleaf : IsLeaf T u
    · have hcomp := treeComponent_eq_singleton_of_isLeaf hT hadj hleaf
      have hset : leafIncidencesIn T u s(u, w) = {(u, s(u, w))} := by
        ext ⟨v, e⟩
        change (IsTreeIncidence T v e ∧ IsLeaf T v ∧ v ∈ treeComponent T u s(u, w)) ↔
          (v, e) = (u, s(u, w))
        rw [hcomp, Set.mem_singleton_iff, Prod.mk.injEq]
        constructor
        · rintro ⟨hve, _, rfl⟩
          refine ⟨rfl, ?_⟩
          obtain ⟨z, hadj_z, rfl⟩ := isTreeIncidence_iff_exists_adj.1 hve
          obtain ⟨z₀, _, hz₀⟩ := hT.exists_adj_of_isLeaf hleaf
          have : z = w := (hz₀ z hadj_z).trans (hz₀ w hadj).symm
          rw [this]
        · rintro ⟨rfl, rfl⟩
          exact ⟨huf, hleaf, rfl⟩
      rw [hset]
      simp
    · obtain ⟨u₁, u₂, hw₁, hw₂, hu12, hiff⟩ := hT.exists_other_two_adj hleaf hadj
      have hadj₁ : T.Adj u u₁ := (hiff u₁).2 (Or.inr (Or.inl rfl))
      have hadj₂ : T.Adj u u₂ := (hiff u₂).2 (Or.inr (Or.inr rfl))
      obtain ⟨hcomp_eq, _hcomp_disj, hu_not₁, hu_not₂⟩ :=
        treeComponent_split_of_not_isLeaf hT hadj hw₁ hw₂ hu12 hiff
      let f₁ := s(u₁, u)
      let f₂ := s(u₂, u)
      have hf₁_inc : IsTreeIncidence T u₁ f₁ := isTreeIncidence_iff_adj.2 hadj₁.symm
      have hf₂_inc : IsTreeIncidence T u₂ f₂ := isTreeIncidence_iff_adj.2 hadj₂.symm
      have hlt₁ : (treeComponent T u₁ f₁).ncard < n := by
        rw [← hcard]
        refine Set.ncard_lt_ncard ⟨?_, ?_⟩ (Set.toFinite _)
        · rw [hcomp_eq]
          exact Set.subset_union_of_subset_left Set.subset_union_right _
        · intro hsub
          have hu_mem : u ∈ treeComponent T u s(u, w) := Reachable.rfl
          exact hu_not₁ (hsub hu_mem)
      have hlt₂ : (treeComponent T u₂ f₂).ncard < n := by
        rw [← hcard]
        refine Set.ncard_lt_ncard ⟨?_, ?_⟩ (Set.toFinite _)
        · rw [hcomp_eq]
          exact Set.subset_union_right
        · intro hsub
          have hu_mem : u ∈ treeComponent T u s(u, w) := Reachable.rfl
          exact hu_not₂ (hsub hu_mem)
      obtain ⟨hdisj₁, hunion₁⟩ := ih _ hlt₁ u₁ f₁ hf₁_inc rfl
      obtain ⟨hdisj₂, hunion₂⟩ := ih _ hlt₂ u₂ f₂ hf₂_inc rfl
      have hleaf_union :
          leafIncidencesIn T u s(u, w) =
            leafIncidencesIn T u₁ f₁ ∪ leafIncidencesIn T u₂ f₂ := by
        ext ⟨v, e⟩
        change (IsTreeIncidence T v e ∧ IsLeaf T v ∧ v ∈ treeComponent T u s(u, w)) ↔
          (IsTreeIncidence T v e ∧ IsLeaf T v ∧ v ∈ treeComponent T u₁ f₁) ∨
          (IsTreeIncidence T v e ∧ IsLeaf T v ∧ v ∈ treeComponent T u₂ f₂)
        rw [hcomp_eq]
        simp only [Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hve, hv_leaf, (rfl | hv₁) | hv₂⟩
          · exact (hleaf hv_leaf).elim
          · exact Or.inl ⟨hve, hv_leaf, hv₁⟩
          · exact Or.inr ⟨hve, hv_leaf, hv₂⟩
        · rintro (⟨hve, hv_leaf, hv₁⟩ | ⟨hve, hv_leaf, hv₂⟩)
          · exact ⟨hve, hv_leaf, Or.inl (Or.inr hv₁)⟩
          · exact ⟨hve, hv_leaf, Or.inr hv₂⟩
      have hf₁_u : IsTreeIncidence T u f₁ := isTreeIncidence_symm hadj₁.symm
      have hf₂_u : IsTreeIncidence T u f₂ := isTreeIncidence_symm hadj₂.symm
      have hne_f1 : s(u, w) ≠ f₁ := by
        rw [show f₁ = s(u, u₁) from Sym2.eq_swap]
        exact sym2_mk_eq_left_iff.not.2 hw₁
      have hne_f2 : s(u, w) ≠ f₂ := by
        rw [show f₂ = s(u, u₂) from Sym2.eq_swap]
        exact sym2_mk_eq_left_iff.not.2 hw₂
      have hne_12 : f₁ ≠ f₂ := by
        rw [show f₁ = s(u, u₁) from Sym2.eq_swap, show f₂ = s(u, u₂) from Sym2.eq_swap]
        exact sym2_mk_eq_left_iff.not.2 hu12
      obtain ⟨hu_union, hu_inter⟩ :=
        hα.compl_eq_union_of_degree_three huf hf₁_u hf₂_u hne_f1 hne_f2 hne_12
      have hcompl₁ : E \ α u₁ f₁ = α u f₁ := by
        rw [hα.isTreeLabelling.compl_eq hadj₁.symm,
          Set.sdiff_sdiff_cancel_left (hα.isTreeLabelling.subset_of_inc hf₁_u)]
      have hcompl₂ : E \ α u₂ f₂ = α u f₂ := by
        rw [hα.isTreeLabelling.compl_eq hadj₂.symm,
          Set.sdiff_sdiff_cancel_left (hα.isTreeLabelling.subset_of_inc hf₂_u)]
      rw [hleaf_union]
      refine ⟨?_, ?_⟩
      · intro p₁ hp₁ p₂ hp₂ hp_ne
        have hcross : ∀ (q₁ q₂ : ι × Sym2 ι),
            q₁ ∈ leafIncidencesIn T u₁ f₁ → q₂ ∈ leafIncidencesIn T u₂ f₂ →
            Disjoint (E \ α q₁.1 q₁.2) (E \ α q₂.1 q₂.2) := by
          intro q₁ q₂ hq₁ hq₂
          have hsub₁ : E \ α q₁.1 q₁.2 ⊆ α u f₁ := by
            rw [← hcompl₁, ← hunion₁]
            exact Set.subset_biUnion_of_mem (u := fun p : ι × Sym2 ι ↦ E \ α p.1 p.2) hq₁
          have hsub₂ : E \ α q₂.1 q₂.2 ⊆ α u f₂ := by
            rw [← hcompl₂, ← hunion₂]
            exact Set.subset_biUnion_of_mem (u := fun p : ι × Sym2 ι ↦ E \ α p.1 p.2) hq₂
          exact Set.disjoint_iff_inter_eq_empty.2
            (Set.Subset.antisymm
              ((Set.inter_subset_inter hsub₁ hsub₂).trans hu_inter.subset)
              (Set.empty_subset _))
        rcases hp₁ with hp₁ | hp₁ <;> rcases hp₂ with hp₂ | hp₂
        · exact hdisj₁ hp₁ hp₂ hp_ne
        · exact hcross p₁ p₂ hp₁ hp₂
        · exact (hcross p₂ p₁ hp₂ hp₁).symm
        · exact hdisj₂ hp₁ hp₂ hp_ne
      · rw [Set.biUnion_union, hunion₁, hunion₂, hcompl₁, hcompl₂, hu_union]

end GraphMinor.GM10
