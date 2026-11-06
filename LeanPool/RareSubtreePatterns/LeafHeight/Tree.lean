/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.LeafHeight.Consequences
public import LeanPool.RareSubtreePatterns.Bienayme.Normalization
public import LeanPool.RareSubtreePatterns.PlaneTree.Patterns

import Mathlib.MeasureTheory.Measure.Real

/-!
# Leaf-heights of plane trees and the root leaf-height law

Source lines 814–833 and 2911–2930. The leaf-height `λ_v(T)` of a vertex is the distance from
`v` to its closest leaf descendant; we define the root leaf-height `λ_∅(T)` recursively
(a leaf has `0`; otherwise one plus the minimum over the children) and the leaf-height
`λ(T) = max_{v ∈ T} λ_v(T)`, where `λ_v(T) = λ_∅(T_v)` for the fringe subtree `T_v`.

* `PlaneTree.le_leafHeight_iff_markCount_pos`: `λ(T) ≥ k` iff the raw count
  `∑_{v ∈ T} 1{λ_∅(T_v) ≥ k}` is positive (inventory U04, source lines 827–829).
* `LeafHeight.bienayme_real_le_rootLeafHeight`: for a critical `μ` with `μ_1 ≠ 1`,
  `P(λ_∅(𝒯) ≥ k)` is the analytic sequence `π_k` (`π_0 = 1`, `π_{k+1} = g(π_k)`), by the
  branching property (inventory U10, source lines 2922–2930, 2956–2957); and
  `P(λ_∅(𝒯) = k) = ℓ_k`.
* Lemma `lem:ell_asymp` and the identification of `C_μ`, `D_μ` (U03), restated for the tree law.
-/

@[expose] public section

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal

namespace PoissonDeclumping

namespace PlaneTree

@[simp] theorem rootLeafHeight_leaf : rootLeafHeight (node []) = 0 := by
  rw [rootLeafHeight]

private theorem le_foldr_min_iff (k a : ℕ) (l : List ℕ) :
    k ≤ l.foldr min a ↔ k ≤ a ∧ ∀ x ∈ l, k ≤ x := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldr_cons, le_min_iff, ih, List.forall_mem_cons]
    tauto

private theorem le_foldr_max_iff (k : ℕ) (l : List ℕ) :
    k ≤ l.foldr max 0 ↔ k = 0 ∨ ∃ x ∈ l, k ≤ x := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldr_cons, le_max_iff, ih, List.mem_cons, exists_eq_or_imp]
    tauto

/-- `λ_∅(T) ≥ k + 1` iff the root has at least one child and every child has root
leaf-height at least `k`. -/
theorem succ_le_rootLeafHeight_iff (k : ℕ) (T : PlaneTree) :
    k + 1 ≤ rootLeafHeight T ↔ T.children ≠ [] ∧ ∀ U ∈ T.children, k ≤ rootLeafHeight U := by
  rcases T with ⟨_ | ⟨t, us⟩⟩
  · simp
  · rw [rootLeafHeight, Nat.add_le_add_iff_right, le_foldr_min_iff]
    simp

/-- `λ_∅(T) = 0` iff `T` is a leaf. -/
theorem rootLeafHeight_eq_zero_iff (T : PlaneTree) :
    rootLeafHeight T = 0 ↔ T.children = [] := by
  rcases T with ⟨_ | ⟨t, us⟩⟩
  · simp
  · simp [rootLeafHeight]

/-- `λ(T) ≥ k` iff some vertex `v` has `λ_∅(T_v) ≥ k`. -/
theorem le_leafHeight_iff (k : ℕ) (T : PlaneTree) :
    k ≤ leafHeight T ↔ ∃ U ∈ T.fringeTrees, k ≤ rootLeafHeight U := by
  rw [leafHeight, le_foldr_max_iff]
  constructor
  · rintro (rfl | ⟨x, hx, hkx⟩)
    · exact ⟨T, self_mem_fringeTrees T, Nat.zero_le _⟩
    · obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hx
      exact ⟨U, hU, hkx⟩
  · rintro ⟨U, hU, hk⟩
    exact Or.inr ⟨_, List.mem_map_of_mem hU, hk⟩

/-- U04 for the leaf-height: `λ(T) ≥ k` iff the raw marked count
`∑_{v ∈ T} 1{λ_∅(T_v) ≥ k}` is positive (source lines 827–829). -/
theorem le_leafHeight_iff_markCount_pos (k : ℕ) (T : PlaneTree) :
    k ≤ leafHeight T ↔ 0 < markCount (fun U => k ≤ rootLeafHeight U) T := by
  rw [le_leafHeight_iff, markCount_pos_iff]

theorem rootLeafHeight_le_leafHeight (T : PlaneTree) : rootLeafHeight T ≤ leafHeight T :=
  (le_leafHeight_iff _ T).mpr ⟨T, self_mem_fringeTrees T, le_rfl⟩

end PlaneTree

namespace LeafHeight

open PlaneTree

variable {μ : PMF ℕ}

/-- The set of trees with all root children in `A` is the disjoint union of the leaf and of
`{λ_∅ ≥ k + 1}`, for `A = {λ_∅ ≥ k}`. -/
private theorem forall_children_eq_union (k : ℕ) :
    {T : PlaneTree | ∀ U ∈ T.children, U ∈ {V : PlaneTree | k ≤ rootLeafHeight V}} =
      {T | k + 1 ≤ rootLeafHeight T} ∪ {node []} := by
  ext T
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff,
    succ_le_rootLeafHeight_iff]
  constructor
  · intro h
    by_cases hT : T.children = []
    · right
      rw [eq_node_children T, hT]
    · exact Or.inl ⟨hT, h⟩
  · rintro (⟨-, h⟩ | rfl)
    · exact h
    · simp

/-- U10: for a critical `μ` with `μ_1 ≠ 1`, `P(λ_∅(𝒯) ≥ k) = π_k`, where `π_0 = 1` and
`π_{k+1} = g(π_k)`, `g(x) = ∑_{j ≥ 1} μ_j x^j`. -/
theorem bienayme_real_le_rootLeafHeight (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (k : ℕ) :
    (bienayme μ).real {T | k ≤ rootLeafHeight T} = piSeq μ k := by
  induction k with
  | zero =>
    simp only [Nat.zero_le, Set.ofPred_true, piSeq_zero, measureReal_def,
      bienayme_univ hc h1, ENNReal.toReal_one]
  | succ k ih =>
    set A : Set PlaneTree := {V | k ≤ rootLeafHeight V} with hA
    have hdisj : Disjoint {T : PlaneTree | k + 1 ≤ rootLeafHeight T} {node []} := by
      rw [Set.disjoint_singleton_right]
      simp
    have hsplit := bienayme_forall_children_mem μ A
    rw [forall_children_eq_union k, measure_union hdisj (measurableSet_singleton _),
      bienayme_apply_singleton, weight_node] at hsplit
    simp only [List.length_nil, List.map_nil, List.prod_nil, mul_one] at hsplit
    have hAle : bienayme μ A ≤ 1 := (measure_mono (Set.subset_univ A)).trans
      (bienayme_univ hc h1).le
    have hAtop : bienayme μ A ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hAle
    have hterm : ∀ j, μ j * bienayme μ A ^ j ≠ ∞ := fun j =>
      ENNReal.mul_ne_top (μ.apply_ne_top j) (ENNReal.pow_ne_top hAtop)
    have hStop : bienayme μ {T : PlaneTree | k + 1 ≤ rootLeafHeight T} ≠ ∞ :=
      measure_ne_top _ _
    have hreal := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add hStop (μ.apply_ne_top 0), ENNReal.tsum_toReal_eq hterm] at hreal
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow] at hreal
    have hAreal : (bienayme μ A).toReal = piSeq μ k := by
      rw [← ih, measureReal_def]
    rw [hAreal] at hreal
    rw [measureReal_def, piSeq_succ,
      g_eq_pgf_sub (piSeq_pos hc h1 k).le (piSeq_le_one hc h1 k)]
    simp only [mass]
    linarith

/-- `P(λ_∅(𝒯) = k) = ℓ_k = π_k - π_{k+1}` (source line 3009). -/
theorem bienayme_real_rootLeafHeight_eq (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (k : ℕ) :
    (bienayme μ).real {T | rootLeafHeight T = k} = ellSeq μ k := by
  have hset : {T : PlaneTree | rootLeafHeight T = k} =
      {T | k ≤ rootLeafHeight T} \ {T | k + 1 ≤ rootLeafHeight T} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
    omega
  have hsub : {T : PlaneTree | k + 1 ≤ rootLeafHeight T} ⊆ {T | k ≤ rootLeafHeight T} :=
    fun T hT => le_trans (Nat.le_succ k) hT
  rw [hset, measureReal_sdiff hsub (DiscreteMeasurableSpace.forall_measurableSet _),
    bienayme_real_le_rootLeafHeight hc h1, bienayme_real_le_rootLeafHeight hc h1, ellSeq]

/-- `P(λ_∅(𝒯) ≥ k)` as a function of `k` is `π`. -/
theorem bienayme_real_le_rootLeafHeight_eq_piSeq (hc : IsCritical μ) (h1 : μ 1 ≠ 1) :
    (fun k : ℕ => (bienayme μ).real {T | k ≤ rootLeafHeight T}) = piSeq μ :=
  funext (bienayme_real_le_rootLeafHeight hc h1)

/-- Lemma `lem:ell_asymp`(i) for the tree law: if `μ_1 > 0`,
`P(λ_∅(𝒯) ≥ k) ∼ C_μ μ_1^k` with `C_μ = lim P(λ_∅(𝒯) ≥ k)/μ_1^k > 0`. -/
theorem lem_ell_asymp_i_tree (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (hpos : 0 < μ 1) :
    0 < leafC μ ∧
      Tendsto (fun k : ℕ => (bienayme μ).real {T | k ≤ rootLeafHeight T} / (μ 1).toReal ^ k)
        atTop (𝓝 (leafC μ)) ∧
      (fun k : ℕ => (bienayme μ).real {T | k ≤ rootLeafHeight T}) ~[atTop]
        fun k => leafC μ * (μ 1).toReal ^ k := by
  simp only [bienayme_real_le_rootLeafHeight hc h1]
  exact ⟨leafC_pos hc h1 hpos, tendsto_ratio_leafC hc h1 hpos,
    piSeq_isEquivalent_leafC hc h1 hpos⟩

/-- Lemma `lem:ell_asymp`(ii) for the tree law: if `μ_1 = 0` and `κ = min{j ≥ 2 : μ_j > 0}`,
`P(λ_∅(𝒯) ≥ k) ∼ μ_κ^{-1/(κ-1)} D_μ^{κ^k}` with
`D_μ = lim P(λ_∅(𝒯) ≥ k)^{1/κ^k} ∈ (0, 1)`. -/
theorem lem_ell_asymp_ii_tree (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (h0 : μ 1 = 0) :
    kappa μ = sInf {j : ℕ | 2 ≤ j ∧ 0 < μ j} ∧ 0 < leafD μ ∧ leafD μ < 1 ∧
      Tendsto (fun k : ℕ => (bienayme μ).real {T | k ≤ rootLeafHeight T} ^
        (1 / (kappa μ : ℝ) ^ k)) atTop (𝓝 (leafD μ)) ∧
      (fun k : ℕ => (bienayme μ).real {T | k ≤ rootLeafHeight T}) ~[atTop]
        fun k => (μ (kappa μ)).toReal ^ (-1 / ((kappa μ : ℝ) - 1)) *
          leafD μ ^ (kappa μ ^ k) := by
  simp only [bienayme_real_le_rootLeafHeight hc h1]
  exact ⟨kappa_eq_sInf_two h0, leafD_pos hc h1 h0, leafD_lt_one hc h1 h0,
    tendsto_piSeq_rpow_leafD hc h1 h0, piSeq_isEquivalent_leafD hc h1 h0⟩

end LeafHeight

end PoissonDeclumping
