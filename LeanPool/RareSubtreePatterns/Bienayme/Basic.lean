/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bienayme.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Bienaymé trees: weights, the branching property and forests

Source lines 679–704 (Section 2.1) of the paper. For an arbitrary offspring law `μ` (a PMF
on `ℕ`, no criticality assumed) we prove:

* `weight_node`: `𝐏_μ(node [t_1,…,t_k]) = μ_k ∏ 𝐏_μ(t_i)`, and `bienayme_apply_singleton`:
  the Bienaymé measure gives each finite tree its weight `∏_{u∈T} μ_{k_u(T)}`;
* `bienayme_apply`: the measure of any set of trees is the sum of the weights;
* the branching property (`bienayme_children_eq`, `bienayme_rootDegree_eq_children_mem`,
  `bienayme_node_ofFn_mem`): given the root degree `k`, the `k` child subtrees are
  independent `μ`-Bienaymé trees;
* the forest product formulas `tsum_forest_fin`, `tsum_forest_list`, and the law of the size
  `bienayme_vertexCount_succ` in terms of forest sizes `forestSizeWeight`;
* `bienayme_univ_le_one`: the total weight of the finite trees is at most one, so
  `bienayme μ` is a finite measure. That it equals one for critical `μ` with `μ 1 ≠ 1` is
  proved in `PoissonDeclumping.Bienayme.Normalization`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PoissonDeclumping.PlaneTree

/-! ### Tree combinatorics -/

/-- The number of vertices is one plus the total size of the root's child trees. -/
theorem vertexCount_node (ts : List PlaneTree) :
    (node ts).vertexCount = (ts.map vertexCount).sum + 1 := by
  simp only [vertexCount, fringeTrees_node, List.length_cons, List.length_flatMap]
  rfl

/-- A tree is determined by its list of children. -/
theorem eq_node_children (T : PlaneTree) : T = node T.children := by
  cases T; rfl

/-- Finite plane trees are in bijection with lists of finite plane trees (their children). -/
def equivList : PlaneTree ≃ List PlaneTree where
  toFun := children
  invFun := node
  left_inv T := (eq_node_children T).symm
  right_inv _ := rfl

/-- Finite plane trees are in bijection with pairs `(k, (T_0, …, T_{k-1}))`: the root degree
and the ordered tuple of child trees. -/
def equivSigma : PlaneTree ≃ Σ k, Fin k → PlaneTree :=
  equivList.trans List.equivSigmaTuple

@[simp] theorem equivSigma_symm_apply (p : Σ k, Fin k → PlaneTree) :
    equivSigma.symm p = node (List.ofFn p.2) := rfl

/-- Sum over `k`-tuples of a product of functions of the coordinates (in `ℝ≥0∞`). -/
theorem tsum_pi_fin_prod {α : Type*} : ∀ (k : ℕ) (g : Fin k → α → ℝ≥0∞),
    ∑' f : Fin k → α, ∏ i, g i (f i) = ∏ i, ∑' a, g i a
  | 0, g => by simp
  | k + 1, g => by
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => α).tsum_eq]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp only [ENNReal.tsum_mul_left]
    rw [tsum_pi_fin_prod k (fun i => g i.succ), ENNReal.tsum_mul_right]

variable (μ : PMF ℕ)

/-! ### Weights and the Bienaymé measure -/

/-- The weight of a tree is `μ` of the root degree times the weights of the child trees. -/
theorem weight_node (ts : List PlaneTree) :
    weight μ (node ts) = μ ts.length * (ts.map (weight μ)).prod := by
  simp only [weight, degSeq_node, List.map_cons, List.prod_cons]
  congr 1
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_cons,
      List.prod_cons, weight]

theorem weight_node_ofFn {k : ℕ} (f : Fin k → PlaneTree) :
    weight μ (node (List.ofFn f)) = μ k * ∏ i, weight μ (f i) := by
  rw [weight_node, List.length_ofFn, List.map_ofFn, List.prod_ofFn]
  rfl

/-- `𝐏_μ(T ∈ s) = ∑_{T ∈ s} ∏_{u ∈ T} μ_{k_u(T)}`. -/
theorem bienayme_apply (s : Set PlaneTree) :
    bienayme μ s = ∑' T, s.indicator (weight μ) T := by
  rw [bienayme, Measure.sum_apply _ (DiscreteMeasurableSpace.forall_measurableSet s)]
  congr 1
  ext T
  by_cases h : T ∈ s <;> simp [h]

/-- `𝐏_μ(T) = ∏_{u ∈ T} μ_{k_u(T)}` (source line 696). -/
theorem bienayme_apply_singleton (T : PlaneTree) : bienayme μ {T} = weight μ T := by
  rw [bienayme_apply, tsum_eq_single T]
  · simp
  · intro U hU
    simp [hU]

/-- Decomposition of `𝐏_μ(T ∈ s)` according to the root degree `k` and the tuple of child
trees. -/
theorem bienayme_apply_eq_tsum_sigma (s : Set PlaneTree) :
    bienayme μ s =
      ∑' k, ∑' f : Fin k → PlaneTree, s.indicator (weight μ) (node (List.ofFn f)) := by
  rw [bienayme_apply, ← equivSigma.symm.tsum_eq, ENNReal.tsum_sigma']
  rfl

/-- For a fixed root degree `k`, summing the weight of `node [T_0, …, T_{k-1}]` over the
tuples with `T_i ∈ A_i` gives `μ_k ∏_i 𝐏_μ(A_i)`. -/
theorem tsum_weight_node_ofFn_indicator (k : ℕ) (A : Fin k → Set PlaneTree) :
    ∑' f : Fin k → PlaneTree,
        {f : Fin k → PlaneTree | ∀ i, f i ∈ A i}.indicator
          (fun f => weight μ (node (List.ofFn f))) f =
      μ k * ∏ i, bienayme μ (A i) := by
  have h : ∀ f : Fin k → PlaneTree,
      {f : Fin k → PlaneTree | ∀ i, f i ∈ A i}.indicator
          (fun f => weight μ (node (List.ofFn f))) f =
        μ k * ∏ i, (A i).indicator (weight μ) (f i) := by
    intro f
    by_cases hf : ∀ i, f i ∈ A i
    · rw [Set.indicator_of_mem (show f ∈ {f : Fin k → PlaneTree | ∀ i, f i ∈ A i} from hf),
        weight_node_ofFn]
      congr 1
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hf i) _).symm
    · rw [Set.indicator_of_notMem (show f ∉ {f : Fin k → PlaneTree | ∀ i, f i ∈ A i} from hf)]
      push Not at hf
      obtain ⟨i, hi⟩ := hf
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _), mul_zero]
  simp only [h, ENNReal.tsum_mul_left, tsum_pi_fin_prod, bienayme_apply]

/-- General branching decomposition: if membership of `node [T_0, …, T_{k-1}]` in `s` means
`k ∈ D` and `T_i ∈ A k i` for all `i`, then `𝐏_μ(s) = ∑_{k ∈ D} μ_k ∏_i 𝐏_μ(A k i)`. -/
theorem bienayme_eq_tsum_of_mem_iff (s : Set PlaneTree) (D : Set ℕ)
    (A : (k : ℕ) → Fin k → Set PlaneTree)
    (hs : ∀ k (f : Fin k → PlaneTree), node (List.ofFn f) ∈ s ↔ k ∈ D ∧ ∀ i, f i ∈ A k i) :
    bienayme μ s = ∑' k, D.indicator (fun k => μ k * ∏ i, bienayme μ (A k i)) k := by
  rw [bienayme_apply_eq_tsum_sigma]
  refine tsum_congr fun k => ?_
  by_cases hk : k ∈ D
  · rw [Set.indicator_of_mem hk, ← tsum_weight_node_ofFn_indicator]
    refine tsum_congr fun f => ?_
    by_cases hf : ∀ i, f i ∈ A k i
    · rw [Set.indicator_of_mem ((hs k f).2 ⟨hk, hf⟩),
        Set.indicator_of_mem (show f ∈ {f : Fin k → PlaneTree | ∀ i, f i ∈ A k i} from hf)]
    · rw [Set.indicator_of_notMem (fun h => hf ((hs k f).1 h).2),
        Set.indicator_of_notMem (show f ∉ {f : Fin k → PlaneTree | ∀ i, f i ∈ A k i} from hf)]
  · rw [Set.indicator_of_notMem hk]
    exact ENNReal.tsum_eq_zero.2 fun f => Set.indicator_of_notMem (fun h => hk ((hs k f).1 h).1) _

/-! ### Branching property -/

/-- The law of the root's children: `𝐏_μ(children = [t_1, …, t_k]) = μ_k ∏_i 𝐏_μ(t_i)`. -/
theorem bienayme_children_eq (ts : List PlaneTree) :
    bienayme μ {T | T.children = ts} =
      μ ts.length * (ts.map fun U => bienayme μ {U}).prod := by
  have hs : {T : PlaneTree | T.children = ts} = {node ts} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [eq_node_children T, h]
    · rintro rfl
      rfl
  rw [hs, bienayme_apply_singleton, weight_node]
  simp only [bienayme_apply_singleton]

/-- **Branching property** (source lines 696–698): given root degree `k`, the `k` child
subtrees are independent `μ`-Bienaymé trees:
`𝐏_μ(k_∅ = k, T_i ∈ A_i for all i < k) = μ_k ∏_{i<k} 𝐏_μ(A_i)`. -/
theorem bienayme_rootDegree_eq_children_mem (k : ℕ) (A : ℕ → Set PlaneTree) :
    bienayme μ {T | T.rootDegree = k ∧
        ∀ (i : ℕ) (hi : i < T.children.length), T.children[i] ∈ A i} =
      μ k * ∏ i ∈ Finset.range k, bienayme μ (A i) := by
  rw [bienayme_eq_tsum_of_mem_iff μ _ {k} (fun _ i => A i), tsum_eq_single k]
  · rw [Set.indicator_of_mem (Set.mem_singleton k), Fin.prod_univ_eq_prod_range
      (fun i => bienayme μ (A i)) k]
  · intro j hj
    exact Set.indicator_of_notMem (Set.notMem_singleton_iff.2 hj) _
  · intro j f
    simp only [Set.mem_ofPred_eq, rootDegree_node, List.length_ofFn, children_node,
      List.getElem_ofFn, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i => h2 i i.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i hi => h2 ⟨i, hi⟩⟩

/-- Branching property, `Fin`-indexed form: for sets `A_0, …, A_{k-1}`,
`𝐏_μ(k_∅ = k, T_i ∈ A_i for all i) = μ_k ∏_i 𝐏_μ(A_i)`. -/
theorem bienayme_node_ofFn_mem (k : ℕ) (A : Fin k → Set PlaneTree) :
    bienayme μ {T | ∃ f : Fin k → PlaneTree, T = node (List.ofFn f) ∧ ∀ i, f i ∈ A i} =
      μ k * ∏ i, bienayme μ (A i) := by
  rw [bienayme_eq_tsum_of_mem_iff μ _ {k} (fun j i => if h : j = k then A (i.cast h) else ∅),
    tsum_eq_single k]
  · simp
  · intro j hj
    exact Set.indicator_of_notMem (Set.notMem_singleton_iff.2 hj) _
  · intro j f
    simp only [Set.mem_ofPred_eq, node.injEq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, hg, hgA⟩
      have hj : j = k := by simpa using congrArg List.length hg
      subst hj
      rw [List.ofFn_inj] at hg
      subst hg
      simpa using hgA
    · rintro ⟨rfl, h⟩
      exact ⟨f, rfl, by simpa using h⟩

/-- `𝐏_μ(all children in A) = ∑_k μ_k 𝐏_μ(A)^k`, i.e. the generating function of `μ`
evaluated at `𝐏_μ(A)`. -/
theorem bienayme_forall_children_mem (A : Set PlaneTree) :
    bienayme μ {T | ∀ U ∈ T.children, U ∈ A} = ∑' k, μ k * bienayme μ A ^ k := by
  rw [bienayme_eq_tsum_of_mem_iff μ _ Set.univ (fun _ _ => A)]
  · simp
  · intro k f
    simp [List.mem_ofFn]

/-! ### Forests -/

/-- Forest product formula: the total weight of `k`-tuples of trees with `T_i ∈ A_i` is
`∏_i 𝐏_μ(A_i)` (independence of the trees of a forest). -/
theorem tsum_forest_fin (k : ℕ) (A : Fin k → Set PlaneTree) :
    ∑' f : Fin k → PlaneTree, ∏ i, (A i).indicator (weight μ) (f i) =
      ∏ i, bienayme μ (A i) := by
  rw [tsum_pi_fin_prod]
  simp only [bienayme_apply]

/-- Forest product formula for lists: the total weight of lists of `k` trees all in `A` is
`𝐏_μ(A)^k`. -/
theorem tsum_forest_list (k : ℕ) (A : Set PlaneTree) :
    ∑' ts : List PlaneTree,
        {ts : List PlaneTree | ts.length = k ∧ ∀ U ∈ ts, U ∈ A}.indicator
          (fun ts => (ts.map (weight μ)).prod) ts =
      bienayme μ A ^ k := by
  rw [← List.equivSigmaTuple.symm.tsum_eq, ENNReal.tsum_sigma', tsum_eq_single k]
  · rw [← Fin.prod_const, ← tsum_forest_fin]
    refine tsum_congr fun f => ?_
    simp only [List.equivSigmaTuple_symm_apply]
    by_cases hf : ∀ i, f i ∈ A
    · rw [Set.indicator_of_mem (show List.ofFn f ∈
          {ts : List PlaneTree | ts.length = k ∧ ∀ U ∈ ts, U ∈ A} from
          ⟨List.length_ofFn, by simpa [List.mem_ofFn] using hf⟩),
        List.map_ofFn, List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hf i) _).symm
    · rw [Set.indicator_of_notMem]
      · push Not at hf
        obtain ⟨i, hi⟩ := hf
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
      · rintro ⟨-, h⟩
        exact hf fun i => h _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  · intro j hj
    refine ENNReal.tsum_eq_zero.2 fun f => Set.indicator_of_notMem ?_ _
    rintro ⟨h, -⟩
    simp only [List.equivSigmaTuple_symm_apply, List.length_ofFn] at h
    exact hj h

/-- Total weight of the `k`-tuples of trees with `n` vertices in total: the probability that
a forest of `k` independent `μ`-Bienaymé trees has `n` vertices. -/
noncomputable def forestSizeWeight (k n : ℕ) : ℝ≥0∞ :=
  ∑' f : Fin k → PlaneTree, if ∑ i, (f i).vertexCount = n then ∏ i, weight μ (f i) else 0

/-- Law of the size: `𝐏_μ(|T| = n + 1) = ∑_k μ_k 𝐏(|F_k| = n)`, where `F_k` is a forest of
`k` independent `μ`-Bienaymé trees. -/
theorem bienayme_vertexCount_succ (n : ℕ) :
    bienayme μ {T | T.vertexCount = n + 1} = ∑' k, μ k * forestSizeWeight μ k n := by
  rw [bienayme_apply_eq_tsum_sigma]
  refine tsum_congr fun k => ?_
  rw [forestSizeWeight, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun f => ?_
  have hv : (node (List.ofFn f)).vertexCount = ∑ i, (f i).vertexCount + 1 := by
    rw [vertexCount_node, List.map_ofFn, List.sum_ofFn]
    rfl
  by_cases h : ∑ i, (f i).vertexCount = n
  · rw [Set.indicator_of_mem (show node (List.ofFn f) ∈ {T | T.vertexCount = n + 1} by
      simp only [Set.mem_ofPred_eq, hv, h]), ite_eq_left h, weight_node_ofFn]
  · rw [Set.indicator_of_notMem (show node (List.ofFn f) ∉ {T | T.vertexCount = n + 1} by
      simpa only [Set.mem_ofPred_eq, hv, add_left_inj] using h), ite_eq_right h, mul_zero]

/-- Summing over sizes, a forest of `k` trees has total weight `𝐏_μ(univ)^k`. -/
theorem tsum_forestSizeWeight (k : ℕ) :
    ∑' n, forestSizeWeight μ k n = bienayme μ Set.univ ^ k := by
  simp only [forestSizeWeight]
  rw [ENNReal.tsum_comm, ← Fin.prod_const, ← tsum_forest_fin]
  refine tsum_congr fun f => ?_
  rw [tsum_eq_single (∑ i, (f i).vertexCount) fun n hn => ite_eq_right (Ne.symm hn)]
  simp

/-! ### Total mass at most one -/

/-- Trees of height at most `h` (an auxiliary truncation). -/
def heightLE : ℕ → Set PlaneTree
  | 0 => {T | T.children = []}
  | h + 1 => {T | ∀ U ∈ T.children, U ∈ heightLE h}

theorem heightLE_subset_succ : ∀ h, heightLE h ⊆ heightLE (h + 1)
  | 0 => fun T hT U hU => by
    simp only [heightLE, Set.mem_ofPred_eq] at hT
    simp [hT] at hU
  | h + 1 => fun _ hT U hU => heightLE_subset_succ h (hT U hU)

theorem heightLE_mono : Monotone heightLE := monotone_nat_of_le_succ heightLE_subset_succ

theorem exists_mem_heightLE (T : PlaneTree) : ∃ h, T ∈ heightLE h := by
  induction T using induction_children with
  | step T ih =>
    have hb : ∀ l : List PlaneTree, (∀ U ∈ l, ∃ h, U ∈ heightLE h) →
        ∃ H, ∀ U ∈ l, U ∈ heightLE H := by
      intro l hl
      induction l with
      | nil => exact ⟨0, by simp⟩
      | cons t l ihl =>
        obtain ⟨h₁, h₁t⟩ := hl t (List.mem_cons_self ..)
        obtain ⟨H, hH⟩ := ihl fun U hU => hl U (List.mem_cons_of_mem _ hU)
        refine ⟨max h₁ H, fun U hU => ?_⟩
        rcases List.mem_cons.1 hU with rfl | hU
        · exact heightLE_mono (le_max_left _ _) h₁t
        · exact heightLE_mono (le_max_right _ _) (hH U hU)
    obtain ⟨H, hH⟩ := hb T.children ih
    exact ⟨H + 1, hH⟩

theorem iUnion_heightLE : ⋃ h, heightLE h = Set.univ :=
  Set.eq_univ_of_forall fun T => Set.mem_iUnion.2 (exists_mem_heightLE T)

theorem bienayme_heightLE_le_one : ∀ h, bienayme μ (heightLE h) ≤ 1
  | 0 => by
    have : heightLE 0 = {T | T.children = []} := rfl
    rw [this, bienayme_children_eq]
    simpa using μ.coe_le_one 0
  | h + 1 => by
    rw [heightLE, bienayme_forall_children_mem]
    calc ∑' k, μ k * bienayme μ (heightLE h) ^ k ≤ ∑' k, μ k :=
          ENNReal.tsum_le_tsum fun k =>
            mul_le_of_le_one_right' (pow_le_one₀ zero_le (bienayme_heightLE_le_one h))
      _ = 1 := μ.tsum_coe

/-- For every offspring law `μ` (critical or not), the total Bienaymé weight of the finite
plane trees is at most one. -/
theorem bienayme_univ_le_one : bienayme μ Set.univ ≤ 1 := by
  rw [← iUnion_heightLE, heightLE_mono.measure_iUnion]
  exact iSup_le (bienayme_heightLE_le_one μ)

instance isFiniteMeasure_bienayme : IsFiniteMeasure (bienayme μ) :=
  ⟨(bienayme_univ_le_one μ).trans_lt ENNReal.one_lt_top⟩

end PoissonDeclumping.PlaneTree
