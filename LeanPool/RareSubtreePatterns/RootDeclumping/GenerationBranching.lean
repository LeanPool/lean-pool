/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.RootDeclumping.Generations
public import LeanPool.RareSubtreePatterns.Bienayme.Normalization
public import LeanPool.RareSubtreePatterns.PlaneTree.Patterns
public import Mathlib.Data.List.SplitLengths

import LeanPool.RareSubtreePatterns.LeafHeight.Tree

/-!
# The branching property at generation `k`

Source lines 3070–3083 (proof of Lemma `lem:S_lh`, inventory P23): "conditionally on the first
`k` generations, the fringe subtrees rooted at generation `k` are independent Bienaymé trees".

* `trunc k T`: the truncation of `T` at height `k` (generation-`k` vertices become leaves);
  `λ_∅ ≥ k` and `C_k` are functions of it (`le_rootLeafHeight_trunc_iff`, `skelSize_trunc`),
  and so is `Z_k` (`genCount_trunc`).
* `bienayme_trunc_gen_eq` (point form): `P(𝒯^{≤k} = S, (𝒯_v)_{|v|=k} = (t_1,…,t_L))` equals
  `W_k(S) ∏_j P(𝒯 = t_j)` if `S` is a truncation with `Z_k(S) = L`, and `0` otherwise
  (`skelWeight`: the product of the offspring masses of the vertices of `S` at depth `< k`).
* `bienayme_trunc_mem_gen_eq` (critical `μ`, `μ_1 ≠ 1`):
  `P(𝒯^{≤k} ∈ 𝒮, (𝒯_v)_{|v|=k} = (t_1,…,t_L)) = P(𝒯^{≤k} ∈ 𝒮, Z_k = L) ∏_j P(𝒯 = t_j)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PoissonDeclumping.PlaneTree

/-- The truncation `T^{≤k}` of `T` at height `k`: the first `k + 1` generations, the vertices
of generation `k` becoming leaves. -/
def trunc : ℕ → PlaneTree → PlaneTree
  | 0, _ => node []
  | k + 1, T => node (T.children.map (trunc k))

@[simp] theorem trunc_zero (T : PlaneTree) : trunc 0 T = node [] := rfl

@[simp] theorem trunc_succ_node (k : ℕ) (ts : List PlaneTree) :
    trunc (k + 1) (node ts) = node (ts.map (trunc k)) := rfl

/-- The number of generation-`k` vertices is read off the truncation. -/
theorem genCount_trunc (k : ℕ) (T : PlaneTree) : genCount k (trunc k T) = genCount k T := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih =>
    cases T with
    | node ts =>
      rw [trunc_succ_node, genCount_succ_node, genCount_succ_node, List.map_map]
      exact congrArg List.sum (List.map_congr_left fun U _ => ih U)

theorem trunc_trunc (k : ℕ) (T : PlaneTree) : trunc k (trunc k T) = trunc k T := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih =>
    cases T with
    | node ts =>
      simp only [trunc_succ_node, List.map_map, node.injEq]
      exact List.map_congr_left fun U _ => ih U

/-- `C_k` is read off the truncation. -/
theorem skelSize_trunc (k : ℕ) (T : PlaneTree) : skelSize k (trunc k T) = skelSize k T := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih =>
    cases T with
    | node ts =>
      rw [skelSize_succ, skelSize_succ, trunc_succ_node, children_node, children_node,
        List.map_map]
      congr 1
      exact congrArg List.sum (List.map_congr_left fun U _ => ih U)

/-- `λ_∅(T) ≥ k` is read off the truncation at height `k`. -/
theorem le_rootLeafHeight_trunc_iff (k : ℕ) (T : PlaneTree) :
    k ≤ rootLeafHeight (trunc k T) ↔ k ≤ rootLeafHeight T := by
  induction k generalizing T with
  | zero => simp
  | succ k ih =>
    cases T with
    | node ts =>
      rw [trunc_succ_node, succ_le_rootLeafHeight_iff, succ_le_rootLeafHeight_iff]
      simp only [children_node, ne_eq, List.map_eq_nil_iff, List.mem_map, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂, ih]

/-- Splitting a flattened list along the lengths of its blocks recovers the blocks. -/
theorem splitLengths_flatten {α : Type*} (L : List (List α)) :
    (L.map List.length).splitLengths L.flatten = L := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.map_cons, List.splitLengths_cons, List.flatten_cons, List.take_left',
      List.drop_left', ih]


/-- The Bienaymé weight of the first `k` generations of a skeleton:
`∏_{u ∈ S, |u| < k} μ_{k_u(S)}`. -/
noncomputable def skelWeight (μ : PMF ℕ) : ℕ → PlaneTree → ℝ≥0∞
  | 0, _ => 1
  | k + 1, T => μ T.rootDegree * (T.children.map (skelWeight μ k)).prod

open scoped Classical in
/-- **Branching property at generation `k`**, point form: the truncation at height `k` and the
list of generation-`k` fringe subtrees of a `μ`-Bienaymé tree satisfy
`P(𝒯^{≤k} = S, (𝒯_v)_{|v| = k} = (t_1, …, t_L)) = W_k(S) ∏_j P(𝒯 = t_j)` whenever `S` is a
truncation and `L = Z_k(S)` (and `0` otherwise). -/
theorem bienayme_trunc_gen_eq (μ : PMF ℕ) (k : ℕ) (S : PlaneTree) (ts : List PlaneTree) :
    bienayme μ {T | trunc k T = S ∧ gen k T = ts} =
      if trunc k S = S ∧ ts.length = genCount k S then
        skelWeight μ k S * (ts.map (weight μ)).prod else 0 := by
  induction k generalizing S ts with
  | zero =>
    by_cases hS : S = node []
    · subst hS
      rcases ts with _ | ⟨t, _ | ⟨t', ts⟩⟩
      · have : {T : PlaneTree | trunc 0 T = node [] ∧ gen 0 T = []} = ∅ := by
          ext T; simp
        rw [this]
        simp [genCount]
      · have : {T : PlaneTree | trunc 0 T = node [] ∧ gen 0 T = [t]} = {t} := by
          ext T; simp
        rw [this, bienayme_apply_singleton]
        simp [skelWeight, genCount]
      · have : {T : PlaneTree | trunc 0 T = node [] ∧ gen 0 T = t :: t' :: ts} = ∅ := by
          ext T; simp
        rw [this]
        simp [genCount]
    · have : {T : PlaneTree | trunc 0 T = S ∧ gen 0 T = ts} = ∅ := by
        ext T
        simp only [trunc_zero, gen_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro h
        exact absurd h.symm hS
      rw [this, measure_empty, ite_eq_right]
      rintro ⟨h, -⟩
      exact hS h.symm
  | succ k ih =>
    cases S with
    | node ss =>
    set sz := ss.map (genCount k) with hsz
    have hgc : genCount (k + 1) (node ss) = sz.sum := genCount_succ_node k ss
    by_cases hlen : ts.length = sz.sum
    · set cs := sz.splitLengths ts with hcs
      have hcs_len : cs.length = ss.length := by simp [hcs, hsz]
      have hcs_flat : cs.flatten = ts := List.flatten_splitLengths ts sz hlen.le
      have hlt : ∀ i, i < ss.length → i < cs.length := fun i hi => by rw [hcs_len]; exact hi
      have hcs_get : ∀ (i : ℕ) (hi : i < ss.length),
          (cs[i]'(hlt i hi)).length = genCount k ss[i] := by
        intro i hi
        rw [List.splitLengths_length_getElem ts sz hlen.ge]
        simp [hsz]
      have hset : {T : PlaneTree | trunc (k + 1) T = node ss ∧ gen (k + 1) T = ts} =
          {T | ∃ f : Fin ss.length → PlaneTree, T = node (List.ofFn f) ∧
            ∀ i, f i ∈ {U : PlaneTree | trunc k U = ss[i.1] ∧
              gen k U = cs[i.1]'(hlt i.1 i.2)}} := by
        ext T
        cases T with
        | node us =>
        simp only [Set.mem_ofPred_eq, trunc_succ_node, gen_succ_node, node.injEq]
        constructor
        · rintro ⟨hmap, hgen⟩
          have hus : us.length = ss.length := by rw [← hmap, List.length_map]
          have hL : us.map (gen k) = cs := by
            rw [hcs, ← hgen, List.flatMap_def, hsz, ← hmap, List.map_map]
            have : genCount k ∘ trunc k = (List.length ∘ gen k) := by
              funext U
              exact genCount_trunc k U
            rw [this, ← List.map_map, splitLengths_flatten]
          refine ⟨fun i => us[i.1]'(by rw [hus]; exact i.2), ?_, fun i => ⟨?_, ?_⟩⟩
          · exact List.ext_getElem (by simp [hus]) (fun j h1 h2 => by simp)
          · simp [← hmap]
          · simp [← hL]
        · rintro ⟨f, hf, hfA⟩
          subst hf
          refine ⟨List.ext_getElem (by simp) (fun j h1 h2 => by simpa using (hfA ⟨j, by
            simpa using h1⟩).1), ?_⟩
          rw [List.flatMap_def, ← hcs_flat]
          congr 1
          exact List.ext_getElem (by simp [hcs_len]) (fun j h1 h2 => by
            simpa using (hfA ⟨j, by simpa using h1⟩).2)
      have hA : ∀ i : Fin ss.length,
          bienayme μ {U : PlaneTree | trunc k U = ss[i.1] ∧ gen k U = cs[i.1]'(hlt i.1 i.2)} =
            if trunc k ss[i.1] = ss[i.1] then
              skelWeight μ k ss[i.1] * ((cs[i.1]'(hlt i.1 i.2)).map (weight μ)).prod else 0 := by
        intro i
        rw [ih, hcs_get i.1 i.2]
        simp only [and_true]
      rw [hset, bienayme_node_ofFn_mem, Finset.prod_congr rfl (fun i _ => hA i)]
      have htrunc : trunc (k + 1) (node ss) = node ss ↔
          ∀ i : Fin ss.length, trunc k ss[i.1] = ss[i.1] := by
        rw [trunc_succ_node, node.injEq]
        constructor
        · intro h i
          have := List.getElem_of_eq h (by simp : i.1 < (ss.map (trunc k)).length)
          simpa using this
        · intro h
          exact List.ext_getElem (by simp) (fun j h1 h2 => by simpa using h ⟨j, h2⟩)
      by_cases hall : ∀ i : Fin ss.length, trunc k ss[i.1] = ss[i.1]
      · rw [ite_eq_left ⟨htrunc.mpr hall, hlen.trans hgc.symm⟩]
        rw [Finset.prod_congr rfl (fun i _ => ite_eq_left (hall i)), Finset.prod_mul_distrib,
          skelWeight, rootDegree_node, children_node, mul_assoc,
          Fin.prod_univ_fun_getElem ss (skelWeight μ k)]
        congr 2
        rw [← hcs_flat, List.map_flatten, List.prod_flatten, List.map_map]
        rw [← Fin.prod_univ_fun_getElem cs (List.prod ∘ List.map (weight μ))]
        exact Fin.prod_congr' (fun i : Fin cs.length => (List.prod ∘ List.map (weight μ)) cs[i.1])
          hcs_len.symm
      · rw [ite_eq_right (fun h => hall (htrunc.mp h.1))]
        push Not at hall
        obtain ⟨i, hi⟩ := hall
        exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i)
          (ite_eq_right hi))
    · have : {T : PlaneTree | trunc (k + 1) T = node ss ∧ gen (k + 1) T = ts} = ∅ := by
        ext T
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro htr hgen
        apply hlen
        rw [← hgen, ← hgc, ← htr, genCount_trunc]
        rfl
      rw [this, measure_empty, ite_eq_right]
      rintro ⟨-, h⟩
      exact hlen (h.trans hgc)


/-- Disintegration of a Bienaymé probability along the fibres of any map. -/
theorem bienayme_eq_tsum_inter_fiber {α : Type*} (μ : PMF ℕ) (f : PlaneTree → α)
    (E : Set PlaneTree) : bienayme μ E = ∑' a, bienayme μ (E ∩ f ⁻¹' {a}) := by
  simp_rw [bienayme_apply]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun T => ?_
  rw [tsum_eq_single (f T)]
  · by_cases hT : T ∈ E
    · rw [Set.indicator_of_mem hT,
        Set.indicator_of_mem (show T ∈ E ∩ f ⁻¹' {f T} from ⟨hT, rfl⟩)]
    · rw [Set.indicator_of_notMem hT, Set.indicator_of_notMem fun h => hT h.1]
  · intro a ha
    exact Set.indicator_of_notMem (fun h => ha h.2.symm) _

/-- **Branching property at generation `k`** (source lines 3070–3083): for a critical `μ` with
`μ_1 ≠ 1`, every event `{𝒯^{≤k} ∈ 𝒮}` determined by the first `k` generations, and every list
`(t_1, …, t_L)`, `P(𝒯^{≤k} ∈ 𝒮, (𝒯_v)_{|v| = k} = (t_1, …, t_L)) =
P(𝒯^{≤k} ∈ 𝒮, Z_k = L) ∏_j P(𝒯 = t_j)`: conditionally on the first `k` generations, the fringe
subtrees rooted at generation `k` are independent `μ`-Bienaymé trees. -/
theorem bienayme_trunc_mem_gen_eq {μ : PMF ℕ} (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (k : ℕ)
    (𝒮 : Set PlaneTree) (ts : List PlaneTree) :
    bienayme μ {T | trunc k T ∈ 𝒮 ∧ gen k T = ts} =
      bienayme μ {T | trunc k T ∈ 𝒮 ∧ (gen k T).length = ts.length} *
        (ts.map (weight μ)).prod := by
  classical
  set F : PlaneTree → List PlaneTree → ℝ≥0∞ := fun S ts' =>
    𝒮.indicator (fun S => bienayme μ {T | trunc k T = S ∧ gen k T = ts'}) S with hF
  have hstep1 : ∀ ts', bienayme μ {T | trunc k T ∈ 𝒮 ∧ gen k T = ts'} = ∑' S, F S ts' := by
    intro ts'
    rw [bienayme_eq_tsum_inter_fiber μ (trunc k)]
    refine tsum_congr fun S => ?_
    by_cases hS : S ∈ 𝒮
    · simp only [hF, Set.indicator_of_mem hS]
      congr 1
      ext T
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩; exact ⟨⟨h3 ▸ hS, h2⟩, h3⟩
    · simp only [hF, Set.indicator_of_notMem hS]
      convert measure_empty (μ := bienayme μ)
      ext T
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and, and_imp]
      intro h _ h3
      exact hS (h3 ▸ h)
  have hstep2 : bienayme μ {T | trunc k T ∈ 𝒮 ∧ (gen k T).length = ts.length} =
      ∑' ts', if ts'.length = ts.length then
        bienayme μ {T | trunc k T ∈ 𝒮 ∧ gen k T = ts'} else 0 := by
    rw [bienayme_eq_tsum_inter_fiber μ (gen k)]
    refine tsum_congr fun ts' => ?_
    split_ifs with hts'
    · congr 1
      ext T
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hts'⟩, h3⟩
    · convert measure_empty (μ := bienayme μ)
      ext T
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and, and_imp]
      intro _ h2 h3
      exact hts' (h3 ▸ h2)
  have hforest : ∑' ts' : List PlaneTree, (if ts'.length = ts.length then
      (ts'.map (weight μ)).prod else 0) = 1 := by
    have h := tsum_forest_list μ ts.length Set.univ
    rw [bienayme_univ hc h1, one_pow] at h
    rw [← h]
    refine tsum_congr fun ts' => ?_
    by_cases h' : ts'.length = ts.length
    · rw [ite_eq_left h', Set.indicator_of_mem (show ts' ∈ {ts' : List PlaneTree |
        ts'.length = ts.length ∧ ∀ U ∈ ts', U ∈ (Set.univ : Set PlaneTree)} from
        ⟨h', fun _ _ => trivial⟩)]
    · rw [ite_eq_right h', Set.indicator_of_notMem (fun h => h' h.1)]
  have hinner : ∀ S, ∑' ts', (if ts'.length = ts.length then F S ts' else 0) =
      𝒮.indicator (fun S => if trunc k S = S ∧ ts.length = genCount k S then
        skelWeight μ k S else 0) S := by
    intro S
    by_cases hS : S ∈ 𝒮
    · rw [Set.indicator_of_mem hS]
      simp only [hF, Set.indicator_of_mem hS, bienayme_trunc_gen_eq]
      by_cases hgood : trunc k S = S ∧ ts.length = genCount k S
      · rw [ite_eq_left hgood]
        conv_rhs => rw [← mul_one (skelWeight μ k S), ← hforest]
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun ts' => ?_
        by_cases h' : ts'.length = ts.length
        · rw [ite_eq_left h', ite_eq_left h', ite_eq_left ⟨hgood.1, h'.trans hgood.2⟩]
        · rw [ite_eq_right h', ite_eq_right h', mul_zero]
      · rw [ite_eq_right hgood]
        refine ENNReal.tsum_eq_zero.mpr fun ts' => ?_
        split_ifs with h' h''
        · exact absurd ⟨h''.1, h'.symm.trans h''.2⟩ hgood
        · rfl
        · rfl
    · simp only [hF, Set.indicator_of_notMem hS, ite_self, tsum_zero]
  rw [hstep1, hstep2]
  simp only [hstep1]
  have hite : ∀ ts' : List PlaneTree, (if ts'.length = ts.length then ∑' S, F S ts' else 0) =
      ∑' S, (if ts'.length = ts.length then F S ts' else 0) := by
    intro ts'
    split_ifs <;> simp
  simp only [hite]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun S => ?_
  rw [hinner S]
  by_cases hS : S ∈ 𝒮
  · simp only [hF, Set.indicator_of_mem hS, bienayme_trunc_gen_eq]
    split_ifs <;> simp
  · simp [hF, Set.indicator_of_notMem hS]

end PoissonDeclumping.PlaneTree
