/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.PlaneTree.Patterns
public import LeanPool.RareSubtreePatterns.Bienayme.Normalization
public import LeanPool.RareSubtreePatterns.Setup.Marks

/-!
# Non-fringe patterns: grafting at the leaves and the conditional law (U06)

Source lines 682 (definition of `T' ≺ T`), 1433–1445 (inventory U06) and 2468–2476.

`T' ≺ T` (`PlaneTree.Embeds T' T`) means that `T` is obtained from `T'` by grafting plane trees
onto the leaves of `T'`; internal vertices of `T'` keep their exact outdegree.

* `leafCount T'` (number of leaves `L`), `internalCount T'` (number of internal vertices `C`)
  and `patternWeight μ T' = ∏_{v ∈ T' internal} μ_{k_v(T')}`.
* `leafTrees T' T = (𝒯^{(1)}, …, 𝒯^{(L)})`: the trees grafted onto the leaves of `T'`, in DFS
  order; `graftLeaves T' ls = T'[ls]` grafts a list of `L` trees. `embedsEquiv T'` is the
  bijection `{T : T' ≺ T} ≃ {lists of L trees}`; `weight_eq_of_embeds`:
  `𝐏(𝒯 = T) = patternWeight μ T' ∏_i 𝐏(𝒯 = 𝒯^{(i)})`; `vertexCount_eq_of_embeds`:
  `|T| = C + ∑_{i ≤ L} |𝒯^{(i)}|`.
* `forestLaw μ L`: the law of a list of `L` independent `μ`-Bienaymé trees.
* U06: `bienayme_embeds_eq`: `𝐏(T' ≺ 𝒯) = ∏_{v ∈ T' internal} μ_{k_v(T')}`;
  `bienayme_embeds_leafTrees_mem`, `map_cond_embeds_leafTrees`, `cond_embeds_leafTrees_pi`:
  conditionally on `T' ≺ 𝒯`, the grafted trees `𝒯^{(1)}, …, 𝒯^{(L)}` are i.i.d. (unconditioned)
  `μ`-Bienaymé trees; `cond_embeds_eq_map_graftLeaves`: conditionally on `T' ≺ 𝒯`, `𝒯` has the
  law of `T'[𝒯^{(1)}, …, 𝒯^{(L)}]`; `skeleton_embeds`: the resulting decomposition
  `(𝒯, C, (𝒯^{(1)}, …, 𝒯^{(L)}))` is a `PoissonDeclumping.Skeleton` for the mark `T' ≺ ·`
  (Assumption (S) shape, used in the proof of Corollary `cor:Non-fringe Poisson`), with
  deterministic `C = internalCount T'` and `L = leafCount T'` (`embedsSkeletonLaw_ae`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PoissonDeclumping.PlaneTree

/-! ### Leaves, internal vertices and the pattern weight -/

/-- The number of leaves (vertices of outdegree `0`). -/
def leafCount (T : PlaneTree) : ℕ := T.degSeq.count 0

/-- The number of internal vertices (vertices of positive outdegree). -/
def internalCount (T : PlaneTree) : ℕ := T.degSeq.countP (· ≠ 0)

/-- `∏_{v ∈ T internal} μ_{k_v(T)}`: the product of the offspring masses over the internal
vertices only (leaves of a pattern receive grafted trees and contribute no factor). -/
noncomputable def patternWeight (μ : PMF ℕ) (T : PlaneTree) : ℝ≥0∞ :=
  ((T.degSeq.filter (· ≠ 0)).map μ).prod

@[simp] theorem degSeq_leaf : (node []).degSeq = [0] := by simp [degSeq_node]

@[simp] theorem leafCount_leaf : leafCount (node []) = 1 := by simp [leafCount]

@[simp] theorem internalCount_leaf : internalCount (node []) = 0 := by simp [internalCount]

@[simp] theorem patternWeight_leaf (μ : PMF ℕ) : patternWeight μ (node []) = 1 := by
  simp [patternWeight]

theorem leafCount_node {ts : List PlaneTree} (hts : ts ≠ []) :
    leafCount (node ts) = (ts.map leafCount).sum := by
  have h0 : ts.length ≠ 0 := by simpa using hts
  simp only [leafCount, degSeq_node, List.count_cons, List.count_flatMap]
  simp [h0, Function.comp_def]
  rfl

theorem internalCount_node {ts : List PlaneTree} (hts : ts ≠ []) :
    internalCount (node ts) = (ts.map internalCount).sum + 1 := by
  have h0 : ts.length ≠ 0 := by simpa using hts
  simp only [internalCount, degSeq_node, List.countP_cons, List.countP_flatMap,
    Function.comp_def]
  rw [ite_eq_left (by simpa using h0)]
  rfl

theorem patternWeight_node (μ : PMF ℕ) {ts : List PlaneTree} (hts : ts ≠ []) :
    patternWeight μ (node ts) = μ ts.length * (ts.map (patternWeight μ)).prod := by
  have h0 : ts.length ≠ 0 := by simpa using hts
  simp only [patternWeight, degSeq_node, List.filter_cons, List.filter_flatMap]
  simp only [ne_eq, h0, not_false_eq_true, decide_true, ite_true, List.map_cons, List.prod_cons]
  congr 1
  induction ts with
  | nil => simp
  | cons t ts ih =>
    by_cases hne : ts = []
    · subst hne
      simp [patternWeight]
    · have := ih hne (by simpa using hne)
      simp only [List.flatMap_cons, List.map_append, List.prod_append, List.map_cons,
        List.prod_cons] at this ⊢
      rw [this]
      rfl

private theorem count_zero_add_countP_ne (l : List ℕ) :
    l.count 0 + l.countP (· ≠ 0) = l.length := by
  rw [List.count_eq_countP, List.length_eq_countP_add_countP (· == 0)]
  congr 1

theorem leafCount_add_internalCount (T : PlaneTree) :
    T.leafCount + T.internalCount = T.vertexCount := by
  rw [leafCount, internalCount, count_zero_add_countP_ne, length_degSeq]

/-! ### Embeddings -/

theorem embeds_node_iff {cs : List PlaneTree} (hcs : cs ≠ []) {T : PlaneTree} :
    Embeds (node cs) T ↔ List.Forall₂ Embeds cs T.children := by
  constructor
  · intro h
    cases h with
    | leaf => exact absurd rfl hcs
    | node _ ts _ hlen h =>
      rw [List.forall₂_iff_get]
      exact ⟨hlen, fun i h₁ _ => by simpa using h i h₁⟩
  · intro h
    rw [eq_node_children T]
    have hlen := h.length_eq
    refine Embeds.node cs T.children hcs hlen fun i hi => ?_
    have := (List.forall₂_iff_get.1 h).2 i hi (hlen ▸ hi)
    simpa using this

/-- Induction principle for `Embeds` with the children handled by `List.Forall₂`. -/
theorem Embeds.induction' {P : PlaneTree → PlaneTree → Prop}
    (hleaf : ∀ T, P (PlaneTree.node []) T)
    (hnode : ∀ cs ts, cs ≠ [] → List.Forall₂ (fun c t => Embeds c t ∧ P c t) cs ts →
      P (PlaneTree.node cs) (PlaneTree.node ts))
    {T' T : PlaneTree} (h : Embeds T' T) : P T' T := by
  induction h with
  | leaf T => exact hleaf T
  | node cs ts hne hlen h ih =>
    apply hnode cs ts hne
    rw [List.forall₂_iff_get]
    exact ⟨hlen, fun i h₁ _ => ⟨by simpa using h i h₁, by simpa using ih i h₁⟩⟩

mutual
/-- `leafTrees T' T`: for `T' ≺ T`, the list `(𝒯^{(1)}, …, 𝒯^{(L)})` of the fringe subtrees of
`T` at the images of the leaves of `T'`, in DFS order (meaningful only when `Embeds T' T`). -/
def leafTrees : PlaneTree → PlaneTree → List PlaneTree
  | node [], T => [T]
  | node (c :: cs), T => leafTreesForest (c :: cs) T.children
/-- Forest version of `leafTrees`: concatenation over matched children. -/
def leafTreesForest : List PlaneTree → List PlaneTree → List PlaneTree
  | c :: cs, t :: ts => leafTrees c t ++ leafTreesForest cs ts
  | _, _ => []
end

@[simp] theorem leafTrees_leaf (T : PlaneTree) : leafTrees (node []) T = [T] := by
  rw [leafTrees]

theorem leafTrees_node {cs : List PlaneTree} (hcs : cs ≠ []) (T : PlaneTree) :
    leafTrees (node cs) T = leafTreesForest cs T.children := by
  cases cs with
  | nil => exact absurd rfl hcs
  | cons c cs => rw [leafTrees]

@[simp] theorem leafTreesForest_cons (c t : PlaneTree) (cs ts : List PlaneTree) :
    leafTreesForest (c :: cs) (t :: ts) = leafTrees c t ++ leafTreesForest cs ts := by
  rw [leafTreesForest]

@[simp] theorem leafTreesForest_nil_left (ts : List PlaneTree) : leafTreesForest [] ts = [] := by
  cases ts <;> rfl

theorem length_leafTrees {T' T : PlaneTree} (h : Embeds T' T) :
    (leafTrees T' T).length = leafCount T' := by
  refine Embeds.induction' (P := fun T' T => (leafTrees T' T).length = leafCount T')
    (fun T => by simp) (fun cs ts hcs hf => ?_) h
  · rw [leafTrees_node hcs, leafCount_node hcs, children_node]
    clear hcs
    induction hf with
    | nil => simp
    | cons h _ ih => simp [ih, h.2]

theorem weight_eq_of_embeds (μ : PMF ℕ) {T' T : PlaneTree} (h : Embeds T' T) :
    weight μ T = patternWeight μ T' * ((leafTrees T' T).map (weight μ)).prod := by
  refine Embeds.induction'
    (P := fun T' T => weight μ T = patternWeight μ T' * ((leafTrees T' T).map (weight μ)).prod)
    (fun T => by simp) (fun cs ts hcs hf => ?_) h
  · rw [leafTrees_node hcs, patternWeight_node μ hcs, children_node, weight_node,
      ← hf.length_eq, mul_assoc]
    congr 1
    clear hcs
    induction hf with
    | nil => simp
    | cons h _ ih =>
      simp only [List.map_cons, List.prod_cons, leafTreesForest_cons, List.map_append,
        List.prod_append]
      rw [h.2, ih]
      ring

theorem vertexCount_eq_of_embeds {T' T : PlaneTree} (h : Embeds T' T) :
    T.vertexCount = internalCount T' + ((leafTrees T' T).map vertexCount).sum := by
  refine Embeds.induction'
    (P := fun T' T => T.vertexCount = internalCount T' + ((leafTrees T' T).map vertexCount).sum)
    (fun T => by simp) (fun cs ts hcs hf => ?_) h
  · rw [leafTrees_node hcs, internalCount_node hcs, children_node, vertexCount_node]
    clear hcs
    suffices (ts.map vertexCount).sum =
        (cs.map internalCount).sum + ((leafTreesForest cs ts).map vertexCount).sum by omega
    induction hf with
    | nil => simp
    | cons h _ ih =>
      simp only [List.map_cons, List.sum_cons, leafTreesForest_cons, List.map_append,
        List.sum_append]
      rw [h.2, ih]
      ring

theorem eq_of_leafTrees_eq {T' T₁ T₂ : PlaneTree} (h₁ : Embeds T' T₁) (h₂ : Embeds T' T₂)
    (h : leafTrees T' T₁ = leafTrees T' T₂) : T₁ = T₂ := by
  refine Embeds.induction' (P := fun T' T₁ => ∀ T₂, Embeds T' T₂ →
      leafTrees T' T₁ = leafTrees T' T₂ → T₁ = T₂)
    (fun T T₂ _ h => by simpa using h) (fun cs ts hcs hf => ?_) h₁ T₂ h₂ h
  · intro T₂ h₂ h
    rw [embeds_node_iff hcs] at h₂
    rw [leafTrees_node hcs, leafTrees_node hcs, children_node] at h
    rw [eq_node_children T₂]
    congr 1
    clear hcs
    generalize T₂.children = us at h₂ h
    induction hf generalizing us with
    | nil =>
      cases h₂
      rfl
    | @cons c t cs ts hct _ ih =>
      cases h₂ with
      | @cons _ u _ us hcu h₂' =>
        simp only [leafTreesForest_cons] at h
        have hl : (leafTrees c t).length = (leafTrees c u).length := by
          rw [length_leafTrees hct.1, length_leafTrees hcu]
        obtain ⟨h1, h2⟩ := List.append_inj h hl
        rw [hct.2 u hcu h1, ih _ h₂' h2]

theorem exists_embeds_leafTrees_eq (T' : PlaneTree) :
    ∀ ls : List PlaneTree, ls.length = leafCount T' →
      ∃ T, Embeds T' T ∧ leafTrees T' T = ls := by
  induction T' using induction_children with
  | step T' ih =>
    intro ls hls
    cases T' with
    | node cs =>
      by_cases hcs : cs = []
      · subst hcs
        rw [leafCount_leaf, List.length_eq_one_iff] at hls
        obtain ⟨t, rfl⟩ := hls
        exact ⟨t, Embeds.leaf t, by simp⟩
      · rw [leafCount_node hcs] at hls
        have key : ∀ cs : List PlaneTree, (∀ c ∈ cs, ∀ ls : List PlaneTree,
            ls.length = leafCount c → ∃ T, Embeds c T ∧ leafTrees c T = ls) →
            ∀ ls : List PlaneTree, ls.length = (cs.map leafCount).sum →
            ∃ ts, List.Forall₂ Embeds cs ts ∧ leafTreesForest cs ts = ls := by
          intro cs
          induction cs with
          | nil =>
            intro _ ls hls
            simp only [List.map_nil, List.sum_nil, List.length_eq_zero_iff] at hls
            exact ⟨[], .nil, by simp [hls]⟩
          | cons c cs ihc =>
            intro hc ls hls
            simp only [List.map_cons, List.sum_cons] at hls
            obtain ⟨t, ht, htl⟩ := hc c (by simp) (ls.take (leafCount c)) (by simp; omega)
            obtain ⟨ts, hts, htsl⟩ := ihc (fun c' hc' => hc c' (by simp [hc']))
              (ls.drop (leafCount c)) (by simp; omega)
            exact ⟨t :: ts, .cons ht hts, by
              rw [leafTreesForest_cons, htl, htsl, List.take_append_drop]⟩
        obtain ⟨ts, hts, htsl⟩ := key cs (fun c hc => ih c (by simpa using hc)) ls hls
        refine ⟨node ts, (embeds_node_iff hcs).2 (by simpa using hts), ?_⟩
        rw [leafTrees_node hcs, children_node, htsl]

/-- `T'[ls]`: the tree obtained by grafting the trees of the list `ls` (of length
`leafCount T'`) onto the leaves of `T'`, in DFS order; characterized by `embeds_graftLeaves`
and `graftLeaves_leafTrees` (for lists of the wrong length it is the junk value `T'`). -/
noncomputable def graftLeaves (T' : PlaneTree) (ls : List PlaneTree) : PlaneTree := by
  classical
  exact if h : ∃ T, Embeds T' T ∧ leafTrees T' T = ls then h.choose else T'

theorem embeds_graftLeaves {T' : PlaneTree} {ls : List PlaneTree}
    (hls : ls.length = leafCount T') :
    Embeds T' (graftLeaves T' ls) ∧ leafTrees T' (graftLeaves T' ls) = ls := by
  have h := exists_embeds_leafTrees_eq T' ls hls
  rw [graftLeaves, dite_eq_left h]
  exact h.choose_spec

theorem graftLeaves_leafTrees {T' T : PlaneTree} (h : Embeds T' T) :
    graftLeaves T' (leafTrees T' T) = T :=
  eq_of_leafTrees_eq (embeds_graftLeaves (length_leafTrees h)).1 h
    (embeds_graftLeaves (length_leafTrees h)).2

/-- The bijection `{T : T' ≺ T} ≃ {(𝒯^{(1)}, …, 𝒯^{(L)})}`. -/
noncomputable def embedsEquiv (T' : PlaneTree) :
    {T : PlaneTree // Embeds T' T} ≃ {ls : List PlaneTree // ls.length = leafCount T'} where
  toFun T := ⟨leafTrees T' T.1, length_leafTrees T.2⟩
  invFun ls := ⟨graftLeaves T' ls.1, (embeds_graftLeaves ls.2).1⟩
  left_inv T := Subtype.ext (graftLeaves_leafTrees T.2)
  right_inv ls := Subtype.ext (embeds_graftLeaves ls.2).2

/-! ### Forest law -/

/-- The law of `L` independent `μ`-Bienaymé trees, as a measure on lists of trees:
`forestLaw μ L {[t_1, …, t_L]} = ∏_i 𝐏_μ(t_i)`, and lists of other lengths have mass zero. -/
noncomputable def forestLaw (μ : PMF ℕ) (L : ℕ) : Measure (List PlaneTree) :=
  Measure.sum fun ls : List PlaneTree =>
    {ls : List PlaneTree | ls.length = L}.indicator (fun ls => (ls.map (weight μ)).prod) ls •
      Measure.dirac ls

theorem forestLaw_apply (μ : PMF ℕ) (L : ℕ) (B : Set (List PlaneTree)) :
    forestLaw μ L B =
      ∑' ls, (B ∩ {ls | ls.length = L}).indicator (fun ls => (ls.map (weight μ)).prod) ls := by
  rw [forestLaw, Measure.sum_apply _ MeasurableSet.of_discrete]
  refine tsum_congr fun ls => ?_
  by_cases hB : ls ∈ B <;> by_cases hL : ls.length = L <;> simp [hB, hL]

theorem forestLaw_univ (μ : PMF ℕ) (L : ℕ) : forestLaw μ L Set.univ = bienayme μ Set.univ ^ L := by
  rw [forestLaw_apply, ← tsum_forest_list μ L Set.univ]
  refine tsum_congr fun ls => ?_
  simp

theorem forestLaw_pi (μ : PMF ℕ) (L : ℕ) (A : ℕ → Set PlaneTree) :
    forestLaw μ L {ls | ∀ (i : ℕ) (hi : i < ls.length), ls[i] ∈ A i} =
      ∏ i ∈ Finset.range L, bienayme μ (A i) := by
  rw [forestLaw_apply, ← List.equivSigmaTuple.symm.tsum_eq, ENNReal.tsum_sigma', tsum_eq_single L]
  · rw [← Fin.prod_univ_eq_prod_range (fun i => bienayme μ (A i)) L,
      ← tsum_forest_fin μ L (fun i => A i)]
    refine tsum_congr fun f => ?_
    simp only [List.equivSigmaTuple_symm_apply]
    by_cases hf : ∀ i : Fin L, f i ∈ A i
    · rw [Set.indicator_of_mem (show List.ofFn f ∈
          {ls : List PlaneTree | ∀ (i : ℕ) (hi : i < ls.length), ls[i] ∈ A i} ∩
            {ls | ls.length = L} from
          ⟨fun i hi => by simpa using hf ⟨i, by simpa using hi⟩, List.length_ofFn⟩),
        List.map_ofFn, List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hf i) _).symm
    · rw [Set.indicator_of_notMem]
      · push Not at hf
        obtain ⟨i, hi⟩ := hf
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
      · rintro ⟨h, -⟩
        exact hf fun i => by simpa using h i (by simp)
  · intro j hj
    refine ENNReal.tsum_eq_zero.2 fun f => Set.indicator_of_notMem ?_ _
    rintro ⟨-, h⟩
    simp only [List.equivSigmaTuple_symm_apply, Set.mem_ofPred_eq, List.length_ofFn] at h
    exact hj h

theorem forestLaw_singleton (μ : PMF ℕ) (L : ℕ) (ls : List PlaneTree) :
    forestLaw μ L {ls} = {ls : List PlaneTree | ls.length = L}.indicator
      (fun ls => (ls.map (weight μ)).prod) ls := by
  rw [forestLaw_apply, tsum_eq_single ls]
  · by_cases hL : ls.length = L <;> simp [hL]
  · intro ls' h
    exact Set.indicator_of_notMem (fun h' => h h'.1) _

/-! ### U06: the law of a non-fringe pattern occurrence -/

/-- `𝐏_μ(T' ≺ 𝒯, (𝒯^{(1)}, …, 𝒯^{(L)}) ∈ B) = (∏_{v ∈ T' internal} μ_{k_v}) 𝐏(F_L ∈ B)`, where
`F_L` is a list of `L` independent `μ`-Bienaymé trees (any offspring law). -/
theorem bienayme_embeds_leafTrees_mem (μ : PMF ℕ) (T' : PlaneTree) (B : Set (List PlaneTree)) :
    bienayme μ {T | Embeds T' T ∧ leafTrees T' T ∈ B} =
      patternWeight μ T' * forestLaw μ (leafCount T') B := by
  rw [bienayme_apply, forestLaw_apply, ← ENNReal.tsum_mul_left]
  set S := {T | Embeds T' T ∧ leafTrees T' T ∈ B} with hS
  let g : {ls : List PlaneTree // ls.length = leafCount T'} → PlaneTree :=
    fun ls => graftLeaves T' ls.1
  have hg : Function.Injective g := fun a b h => Subtype.ext (by
    rw [← (embeds_graftLeaves a.2).2, ← (embeds_graftLeaves b.2).2]
    exact congrArg _ h)
  have hsupp : Function.support (S.indicator (weight μ)) ⊆ Set.range g := fun T hT => by
    have hT' : T ∈ S := Set.support_indicator_subset hT
    exact ⟨⟨leafTrees T' T, length_leafTrees hT'.1⟩, graftLeaves_leafTrees hT'.1⟩
  rw [← hg.tsum_eq hsupp]
  rw [← tsum_subtype_eq_of_support_subset (s := {ls : List PlaneTree | ls.length = leafCount T'})]
  · refine tsum_congr fun ls => ?_
    obtain ⟨he, hl⟩ := embeds_graftLeaves ls.2
    by_cases hB : ls.1 ∈ B
    · rw [Set.indicator_of_mem (show g ls ∈ S from ⟨he, hl ▸ hB⟩),
        Set.indicator_of_mem (show ls.1 ∈ B ∩ _ from ⟨hB, ls.2⟩), weight_eq_of_embeds μ he, hl]
    · rw [Set.indicator_of_notMem (show g ls ∉ S from fun h => hB (hl ▸ h.2)),
        Set.indicator_of_notMem (show ls.1 ∉ B ∩ _ from fun h => hB h.1), mul_zero]
  · intro ls hls
    by_contra h
    exact hls (by dsimp only; rw [Set.indicator_of_notMem (fun h' => h h'.2), mul_zero])

theorem bienayme_embeds (μ : PMF ℕ) (T' : PlaneTree) :
    bienayme μ {T | Embeds T' T} = patternWeight μ T' * bienayme μ Set.univ ^ leafCount T' := by
  rw [← forestLaw_univ, ← bienayme_embeds_leafTrees_mem]
  simp

/-- U06/U07: `𝐏(T' ≺ 𝒯) = ∏_{v ∈ T' internal} μ_{k_v(T')}` for critical `μ` with `μ_1 ≠ 1`. -/
theorem bienayme_embeds_eq {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (T' : PlaneTree) :
    bienayme μ {T | Embeds T' T} = patternWeight μ T' := by
  rw [bienayme_embeds, bienayme_univ hc hne, one_pow, mul_one]

/-- The grafted trees are independent `μ`-Bienaymé trees:
`𝐏(T' ≺ 𝒯, 𝒯^{(i)} ∈ A_i ∀ i) = patternWeight μ T' ∏_{i < L} 𝐏(𝒯 ∈ A_i)`. -/
theorem bienayme_embeds_leafTrees_pi (μ : PMF ℕ) (T' : PlaneTree) (A : ℕ → Set PlaneTree) :
    bienayme μ {T | Embeds T' T ∧
        ∀ (i : ℕ) (hi : i < (leafTrees T' T).length), (leafTrees T' T)[i] ∈ A i} =
      patternWeight μ T' * ∏ i ∈ Finset.range (leafCount T'), bienayme μ (A i) := by
  rw [← forestLaw_pi, ← bienayme_embeds_leafTrees_mem]
  rfl

open ProbabilityTheory in
/-- U06: conditionally on `T' ≺ 𝒯`, the grafted list `(𝒯^{(1)}, …, 𝒯^{(L)})` has the law of `L`
independent unconditioned `μ`-Bienaymé trees. -/
theorem cond_embeds_leafTrees_mem {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {T' : PlaneTree} (hpos : 0 < bienayme μ {T | Embeds T' T}) (B : Set (List PlaneTree)) :
    ProbabilityTheory.cond (bienayme μ) {T | Embeds T' T} {T | leafTrees T' T ∈ B} =
      forestLaw μ (leafCount T') B := by
  rw [cond_apply MeasurableSet.of_discrete]
  have h := bienayme_embeds_leafTrees_mem μ T' B
  have he := bienayme_embeds_eq hc hne T'
  rw [he] at hpos ⊢
  rw [show {T | Embeds T' T} ∩ {T | leafTrees T' T ∈ B} =
      {T | Embeds T' T ∧ leafTrees T' T ∈ B} from rfl, h,
    ENNReal.inv_mul_cancel_left hpos.ne' (he ▸ measure_ne_top _ _)]

open ProbabilityTheory in
/-- U06, law form: the image of `𝐏(· | T' ≺ 𝒯)` under `T ↦ (𝒯^{(1)}, …, 𝒯^{(L)})` is the law of
`L` independent `μ`-Bienaymé trees. -/
theorem map_cond_embeds_leafTrees {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {T' : PlaneTree} (hpos : 0 < bienayme μ {T | Embeds T' T}) :
    (ProbabilityTheory.cond (bienayme μ) {T | Embeds T' T}).map (leafTrees T') =
      forestLaw μ (leafCount T') := by
  ext B hB
  rw [Measure.map_apply Measurable.of_discrete hB]
  exact cond_embeds_leafTrees_mem hc hne hpos B

open ProbabilityTheory in
/-- U06, product form: `𝐏(𝒯^{(i)} ∈ A_i for all i < L | T' ≺ 𝒯) = ∏_{i < L} 𝐏(𝒯 ∈ A_i)`. -/
theorem cond_embeds_leafTrees_pi {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {T' : PlaneTree} (hpos : 0 < bienayme μ {T | Embeds T' T}) (A : ℕ → Set PlaneTree) :
    ProbabilityTheory.cond (bienayme μ) {T | Embeds T' T}
        {T | ∀ (i : ℕ) (hi : i < (leafTrees T' T).length), (leafTrees T' T)[i] ∈ A i} =
      ∏ i ∈ Finset.range (leafCount T'), bienayme μ (A i) := by
  rw [← forestLaw_pi, ← cond_embeds_leafTrees_mem hc hne hpos]
  rfl

theorem forestLaw_length_eq (μ : PMF ℕ) (L n : ℕ) :
    forestLaw μ L {ls | ls.length = n} = if n = L then bienayme μ Set.univ ^ L else 0 := by
  rw [forestLaw_apply]
  split_ifs with h
  · subst h
    rw [← forestLaw_univ, forestLaw_apply]
    simp
  · refine ENNReal.tsum_eq_zero.2 fun ls => Set.indicator_of_notMem ?_ _
    rintro ⟨h1, h2⟩
    exact h (h1.symm.trans h2)

open ProbabilityTheory in
/-- The law `ρ` of `(𝒯, C, (𝒯^{(1)}, …, 𝒯^{(L)}))` under `𝐏(· | T' ≺ 𝒯)`, with the deterministic
number `C = internalCount T'` of internal vertices of the pattern. -/
noncomputable def embedsSkeletonLaw (μ : PMF ℕ) (T' : PlaneTree) :
    Measure (PlaneTree × ℕ × List PlaneTree) :=
  (ProbabilityTheory.cond (bienayme μ) {T | Embeds T' T}).map
    fun T => (T, internalCount T', leafTrees T' T)

theorem embedsSkeletonLaw_apply (μ : PMF ℕ) (T' : PlaneTree)
    (S : Set (PlaneTree × ℕ × List PlaneTree)) :
    embedsSkeletonLaw μ T' S = ProbabilityTheory.cond (bienayme μ) {T | Embeds T' T}
      {T | (T, internalCount T', leafTrees T' T) ∈ S} :=
  Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete

open ProbabilityTheory in
/-- U06 in the shape of Assumption (S) (source lines 1437–1440): for critical `μ` with
`μ_1 ≠ 1` and `𝐏(T' ≺ 𝒯) > 0`, `embedsSkeletonLaw μ T'` is a skeleton decomposition for the
mark `T' ≺ ·`: under `𝐏(· | T' ≺ 𝒯)`, `|𝒯| = C + ∑_{i ≤ L} |𝒯^{(i)}|` with i.i.d. unconditioned
`𝒯^{(i)}`. -/
theorem skeleton_embeds {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {T' : PlaneTree}
    (hpos : 0 < bienayme μ {T | Embeds T' T}) :
    Skeleton μ (Embeds T') (embedsSkeletonLaw μ T') where
  isProbabilityMeasure := by
    have := cond_isProbabilityMeasure (μ := bienayme μ) hpos.ne'
    rw [embedsSkeletonLaw]
    infer_instance
  law_tree := by
    rw [embedsSkeletonLaw, Measure.map_map measurable_fst Measurable.of_discrete]
    exact Measure.map_id
  conditionally_iid := by
    intro c ts
    rw [embedsSkeletonLaw_apply, embedsSkeletonLaw_apply]
    by_cases hcC : internalCount T' = c
    · simp only [Set.mem_ofPred_eq, hcC, true_and]
      have e1 := cond_embeds_leafTrees_mem hc hne hpos {ts}
      have e2 := cond_embeds_leafTrees_mem hc hne hpos {ls | ls.length = ts.length}
      simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq] at e1 e2
      rw [e1, e2, forestLaw_singleton, forestLaw_length_eq, bienayme_univ hc hne, one_pow]
      by_cases hL : ts.length = leafCount T'
      · rw [Set.indicator_of_mem
          (show ts ∈ {ls : List PlaneTree | ls.length = leafCount T'} from hL),
          ite_eq_left hL, one_mul]
      · rw [Set.indicator_of_notMem
          (show ts ∉ {ls : List PlaneTree | ls.length = leafCount T'} from hL),
          ite_eq_right hL, zero_mul]
    · simp [hcC]
  size_eq := by
    rw [embedsSkeletonLaw, ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete]
    filter_upwards [ae_cond_mem (μ := bienayme μ) (MeasurableSet.of_discrete)] with T hT
    exact vertexCount_eq_of_embeds hT

/-- Under `ρ`, `C` and `L` are deterministic and `𝒯 = T'[𝒯^{(1)}, …, 𝒯^{(L)}]`. -/
theorem embedsSkeletonLaw_ae (μ : PMF ℕ) (T' : PlaneTree) :
    ∀ᵐ ω ∂embedsSkeletonLaw μ T',
      ω.2.1 = internalCount T' ∧ ω.2.2.length = leafCount T' ∧ ω.1 = graftLeaves T' ω.2.2 := by
  rw [embedsSkeletonLaw, ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete]
  filter_upwards [ProbabilityTheory.ae_cond_mem (μ := bienayme μ) (MeasurableSet.of_discrete)]
    with T hT
  exact ⟨rfl, length_leafTrees hT, (graftLeaves_leafTrees hT).symm⟩

open ProbabilityTheory in
/-- U06, tree form: conditionally on `T' ≺ 𝒯`, the tree `𝒯` has the law of
`T'[𝒯^{(1)}, …, 𝒯^{(L)}]` with `𝒯^{(1)}, …, 𝒯^{(L)}` independent `μ`-Bienaymé trees. -/
theorem cond_embeds_eq_map_graftLeaves {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {T' : PlaneTree} (hpos : 0 < bienayme μ {T | Embeds T' T}) :
    ProbabilityTheory.cond (bienayme μ) {T | Embeds T' T} =
      (forestLaw μ (leafCount T')).map (graftLeaves T') := by
  ext S hS
  rw [Measure.map_apply Measurable.of_discrete hS, ← cond_embeds_leafTrees_mem hc hne hpos,
    cond_apply MeasurableSet.of_discrete, cond_apply MeasurableSet.of_discrete]
  congr 2
  ext T
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨h, hT⟩
    exact ⟨h, by rwa [graftLeaves_leafTrees h]⟩
  · rintro ⟨h, hT⟩
    exact ⟨h, by rwa [graftLeaves_leafTrees h] at hT⟩

end PoissonDeclumping.PlaneTree
