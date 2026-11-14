/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bridge.Truncation0

/-!
# The two-start bound (`P11`, Lemma `lem:boundb2`)

Work package WP4.7 of the bridge plan (no toolkit). Source lines 1832–1845.

The paper bounds `E[I_1^{(M_n)} I_{1+ℓ}^{(M_n)}]` (unconditioned walk) by `π_n² + A_n(ℓ)`. Its
argument says that if `v_{1+ℓ}` is not in the first tree `𝒯`, then the occurrences at `v_1` and
`v_{1+ℓ}` lie in "two independent Bienaymé trees"; the event `{v_{1+ℓ} ∉ 𝒯} = {|𝒯| ≤ ℓ}` depends on
`𝒯`, so this is made precise here (audit finding 5) by conditioning on the first passage time
`ζ = j`: for `j ≤ ℓ` the indicator at `ℓ + 1` is a function of the fresh increments after `ζ`
(`walkVecLaw_zeta_eq_inter_drop`), and for `j > ℓ` the vertex `v_{1+ℓ}` is `u_{ℓ+1}(𝒯)`.

## Main statements

* `walkVecLaw_ofSeq_mem_le`: `P(T(X_1..X_N) ∈ A) ≤ P(𝒯 ∈ A)`.
* `walkVecLaw_firstMarked_pair_le` (measure form, non-cyclic indicator):
  `P(I_1^{(M)} = 1, I_1^{(M)}(X_{ℓ+1}, …) = 1) ≤ P(G(𝒯)) P(G(𝒯), |𝒯| ≤ M) + A(ℓ)` for `ℓ + M ≤ N`.
* `walkVecLaw_real_firstMarked_pair_le`: the same in `ℝ` with the cyclic indicator `I_{1+ℓ}^{(M)}`,
  bounded by `P(G(𝒯))² + A(ℓ)`; `walkVecLaw_real_pair_le_markProb`: the paper's form
  `≤ π_n² + A_n(ℓ)` with `markProb` and `pairProb` of `Setup/Marks.lean`.

No restriction `ℓ ≥ 1` is needed (for `ℓ = 0` the bound is trivial).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PoissonDeclumping.Bridge

open Lukasiewicz PlaneTree Cyclic

/-- `P(T(X_1, …, X_N) ∈ A) ≤ P(𝒯 ∈ A)`: the first tree encoded by the walk is a Bienaymé tree
(cut at size `N`). -/
theorem walkVecLaw_ofSeq_mem_le (μ : PMF ℕ) (N : ℕ) (A : Set PlaneTree) :
    walkVecLaw μ N {ω | ∃ T ∈ A, ofSeq (List.ofFn ω) = some T} ≤ bienayme μ A := by
  have hsub : {ω : Fin N → ℤ | ∃ T ∈ A, ofSeq (List.ofFn ω) = some T} ⊆
      ⋃ j ∈ Finset.range (N + 1),
        {ω | zeta (List.ofFn ω) = some j ∧ ∃ T ∈ A, ofSeq (List.ofFn ω) = some T} := by
    rintro ω ⟨T, hTA, hT⟩
    have hz := zeta_eq_of_ofSeq_eq_some hT
    have hle := (zeta_eq_some_iff.mp hz).2.1
    rw [List.length_ofFn] at hle
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
    exact ⟨T.vertexCount, by omega, hz, T, hTA, hT⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (N + 1)))
      (fun j => A ∩ {T : PlaneTree | T.vertexCount = j}) := by
    intro i _ j _ hij
    refine Set.disjoint_left.mpr fun T hi hj => hij ?_
    rw [← hi.2, ← hj.2]
  calc walkVecLaw μ N {ω | ∃ T ∈ A, ofSeq (List.ofFn ω) = some T}
      ≤ walkVecLaw μ N (⋃ j ∈ Finset.range (N + 1),
        {ω | zeta (List.ofFn ω) = some j ∧ ∃ T ∈ A, ofSeq (List.ofFn ω) = some T}) :=
        measure_mono hsub
    _ ≤ ∑ j ∈ Finset.range (N + 1), walkVecLaw μ N
        {ω | zeta (List.ofFn ω) = some j ∧ ∃ T ∈ A, ofSeq (List.ofFn ω) = some T} :=
        measure_biUnion_finset_le _ _
    _ = ∑ j ∈ Finset.range (N + 1), bienayme μ (A ∩ {T | T.vertexCount = j}) :=
        Finset.sum_congr rfl fun j hj =>
          walkVecLaw_zeta_eq_ofSeq_mem μ (by have := Finset.mem_range.mp hj; omega) A
    _ = bienayme μ (⋃ j ∈ Finset.range (N + 1), A ∩ {T | T.vertexCount = j}) :=
        (measure_biUnion_finset hdisj fun _ _ => MeasurableSet.of_discrete).symm
    _ ≤ bienayme μ A := measure_mono (Set.iUnion₂_subset fun _ _ => Set.inter_subset_left)

/-- `∑_{j ∈ J} P(𝒯 ∈ A, |𝒯| = j) ≤ P(𝒯 ∈ A)`. -/
theorem sum_bienayme_vertexCount_eq_le (μ : PMF ℕ) (J : Finset ℕ) (A : Set PlaneTree) :
    ∑ j ∈ J, bienayme μ (A ∩ {T | T.vertexCount = j}) ≤ bienayme μ A := by
  have hdisj : Set.PairwiseDisjoint (↑J) (fun j => A ∩ {T : PlaneTree | T.vertexCount = j}) := by
    intro i _ j _ hij
    refine Set.disjoint_left.mpr fun T hi hj => hij ?_
    rw [← hi.2, ← hj.2]
  rw [← measure_biUnion_finset hdisj fun _ _ => MeasurableSet.of_discrete]
  exact measure_mono (Set.iUnion₂_subset fun _ _ => Set.inter_subset_left)

/-- **Two-start bound** (`P11`, Lemma `lem:boundb2`, source lines 1832–1845, corrected as in audit
finding 5). Let `ℓ + M ≤ N`. Then
`P(I_1^{(M)} = 1, I_{1+ℓ}^{(M)} = 1) ≤ P(G(𝒯) = 1) P(G(𝒯) = 1, |𝒯| ≤ M) +
P(|𝒯| ≥ ℓ + 1, G(𝒯) = 1, G(𝒯_{u_{ℓ+1}}) = 1)`, where `I_{1+ℓ}^{(M)}` reads `X_{ℓ+1}, …, X_{ℓ+M}`.

The proof conditions on the first passage time `ζ = j`: if `j ≤ ℓ`, the indicator at `ℓ + 1` only
depends on the fresh increments after `ζ` (strong Markov property at `ζ`); if `j > ℓ`, the vertex
`v_{ℓ+1}` lies in the first tree `𝒯 = T(𝐗)` and `I_{1+ℓ}^{(M)} = 1` forces
`G(𝒯_{u_{ℓ+1}}) = 1`. -/
theorem walkVecLaw_firstMarked_pair_le (μ : PMF ℕ) (G : PlaneTree → Prop) {M N ℓ : ℕ}
    (hN : ℓ + M ≤ N) :
    walkVecLaw μ N {ω | FirstMarked G M (List.ofFn ω) ∧ FirstMarked G M ((List.ofFn ω).drop ℓ)} ≤
      bienayme μ {T | G T} * bienayme μ {T | G T ∧ T.vertexCount ≤ M} +
        bienayme μ {T | ℓ + 1 ≤ T.vertexCount ∧ G T ∧ ∃ U ∈ T.fringeTrees[ℓ]?, G U} := by
  set Aℓ : Set PlaneTree :=
    {T | ℓ + 1 ≤ T.vertexCount ∧ G T ∧ ∃ U ∈ T.fringeTrees[ℓ]?, G U} with hAℓ
  set F : ℕ → Set (Fin N → ℤ) := fun j => {ω | zeta (List.ofFn ω) = some j ∧
    (∃ T ∈ {T : PlaneTree | G T}, ofSeq (List.ofFn ω) = some T) ∧
      (fun y : List ℤ => FirstMarked G M (y.drop (ℓ - j))) ((List.ofFn ω).drop j)} with hF
  have hsub : {ω : Fin N → ℤ | FirstMarked G M (List.ofFn ω) ∧
      FirstMarked G M ((List.ofFn ω).drop ℓ)} ⊆
      {ω | ∃ T ∈ Aℓ, ofSeq (List.ofFn ω) = some T} ∪ ⋃ j ∈ Finset.Icc 1 ℓ, F j := by
    rintro ω ⟨h1, h2⟩
    obtain ⟨T, hT, -, hG⟩ := firstMarked_iff.mp h1
    have hz := zeta_eq_of_ofSeq_eq_some hT
    obtain ⟨hz1, -, -, -⟩ := zeta_eq_some_iff.mp hz
    rcases le_or_gt T.vertexCount ℓ with hle | hgt
    · right
      simp only [Set.mem_iUnion, Finset.mem_Icc, exists_prop]
      refine ⟨T.vertexCount, ⟨hz1, hle⟩, hz, ⟨T, hG, hT⟩, ?_⟩
      change FirstMarked G M (((List.ofFn ω).drop T.vertexCount).drop (ℓ - T.vertexCount))
      rw [List.drop_drop, show T.vertexCount + (ℓ - T.vertexCount) = ℓ by omega]
      exact h2
    · left
      have hi : ℓ < T.fringeTrees.length := hgt
      refine ⟨T, ⟨hgt, hG, T.fringeTrees[ℓ]'hi, List.getElem?_eq_getElem hi, ?_⟩, hT⟩
      obtain ⟨y, hy⟩ := dfsSeq_fringeTrees_prefix T ℓ hi
      obtain ⟨m, hzm, hTd⟩ := ofSeq_eq_some_iff.mp hT
      have hm : m = T.vertexCount := by
        rw [hz] at hzm
        exact (Option.some.inj hzm).symm
      have hdrop : (List.ofFn ω).drop ℓ =
          (T.fringeTrees[ℓ]'hi).dfsSeq ++ (y ++ (List.ofFn ω).drop m) := by
        have hlen : ℓ ≤ ((List.ofFn ω).take m).length := by
          rw [← hTd, length_dfsSeq]
          omega
        rw [← List.append_assoc, hy, hTd, ← List.drop_append_of_le_length hlen,
          List.take_append_drop]
      have hU : ofSeq ((List.ofFn ω).drop ℓ) = some (T.fringeTrees[ℓ]'hi) := by
        rw [hdrop, ofSeq_dfsSeq_append]
      obtain ⟨T', hT', -, hG'⟩ := firstMarked_iff.mp h2
      rw [hU, Option.some.injEq] at hT'
      exact hT' ▸ hG'
  have hFj : ∀ j ∈ Finset.Icc 1 ℓ, walkVecLaw μ N (F j) =
      bienayme μ ({T | G T} ∩ {T | T.vertexCount = j}) *
        bienayme μ {T | G T ∧ T.vertexCount ≤ M} := by
    intro j hj
    have hjℓ := (Finset.mem_Icc.mp hj).2
    have h := walkVecLaw_zeta_eq_inter_drop μ (show j ≤ N by omega) {T : PlaneTree | G T}
      (fun y : List ℤ => FirstMarked G M (y.drop (ℓ - j)))
    refine h.trans ?_
    congr 1
    rw [walkVecLaw_drop μ (show ℓ - j ≤ N - j by omega) (FirstMarked G M),
      ← setOf_firstIndicator_eq_one, walkVecLaw_firstIndicator_eq μ G (by omega)]
    congr 1
    ext T
    simp only [Set.mem_ofPred_eq]
    exact and_comm
  calc walkVecLaw μ N {ω | FirstMarked G M (List.ofFn ω) ∧
        FirstMarked G M ((List.ofFn ω).drop ℓ)}
      ≤ walkVecLaw μ N ({ω | ∃ T ∈ Aℓ, ofSeq (List.ofFn ω) = some T} ∪
          ⋃ j ∈ Finset.Icc 1 ℓ, F j) := measure_mono hsub
    _ ≤ walkVecLaw μ N {ω | ∃ T ∈ Aℓ, ofSeq (List.ofFn ω) = some T} +
          ∑ j ∈ Finset.Icc 1 ℓ, walkVecLaw μ N (F j) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ bienayme μ Aℓ + ∑ j ∈ Finset.Icc 1 ℓ,
          bienayme μ ({T | G T} ∩ {T | T.vertexCount = j}) *
            bienayme μ {T | G T ∧ T.vertexCount ≤ M} := by
        rw [Finset.sum_congr rfl hFj]
        exact add_le_add (walkVecLaw_ofSeq_mem_le μ N Aℓ) le_rfl
    _ ≤ bienayme μ Aℓ + bienayme μ {T | G T} * bienayme μ {T | G T ∧ T.vertexCount ≤ M} := by
        rw [← Finset.sum_mul]
        exact add_le_add le_rfl (mul_le_mul_left (sum_bienayme_vertexCount_eq_le μ _ _) _)
    _ = _ := add_comm _ _

/-- **Two-start bound** (`P11`), in `ℝ` and with the cyclic indicator `I_{1+ℓ}^{(M)}`: for
`ℓ + M ≤ N`, `P(I_1^{(M)} = 1, I_{1+ℓ}^{(M)} = 1) ≤ P(G(𝒯) = 1)² + A(ℓ)`, where
`A(ℓ) = P(|𝒯| ≥ ℓ + 1, G(𝒯) = 1, G(𝒯_{u_{ℓ+1}}) = 1)`. -/
theorem walkVecLaw_real_firstMarked_pair_le (μ : PMF ℕ) (G : PlaneTree → Prop) {M N ℓ : ℕ}
    (hN : ℓ + M ≤ N) :
    (walkVecLaw μ N).real {ω | FirstMarked G M (List.ofFn ω) ∧
        FirstMarked G M ((List.ofFn ω).rotate ℓ)} ≤
      (bienayme μ).real {T | G T} ^ 2 +
        (bienayme μ).real {T | ℓ + 1 ≤ T.vertexCount ∧ G T ∧ ∃ U ∈ T.fringeTrees[ℓ]?, G U} := by
  have hset : {ω : Fin N → ℤ | FirstMarked G M (List.ofFn ω) ∧
      FirstMarked G M ((List.ofFn ω).rotate ℓ)} =
      {ω | FirstMarked G M (List.ofFn ω) ∧ FirstMarked G M ((List.ofFn ω).drop ℓ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [firstMarked_rotate_iff_drop (by rw [List.length_ofFn]; exact hN)]
  rw [hset, measureReal_def]
  refine (ENNReal.toReal_mono (by finiteness) (walkVecLaw_firstMarked_pair_le μ G hN)).trans ?_
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ← measureReal_def,
    ← measureReal_def, ← measureReal_def, sq]
  have hle : (bienayme μ).real {T | G T ∧ T.vertexCount ≤ M} ≤ (bienayme μ).real {T | G T} :=
    measureReal_mono fun T (hT : G T ∧ T.vertexCount ≤ M) => hT.1
  have := mul_le_mul_of_nonneg_left hle (measureReal_nonneg (μ := bienayme μ) (s := {T | G T}))
  linarith

/-- **Lemma `lem:boundb2`, unconditioned two-start bound** (source line 1843), in the paper's
notation: for `ℓ + M ≤ N`,
`P(I_1^{(M)} = 1, I_{1+ℓ}^{(M)} = 1) ≤ π_n² + A_n(ℓ)` with `G = G_{k_n}`. -/
theorem walkVecLaw_real_pair_le_markProb (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ)
    (n : ℕ) {M N ℓ : ℕ} (hN : ℓ + M ≤ N) :
    (walkVecLaw μ N).real {ω | FirstMarked (G (k n)) M (List.ofFn ω) ∧
        FirstMarked (G (k n)) M ((List.ofFn ω).rotate ℓ)} ≤
      markProb μ G k n ^ 2 + pairProb μ G k n ℓ :=
  walkVecLaw_real_firstMarked_pair_le μ (G (k n)) hN

end PoissonDeclumping.Bridge
