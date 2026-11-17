/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Cyclic.UniformVertex

/-!
# Markov decompositions of the Łukasiewicz walk (`B05`)

Source lines 806–824 (Markov property at `ζ` in the proof of Corollary `cor:cyclicshift`) and
1740–1772 (Markov property at a deterministic time and at `ζ = j`, proof of Lemma `lem:pnqn`).

Write `(X_1, …, X_{m+k})` as the first block `(X_1, …, X_m)` and the fresh block
`(X_{m+1}, …, X_{m+k})`; these are independent (`walkVecLaw_map_split`).

* `Cyclic.walkVecLaw_zeta_eq_inter`: **first-tree stopping time and fresh increments after `ζ`.**
  The event `{ζ = m, T(𝐗) ∈ A}` depends only on the first `m` increments, has probability
  `P(𝒯 ∈ A, |𝒯| = m)`, and is independent of the increments after time `m`:
  `P(ζ = m, T(𝐗) ∈ A, (X_{m+1}, …, X_{m+k}) ∈ B) = P(𝒯 ∈ A, |𝒯| = m) P((X_1, …, X_k) ∈ B)`.
* `Cyclic.walkVecLaw_firstIndicator_eq`: `P(I_1^{(M)}(X_1, …, X_n) = 1) = P(G(𝒯) = 1, |𝒯| ≤ M)`
  for `M ≤ n` (countable decomposition according to `ζ = j ≤ M`).
* `Cyclic.walkVecLaw_firstIndicator_inter_sum`: **Markov property at the deterministic time `M`.**
  `P(I_1^{(M)} = 1, S_{M+k} = i) = E[I_1^{(M)} Ψ_k(i - S_M)]`; with `i = -1` and `n = M + k`
  this is the formula `P(I_1^{(M)} = 1, S_n = -1) = E[I_1^{(M)} Ψ_{n-M}(-1 - S_M)]` of source
  line 1745.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PoissonDeclumping.Cyclic

open Lukasiewicz PlaneTree

/-- `(x_1, …, x_{m+k}) = (x_1, …, x_m) (x_{m+1}, …, x_{m+k})` as lists. -/
theorem ofFn_eq_append {m k : ℕ} (ω : Fin (m + k) → ℤ) :
    List.ofFn ω = List.ofFn (fun i : Fin m => ω (Fin.castAdd k i)) ++
      List.ofFn (fun j : Fin k => ω (Fin.natAdd m j)) :=
  List.ofFn_add

/-- The first passage time at the end of a prefix only depends on the prefix. -/
theorem zeta_append_eq_some_iff {x y : List ℤ} {m : ℕ} (hx : x.length = m) :
    zeta (x ++ y) = some m ↔ zeta x = some m := by
  rw [← List.take_left' (l₂ := y) hx, zeta_take_eq_some_iff, List.take_left' hx]
  simp

/-- If `ζ(𝐱) = |𝐱|`, then `T(𝐱 𝐲) = T(𝐱)`. -/
theorem ofSeq_append_of_zeta {x y : List ℤ} (hx : zeta x = some x.length) :
    ofSeq (x ++ y) = ofSeq x := by
  have hz : zeta (x ++ y) = some x.length := (zeta_append_eq_some_iff rfl).mpr hx
  rw [← ofSeq_take_of_zeta_eq hz le_rfl, List.take_left' rfl]

/-- The law of the first excursion: `P(ζ(X_1, …, X_m) = m, T(𝐗) ∈ A) = P(𝒯 ∈ A, |𝒯| = m)`. -/
theorem walkVecLaw_zeta_eq_length (μ : PMF ℕ) (m : ℕ) (A : Set PlaneTree) :
    walkVecLaw μ m {a | zeta (List.ofFn a) = some m ∧ ∃ T ∈ A, ofSeq (List.ofFn a) = some T} =
      bienayme μ (A ∩ {T | T.vertexCount = m}) := by
  classical
  set A' : Set (List ℤ) := {x | x ∈ excursionSet m ∧ ∃ T ∈ A, ofSeq x = some T}
  have hA : ∀ x ∈ A', x.length = m ∧ ∀ a ∈ x, -1 ≤ a :=
    fun x hx => excursionSet_admissible m x hx.1
  have hAB : ∀ ω : Fin m → ℤ, List.ofFn ω ∈ A' ↔
      ω ∈ {a : Fin m → ℤ | zeta (List.ofFn a) = some m ∧
        ∃ T ∈ A, ofSeq (List.ofFn a) = some T} ∧ ∀ i, -1 ≤ ω i := by
    intro ω
    change (List.ofFn ω ∈ excursionSet m ∧ _) ↔ _
    rw [ofFn_mem_excursionSet_iff]
    simp only [Set.mem_ofPred_eq]
    tauto
  rw [walkVecLaw_eq_tsum μ hA hAB]
  have h1 : ∑' x : A', walkWeight μ x.1 = ∑' x : excursionSet m,
      walkWeight μ x.1 * (ofSeq x.1).elim 0 (A.indicator 1) := by
    rw [tsum_subtype A' (walkWeight μ), tsum_subtype (excursionSet m)
      (fun x => walkWeight μ x * (ofSeq x).elim 0 (A.indicator 1))]
    refine tsum_congr fun x => ?_
    by_cases hx : x ∈ excursionSet m
    · rw [Set.indicator_of_mem hx]
      cases hT : ofSeq x with
      | none =>
        have : x ∉ A' := fun h => by obtain ⟨-, T, -, hT'⟩ := h; simp [hT] at hT'
        simp [Set.indicator_of_notMem this]
      | some T =>
        by_cases hTs : T ∈ A
        · have : x ∈ A' := ⟨hx, T, hTs, hT⟩
          simp [Set.indicator_of_mem this, Set.indicator_of_mem hTs]
        · have : x ∉ A' := fun h => by
            obtain ⟨-, U, hU, hU'⟩ := h
            rw [hT, Option.some.injEq] at hU'
            exact hTs (hU' ▸ hU)
          simp [Set.indicator_of_notMem this, Set.indicator_of_notMem hTs]
    · have : x ∉ A' := fun h => hx h.1
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]
  have h2 : ∑' T : {T : PlaneTree // T.vertexCount = m},
      weight μ T.1 * (ofSeq T.1.dfsSeq).elim 0 (A.indicator 1) =
      ∑' T : PlaneTree, {T : PlaneTree | T.vertexCount = m}.indicator
        (fun T => weight μ T * (ofSeq T.dfsSeq).elim 0 (A.indicator 1)) T :=
    tsum_subtype {T : PlaneTree | T.vertexCount = m}
      (fun T => weight μ T * (ofSeq T.dfsSeq).elim 0 (A.indicator 1))
  rw [h1, ← tsum_weight_mul_dfsSeq μ m (fun x => (ofSeq x).elim 0 (A.indicator 1)), h2,
    bienayme_apply]
  refine tsum_congr fun T => ?_
  by_cases hT : T.vertexCount = m <;> by_cases hA : T ∈ A <;>
    simp [Set.indicator_apply, hT, hA, ofSeq_dfsSeq]

/-- **`B05`: first-tree stopping time and fresh increments after `ζ`.** The event
`{ζ = m, T(𝐗) ∈ A}` is determined by `(X_1, …, X_m)`, has probability `P(𝒯 ∈ A, |𝒯| = m)`, and the
increments `(X_{m+1}, …, X_{m+k})` after time `ζ = m` are independent of it with the law of
`(X_1, …, X_k)`. -/
theorem walkVecLaw_zeta_eq_inter (μ : PMF ℕ) (m k : ℕ) (A : Set PlaneTree)
    (B : Set (Fin k → ℤ)) :
    walkVecLaw μ (m + k) {ω | zeta (List.ofFn ω) = some m ∧
        (∃ T ∈ A, ofSeq (List.ofFn ω) = some T) ∧ (fun j : Fin k => ω (Fin.natAdd m j)) ∈ B} =
      bienayme μ (A ∩ {T | T.vertexCount = m}) * walkVecLaw μ k B := by
  set E : Set (Fin m → ℤ) :=
    {a | zeta (List.ofFn a) = some m ∧ ∃ T ∈ A, ofSeq (List.ofFn a) = some T}
  have hset : {ω : Fin (m + k) → ℤ | zeta (List.ofFn ω) = some m ∧
      (∃ T ∈ A, ofSeq (List.ofFn ω) = some T) ∧ (fun j : Fin k => ω (Fin.natAdd m j)) ∈ B} =
      (fun ω : Fin (m + k) → ℤ => ((fun i : Fin m => ω (Fin.castAdd k i)),
        (fun j : Fin k => ω (Fin.natAdd m j)))) ⁻¹' (E ×ˢ B) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, E]
    rw [ofFn_eq_append ω]
    set a := List.ofFn (fun i : Fin m => ω (Fin.castAdd k i))
    have ha : a.length = m := List.length_ofFn
    rw [zeta_append_eq_some_iff ha]
    constructor
    · rintro ⟨hz, hT, hB⟩
      rw [ofSeq_append_of_zeta (by rw [ha]; exact hz)] at hT
      exact ⟨⟨hz, hT⟩, hB⟩
    · rintro ⟨⟨hz, hT⟩, hB⟩
      rw [ofSeq_append_of_zeta (by rw [ha]; exact hz)]
      exact ⟨hz, hT, hB⟩
  rw [hset, ← Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    walkVecLaw_map_split, Measure.prod_prod, walkVecLaw_zeta_eq_length]

/-- `P(ζ = j, T(X_1, …, X_n) ∈ A) = P(𝒯 ∈ A, |𝒯| = j)` for `j ≤ n`. -/
theorem walkVecLaw_zeta_eq_ofSeq_mem (μ : PMF ℕ) {j n : ℕ} (hj : j ≤ n) (A : Set PlaneTree) :
    walkVecLaw μ n {ω | zeta (List.ofFn ω) = some j ∧ ∃ T ∈ A, ofSeq (List.ofFn ω) = some T} =
      bienayme μ (A ∩ {T | T.vertexCount = j}) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have := walkVecLaw_zeta_eq_inter μ j k A Set.univ
  simp only [Set.mem_univ, and_true, measure_univ, mul_one] at this
  exact this

/-- `p = P(I_1^{(M)}(X_1, …, X_n) = 1) = P(G(𝒯) = 1, |𝒯| ≤ M)` for `M ≤ n`: decompose according
to the value `j ≤ M` of `ζ`. -/
theorem walkVecLaw_firstIndicator_eq (μ : PMF ℕ) (G : PlaneTree → Prop) {M n : ℕ} (hM : M ≤ n) :
    walkVecLaw μ n {ω | firstIndicator G M (List.ofFn ω) = 1} =
      bienayme μ {T | T.vertexCount ≤ M ∧ G T} := by
  have h1 : {ω : Fin n → ℤ | firstIndicator G M (List.ofFn ω) = 1} =
      ⋃ j ∈ Finset.range (M + 1),
        {ω | zeta (List.ofFn ω) = some j ∧ ∃ T ∈ {T | G T}, ofSeq (List.ofFn ω) = some T} := by
    ext ω
    simp only [Set.mem_ofPred_eq, firstIndicator_eq_one_iff, Set.mem_iUnion, Finset.mem_range,
      exists_prop]
    constructor
    · rintro ⟨m, hz, hm, T, hT, hG⟩
      exact ⟨m, by exact_mod_cast Nat.lt_succ_of_le (by exact_mod_cast hm), hz, T, hG, hT⟩
    · rintro ⟨m, hm, hz, T, hG, hT⟩
      exact ⟨m, hz, by exact_mod_cast Nat.le_of_lt_succ hm, T, hT, hG⟩
  have h2 : {T : PlaneTree | T.vertexCount ≤ M ∧ G T} =
      ⋃ j ∈ Finset.range (M + 1), ({T | G T} ∩ {T : PlaneTree | T.vertexCount = j}) := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_range,
      exists_prop]
    constructor
    · rintro ⟨hT, hG⟩
      exact ⟨T.vertexCount, by omega, hG, rfl⟩
    · rintro ⟨j, hj, hG, rfl⟩
      exact ⟨by omega, hG⟩
  rw [h1, h2, measure_biUnion_finset, measure_biUnion_finset]
  · refine Finset.sum_congr rfl fun j hj => ?_
    exact walkVecLaw_zeta_eq_ofSeq_mem μ (by have := Finset.mem_range.mp hj; omega) _
  · intro i _ j _ hij
    refine Set.disjoint_left.mpr fun T hi hj => hij ?_
    rw [← hi.2, ← hj.2]
  · exact fun _ _ => MeasurableSet.of_discrete
  · intro i _ j _ hij
    refine Set.disjoint_left.mpr fun ω hi hj => hij ?_
    have := hi.1.symm.trans hj.1
    exact Option.some.inj this
  · exact fun _ _ => (Set.to_countable _).measurableSet

/-- **Markov property at the deterministic time `M`.** For `n = M + k`,
`P(I_1^{(M)}(X_1, …, X_n) = 1, S_n = i) = E[I_1^{(M)}(X_1, …, X_M) Ψ_{n-M}(i - S_M)]`. -/
theorem walkVecLaw_firstIndicator_inter_sum (μ : PMF ℕ) (G : PlaneTree → Prop) (M k : ℕ)
    (i : ℤ) :
    walkVecLaw μ (M + k) {ω | firstIndicator G M (List.ofFn ω) = 1 ∧ ∑ j, ω j = i} =
      ∫⁻ a, (firstIndicator G M (List.ofFn a) : ℝ≥0∞) * walkLaw μ k {i - ∑ j, a j}
        ∂walkVecLaw μ M := by
  classical
  set S : Set ((Fin M → ℤ) × (Fin k → ℤ)) :=
    {p | firstIndicator G M (List.ofFn p.1) = 1 ∧ ∑ j, p.1 j + ∑ j, p.2 j = i}
  have hset : {ω : Fin (M + k) → ℤ | firstIndicator G M (List.ofFn ω) = 1 ∧ ∑ j, ω j = i} =
      (fun ω : Fin (M + k) → ℤ => ((fun j : Fin M => ω (Fin.castAdd k j)),
        (fun j : Fin k => ω (Fin.natAdd M j)))) ⁻¹' S := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, S]
    rw [Fin.sum_univ_add, ← firstIndicator_take G M (List.ofFn ω), ofFn_eq_append ω,
      List.take_left' List.length_ofFn]
  rw [hset, ← Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    walkVecLaw_map_split, Measure.prod_apply (Set.to_countable _).measurableSet]
  refine lintegral_congr fun a => ?_
  rcases firstIndicator_eq_zero_or_eq_one G M (List.ofFn a) with h | h
  · have : Prod.mk a ⁻¹' S = ∅ := by
      ext b
      simp [S, h]
    rw [this, measure_empty, h, Nat.cast_zero, zero_mul]
  · have : Prod.mk a ⁻¹' S = {b | ∑ j, b j = i - ∑ j, a j} := by
      ext b
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, S, h, true_and]
      omega
    rw [this, h, Nat.cast_one, one_mul, walkLaw_singleton]

end PoissonDeclumping.Cyclic
