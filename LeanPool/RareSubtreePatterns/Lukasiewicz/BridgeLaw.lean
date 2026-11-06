/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Lukasiewicz.Excursion
public import LeanPool.RareSubtreePatterns.Bienayme.Conditioned
public import Mathlib.Probability.Distributions.Uniform


/-!
# The DFS law of `𝒯^n` and the cyclic-shift law `eq:shifts`

Section 2.2 of the paper (source lines 718–730), as equalities of measures.

Let `𝐗 = (X_i)_{i ≥ 1}` be i.i.d. with `P(X_1 = i) = μ_{i+1}` for `i ≥ -1`
(`Lukasiewicz.stepPMF μ`), and `S_k = X_1 + ⋯ + X_k`. The law of `(X_1, …, X_n)` is the product
measure `Lukasiewicz.walkVecLaw μ n` on `Fin n → ℤ`.

* `PlaneTree.map_dfsSeq_conditioned`: the DFS sequence of `𝒯^n` has the law of
  `(X_1, …, X_n)` under `P(· | ζ(𝐗) = n)`.
* `PlaneTree.map_shift_conditioned` (`eq:shifts`): if `I` is uniform on `{0, …, n-1}` and
  independent of `𝒯^n`, then the `I`-th cyclic shift `𝐱^{(I)}(𝒯^n)` has the law of
  `(X_1, …, X_n)` under `P(· | S_n = -1)`.
* `PlaneTree.walkVecLaw_sum_eq_neg_one`: `P(S_n = -1) = n P(|𝒯| = n)` (Kemperman / Dwass).

Here `𝒯^n` is `PlaneTree.conditioned μ n`, the `μ`-Bienaymé weights conditioned on `|T| = n`.
None of these statements needs criticality or normalization of the tree law: the conditioned
weights are normalized by their own total mass, and both sides are the zero measure when
`P(|𝒯| = n) = 0`. The paper's sequences are indexed from `1`; ours from `0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PoissonDeclumping

namespace Lukasiewicz

/-- The step law `P(X = i) = μ_{i+1}` (`i ≥ -1`): the image of `μ` under `k ↦ k - 1`. -/
noncomputable def stepPMF (μ : PMF ℕ) : PMF ℤ := μ.map fun k : ℕ => (k : ℤ) - 1

theorem stepPMF_apply (μ : PMF ℕ) (a : ℤ) :
    stepPMF μ a = if -1 ≤ a then μ (a + 1).toNat else 0 := by
  rw [stepPMF, PMF.map_apply]
  split_ifs with ha
  · rw [tsum_eq_single (a + 1).toNat]
    · rw [ite_eq_left (by omega)]
    · intro k hk
      rw [ite_eq_right (by omega)]
  · refine ENNReal.tsum_eq_zero.mpr fun k => ?_
    rw [ite_eq_right (by omega)]

/-- The law of `(X_1, …, X_n)`: `n` independent steps with law `stepPMF μ`. -/
noncomputable def walkVecLaw (μ : PMF ℕ) (n : ℕ) : Measure (Fin n → ℤ) :=
  Measure.pi fun _ => (stepPMF μ).toMeasure

instance (μ : PMF ℕ) (n : ℕ) : IsProbabilityMeasure (walkVecLaw μ n) := by
  unfold walkVecLaw
  infer_instance

theorem walkVecLaw_singleton (μ : PMF ℕ) (n : ℕ) (ω : Fin n → ℤ) :
    walkVecLaw μ n {ω} = ∏ i, stepPMF μ (ω i) := by
  rw [walkVecLaw, Measure.pi_singleton]
  exact Finset.prod_congr rfl fun i _ =>
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)

/-- `(X_1, …, X_n)` under `P(· | S_n = -1)`. -/
noncomputable def bridgeLaw (μ : PMF ℕ) (n : ℕ) : Measure (Fin n → ℤ) :=
  cond (walkVecLaw μ n) {ω | ∑ i, ω i = -1}

/-- `(X_1, …, X_n)` under `P(· | ζ(𝐗) = n)`. -/
noncomputable def excursionLaw (μ : PMF ℕ) (n : ℕ) : Measure (Fin n → ℤ) :=
  cond (walkVecLaw μ n) {ω | zeta (List.ofFn ω) = some n}

/-- A list read as a vector of length `n` (padded by zeros, truncated after `n` entries). -/
def toVec (n : ℕ) (x : List ℤ) : Fin n → ℤ := fun k => x.getD k 0

theorem toVec_ofFn {n : ℕ} (ω : Fin n → ℤ) : toVec n (List.ofFn ω) = ω := by
  funext k
  simp [toVec]

theorem ofFn_toVec {n : ℕ} {x : List ℤ} (hx : x.length = n) : List.ofFn (toVec n x) = x := by
  subst hx
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp [toVec, List.getElem?_eq_getElem h2]

theorem walkWeight_ofFn (μ : PMF ℕ) {n : ℕ} (ω : Fin n → ℤ) (hω : ∀ i, -1 ≤ ω i) :
    walkWeight μ (List.ofFn ω) = ∏ i, stepPMF μ (ω i) := by
  rw [walkWeight, List.map_ofFn, List.prod_ofFn]
  exact Finset.prod_congr rfl fun i _ => by
    rw [stepPMF_apply, ite_eq_left (hω i)]
    rfl

open Classical in
/-- Point masses of the walk law against a set `A` of admissible lists. -/
theorem tsum_walkWeight_mul_toVec {n : ℕ} (μ : PMF ℕ) {A : Set (List ℤ)}
    (hA : ∀ x ∈ A, x.length = n ∧ ∀ a ∈ x, -1 ≤ a) (ω : Fin n → ℤ) :
    ∑' x : A, walkWeight μ x.1 * (if toVec n x.1 = ω then 1 else 0) =
      if List.ofFn ω ∈ A then ∏ i, stepPMF μ (ω i) else 0 := by
  split_ifs with h
  · rw [tsum_eq_single ⟨_, h⟩]
    · rw [toVec_ofFn, ite_eq_left rfl, mul_one]
      refine walkWeight_ofFn μ ω fun i => (hA _ h).2 _ ?_
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    · rintro ⟨x, hx⟩ hne
      rw [ite_eq_right, mul_zero]
      intro he
      apply hne
      apply Subtype.ext
      change x = List.ofFn ω
      rw [← he, ofFn_toVec (hA x hx).1]
  · refine ENNReal.tsum_eq_zero.mpr fun ⟨x, hx⟩ => ?_
    rw [ite_eq_right, mul_zero]
    intro he
    apply h
    rw [← he, ofFn_toVec (hA x hx).1]
    exact hx

/-- The walk law of `B ∩ {ω}`, when `B` corresponds to a set `A` of admissible lists. -/
theorem walkVecLaw_inter_singleton {n : ℕ} (μ : PMF ℕ) {A : Set (List ℤ)} {B : Set (Fin n → ℤ)}
    (hA : ∀ x ∈ A, x.length = n ∧ ∀ a ∈ x, -1 ≤ a)
    (hAB : ∀ ω, List.ofFn ω ∈ A ↔ ω ∈ B ∧ ∀ i, -1 ≤ ω i) (ω : Fin n → ℤ) :
    walkVecLaw μ n (B ∩ {ω}) =
      ∑' x : A, walkWeight μ x.1 * (if toVec n x.1 = ω then 1 else 0) := by
  rw [tsum_walkWeight_mul_toVec μ hA]
  by_cases hB : ω ∈ B
  · rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hB), walkVecLaw_singleton]
    split_ifs with h
    · rfl
    · obtain ⟨i, hi⟩ : ∃ i, ω i < -1 := by
        by_contra hc
        exact h ((hAB ω).mpr ⟨hB, fun i => le_of_not_gt fun hi => hc ⟨i, hi⟩⟩)
      exact Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [stepPMF_apply, ite_eq_right (by omega)])
  · rw [Set.inter_singleton_eq_empty.mpr hB, measure_empty, ite_eq_right]
    exact fun h => hB ((hAB ω).mp h).1

/-- The walk law of `B`, when `B` corresponds to a set `A` of admissible lists. -/
theorem walkVecLaw_eq_tsum {n : ℕ} (μ : PMF ℕ) {A : Set (List ℤ)} {B : Set (Fin n → ℤ)}
    (hA : ∀ x ∈ A, x.length = n ∧ ∀ a ∈ x, -1 ≤ a)
    (hAB : ∀ ω, List.ofFn ω ∈ A ↔ ω ∈ B ∧ ∀ i, -1 ≤ ω i) :
    walkVecLaw μ n B = ∑' x : A, walkWeight μ x.1 := by
  rw [← Measure.tsum_indicator_apply_singleton _ B (Set.to_countable B).measurableSet]
  have h1 : ∀ ω, B.indicator (fun ω => walkVecLaw μ n {ω}) ω = walkVecLaw μ n (B ∩ {ω}) := by
    intro ω
    by_cases hB : ω ∈ B
    · rw [Set.indicator_of_mem hB, Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hB)]
    · rw [Set.indicator_of_notMem hB, Set.inter_singleton_eq_empty.mpr hB, measure_empty]
  simp_rw [h1, walkVecLaw_inter_singleton μ hA hAB]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  rw [ENNReal.tsum_mul_left]
  simp

theorem bridgeSet_admissible (n : ℕ) :
    ∀ x ∈ bridgeSet n, x.length = n ∧ ∀ a ∈ x, -1 ≤ a := fun _ hx => ⟨hx.1, hx.2.1⟩

theorem ofFn_mem_bridgeSet_iff {n : ℕ} (ω : Fin n → ℤ) :
    List.ofFn ω ∈ bridgeSet n ↔ ω ∈ {ω : Fin n → ℤ | ∑ i, ω i = -1} ∧ ∀ i, -1 ≤ ω i := by
  simp only [bridgeSet, Set.mem_ofPred_eq, List.length_ofFn, List.mem_ofFn, List.sum_ofFn,
    true_and, forall_exists_index, forall_apply_eq_imp_iff]
  exact and_comm

theorem excursionSet_admissible (n : ℕ) :
    ∀ x ∈ excursionSet n, x.length = n ∧ ∀ a ∈ x, -1 ≤ a := fun _ hx => ⟨hx.1, hx.2.1⟩

theorem ofFn_mem_excursionSet_iff {n : ℕ} (ω : Fin n → ℤ) :
    List.ofFn ω ∈ excursionSet n ↔
      ω ∈ {ω : Fin n → ℤ | zeta (List.ofFn ω) = some n} ∧ ∀ i, -1 ≤ ω i := by
  simp only [excursionSet, Set.mem_ofPred_eq, List.length_ofFn, List.mem_ofFn,
    true_and, forall_exists_index, forall_apply_eq_imp_iff]
  exact and_comm

/-- `P(S_n = -1) = Ψ_n(-1)`. -/
theorem walkVecLaw_sum_eq_neg_one_eq_walkMass (μ : PMF ℕ) (n : ℕ) :
    walkVecLaw μ n {ω | ∑ i, ω i = -1} = walkMass μ n (-1) :=
  walkVecLaw_eq_tsum μ (bridgeSet_admissible n) ofFn_mem_bridgeSet_iff

/-- `P(ζ(𝐗) = n)` is the total walk weight of `{ζ = n}`. -/
theorem walkVecLaw_zeta_eq (μ : PMF ℕ) (n : ℕ) :
    walkVecLaw μ n {ω | zeta (List.ofFn ω) = some n} = ∑' x : excursionSet n, walkWeight μ x.1 :=
  walkVecLaw_eq_tsum μ (excursionSet_admissible n) ofFn_mem_excursionSet_iff

end Lukasiewicz

namespace PlaneTree

open Lukasiewicz

theorem conditioned_singleton (μ : PMF ℕ) (n : ℕ) (T : PlaneTree) :
    conditioned μ n {T} =
      (bienayme μ {T | T.vertexCount = n})⁻¹ * if T.vertexCount = n then weight μ T else 0 := by
  rw [conditioned, cond_apply MeasurableSet.of_discrete]
  congr 1
  split_ifs with h
  · rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr
      (show T ∈ {T : PlaneTree | T.vertexCount = n} from h)), bienayme_apply_singleton]
  · rw [Set.inter_singleton_eq_empty.mpr
      (show T ∉ {T : PlaneTree | T.vertexCount = n} from h), measure_empty]

instance instIsZeroOrProbabilityMeasureConditioned (μ : PMF ℕ) (n : ℕ) :
    IsZeroOrProbabilityMeasure (conditioned μ n) := by
  unfold conditioned
  infer_instance

/-- **Kemperman / Dwass identity**: `P(S_n = -1) = n P(|𝒯| = n)`. -/
theorem walkVecLaw_sum_eq_neg_one (μ : PMF ℕ) (n : ℕ) :
    walkVecLaw μ n {ω | ∑ i, ω i = -1} = n * bienayme μ {T | T.vertexCount = n} := by
  rw [walkVecLaw_sum_eq_neg_one_eq_walkMass, bienayme_vertexCount_eq,
    natCast_mul_tsum_weight_eq_walkMass]

/-- `P(ζ(𝐗) = n) = P(|𝒯| = n)`. -/
theorem walkVecLaw_zeta_eq_bienayme (μ : PMF ℕ) (n : ℕ) :
    walkVecLaw μ n {ω | zeta (List.ofFn ω) = some n} = bienayme μ {T | T.vertexCount = n} := by
  rw [walkVecLaw_zeta_eq, bienayme_vertexCount_eq]
  have h := tsum_weight_mul_dfsSeq μ n (fun _ => 1)
  simp only [mul_one] at h
  rw [← h]
  refine (tsum_subtype {T : PlaneTree | T.vertexCount = n} (weight μ)).trans ?_
  refine tsum_congr fun T => ?_
  simp [Set.indicator_apply]

/-- `tsum_sum_weight_mul_rotate`, with the step weights written as `walkWeight`. -/
theorem tsum_sum_weight_mul_rotate_walkWeight (μ : PMF ℕ) (n : ℕ) (g : List ℤ → ℝ≥0∞) :
    ∑' T : {T : PlaneTree // T.vertexCount = n}, ∑ i : Fin n,
        weight μ T.1 * g (T.1.dfsSeq.rotate i) =
      ∑' x : bridgeSet n, walkWeight μ x.1 * g x.1 :=
  tsum_sum_weight_mul_rotate μ n g

/-- Sums against the conditioned law, in weights. -/
theorem tsum_conditioned_singleton_mul (μ : PMF ℕ) (n : ℕ) (h : PlaneTree → ℝ≥0∞) :
    ∑' T, conditioned μ n {T} * h T =
      (bienayme μ {T | T.vertexCount = n})⁻¹ *
        ∑' T : {T : PlaneTree // T.vertexCount = n}, weight μ T.1 * h T.1 := by
  simp_rw [conditioned_singleton, mul_assoc, ENNReal.tsum_mul_left]
  congr 1
  refine (((tsum_subtype {T : PlaneTree | T.vertexCount = n}
    (fun T => weight μ T * h T))).trans ?_).symm
  refine tsum_congr fun T => ?_
  by_cases hT : T.vertexCount = n <;> simp [hT]

/-- **DFS law of `𝒯^n`.** The DFS sequence of `𝒯^n` has the law of `(X_1, …, X_n)` under
`P(· | ζ(𝐗) = n)`. -/
theorem map_dfsSeq_conditioned (μ : PMF ℕ) (n : ℕ) :
    (conditioned μ n).map (fun T => toVec n T.dfsSeq) = excursionLaw μ n := by
  refine Measure.ext_of_singleton fun ω => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    ← Measure.tsum_indicator_apply_singleton _ _ (Set.to_countable _).measurableSet,
    excursionLaw, cond_apply (Set.to_countable _).measurableSet,
    walkVecLaw_inter_singleton μ (excursionSet_admissible n) ofFn_mem_excursionSet_iff,
    walkVecLaw_zeta_eq_bienayme,
    ← tsum_weight_mul_dfsSeq μ n (fun x => if toVec n x = ω then 1 else 0)]
  rw [← tsum_conditioned_singleton_mul μ n (fun T => if toVec n T.dfsSeq = ω then 1 else 0)]
  refine tsum_congr fun T => ?_
  by_cases hT : toVec n T.dfsSeq = ω
  · simp [hT]
  · simp [hT]

/-- The uniform law on `{0, …, n-1}`. -/
noncomputable def uniformIndex (n : ℕ) : Measure (Fin n) :=
  Measure.uniformOfFinset Finset.univ

theorem uniformIndex_singleton (n : ℕ) (i : Fin n) : uniformIndex n {i} = (n : ℝ≥0∞)⁻¹ := by
  rw [uniformIndex, Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]

/-- **`eq:shifts`.** If `I` is uniform on `{0, …, n-1}` and independent of `𝒯^n`, then the
cyclic shift `𝐱^{(I)}(𝒯^n)` has the law of `(X_1, …, X_n)` under `P(· | S_n = -1)`. -/
theorem map_shift_conditioned (μ : PMF ℕ) {n : ℕ} (hn : n ≠ 0) :
    ((conditioned μ n).prod (uniformIndex n)).map
        (fun p : PlaneTree × Fin n => toVec n (p.1.dfsSeq.rotate p.2)) =
      bridgeLaw μ n := by
  refine Measure.ext_of_singleton fun ω => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    ← Measure.tsum_indicator_apply_singleton _ _ (Set.to_countable _).measurableSet,
    bridgeLaw, cond_apply (Set.to_countable _).measurableSet,
    walkVecLaw_inter_singleton μ (bridgeSet_admissible n) ofFn_mem_bridgeSet_iff,
    walkVecLaw_sum_eq_neg_one,
    ← tsum_sum_weight_mul_rotate_walkWeight μ n (fun x => if toVec n x = ω then 1 else 0),
    ENNReal.mul_inv (Or.inl (by exact_mod_cast hn)) (Or.inl (ENNReal.natCast_ne_top n)),
    ENNReal.tsum_prod']
  have h1 : ∀ T : PlaneTree, ∑' i : Fin n, (Set.indicator
      ((fun p : PlaneTree × Fin n => toVec n (p.1.dfsSeq.rotate p.2)) ⁻¹' {ω})
      (fun p => ((conditioned μ n).prod (uniformIndex n)) {p}) (T, i)) =
      conditioned μ n {T} * ((n : ℝ≥0∞)⁻¹ *
        ∑ i : Fin n, if toVec n (T.dfsSeq.rotate i) = ω then 1 else 0) := by
    intro T
    rw [tsum_fintype, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : toVec n (T.dfsSeq.rotate i) = ω
    · rw [Set.indicator_of_mem (by exact hi), ← Set.singleton_prod_singleton,
        Measure.prod_prod, uniformIndex_singleton, ite_eq_left hi, mul_one]
    · rw [Set.indicator_of_notMem (by exact hi), ite_eq_right hi, mul_zero, mul_zero]
  simp_rw [h1]
  rw [tsum_conditioned_singleton_mul μ n (fun T => (n : ℝ≥0∞)⁻¹ *
    ∑ i : Fin n, if toVec n (T.dfsSeq.rotate i) = ω then 1 else 0)]
  rw [mul_comm ((n : ℝ≥0∞)⁻¹), mul_assoc]
  congr 1
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun T => ?_
  rw [mul_left_comm, Finset.mul_sum]

end PlaneTree

end PoissonDeclumping
