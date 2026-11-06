/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Cyclic.Indicators
public import LeanPool.RareSubtreePatterns.Cyclic.WalkBridge
public import LeanPool.RareSubtreePatterns.Setup.Marks

/-!
# Lemma `lem:RW`: cyclic indicator sums under the walk bridge

Source lines 758–764. For every mark `G`, every cutoff `M ∈ ℕ ∪ {∞}` and every `n`,
$$\sum_{i=1}^{n} I^{(M)}_{i}(\mathbf{x}(\mathcal T^{n})) \overset{(d)}{=}
\sum_{i=1}^{n} I^{(M)}_{i}(X_{1}, \ldots,X_{n}) \text{ under } P(\cdot \mid S_{n}=-1).$$

`Cyclic.map_cyclicSum_conditioned` states this as an equality of laws on `ℕ`: the push-forward of
`𝒯^n = PlaneTree.conditioned μ n` under `T ↦ ∑_i I_i^{(M)}(𝐱(T))` equals the push-forward of
`Lukasiewicz.bridgeLaw μ n` (the law of `(X_1, …, X_n)` given `S_n = -1`) under
`ω ↦ ∑_i I_i^{(M)}(ω)`. It holds for every `n`: at inadmissible `n` both sides are the zero
measure (`Cyclic.bridgeLaw_eq_zero_of_not_admissible`).

The proof is the paper's: `eq:shifts` (`PlaneTree.map_shift_conditioned`) and the invariance of the
cyclic sum under cyclic shifts (`Cyclic.cyclicSum_rotate`, `B04`). Combined with the counting
identity, the law of the (truncated) number of marked fringe subtrees of `𝒯^n` is the law of the
cyclic sum under the bridge (`Cyclic.map_markCount_conditioned`, `Cyclic.markedCountLaw_eq`).

`B04`, second part: the bridge law is invariant under permutations of the coordinates
(`Cyclic.map_bridgeLaw_comp_perm`), so all cyclic indicators have the same law under the bridge
(`Cyclic.bridgeLaw_shiftIndicator_eq_one`) and
`E[∑_i I_i^{(M)} | S_n = -1] = n P(I_1^{(M)} = 1 | S_n = -1)`
  (`Cyclic.lintegral_cyclicSum_bridgeLaw`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PoissonDeclumping.Cyclic

open Lukasiewicz PlaneTree

/-- The uniform index law has total mass one for `n ≠ 0`. -/
theorem uniformIndex_univ {n : ℕ} (hn : n ≠ 0) : uniformIndex n Set.univ = 1 := by
  classical
  rw [uniformIndex, Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true_of_mem fun _ _ => trivial, Finset.card_univ,
    Fintype.card_fin]
  exact ENNReal.div_self (by simpa using hn) (ENNReal.natCast_ne_top _)

/-- `(X_1, …, X_n)` given `S_n = -1` is the zero measure when `S_n = -1` is impossible. -/
theorem bridgeLaw_eq_zero_of_not_admissible (μ : PMF ℕ) {n : ℕ} (h : ¬Admissible μ n) :
    bridgeLaw μ n = 0 := by
  refine cond_eq_zero_of_meas_eq_zero ?_
  rw [walkVecLaw_sum_eq_neg_one, le_antisymm (not_lt.mp h) zero_le, mul_zero]

/-- Under `𝒯^n ⊗ Unif{0, …, n-1}`, the tree has `n` vertices almost surely. -/
theorem ae_vertexCount_prod (μ : PMF ℕ) (n : ℕ) :
    ∀ᵐ p ∂(conditioned μ n).prod (uniformIndex n), p.1.vertexCount = n :=
  Measure.quasiMeasurePreserving_fst.ae
    (ae_cond_mem (s := {T : PlaneTree | T.vertexCount = n}) MeasurableSet.of_discrete)

/-- **Lemma `lem:RW`.** For every mark `G`, cutoff `M ∈ ℕ ∪ {∞}` and size `n`, the law of
`∑_{i=1}^{n} I_i^{(M)}(𝐱(𝒯^n))` equals the law of `∑_{i=1}^{n} I_i^{(M)}(X_1, …, X_n)` under
`P(· | S_n = -1)`. -/
theorem map_cyclicSum_conditioned (μ : PMF ℕ) (G : PlaneTree → Prop) (M : ℕ∞) (n : ℕ) :
    (conditioned μ n).map (fun T => cyclicSum G M T.dfsSeq) =
      (bridgeLaw μ n).map (fun ω => cyclicSum G M (List.ofFn ω)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [conditioned_eq_zero_of_not_admissible (not_admissible_zero μ),
      bridgeLaw_eq_zero_of_not_admissible μ (not_admissible_zero μ), Measure.map_zero,
      Measure.map_zero]
  rw [← map_shift_conditioned μ hn.ne', Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _)]
  have hae : (fun ω : Fin n → ℤ => cyclicSum G M (List.ofFn ω)) ∘
      (fun p : PlaneTree × Fin n => toVec n (p.1.dfsSeq.rotate p.2)) =ᵐ[(conditioned μ n).prod
        (uniformIndex n)] (fun T : PlaneTree => cyclicSum G M T.dfsSeq) ∘ Prod.fst := by
    filter_upwards [ae_vertexCount_prod μ n] with p hp
    simp only [Function.comp_apply]
    rw [ofFn_toVec (by rw [List.length_rotate, length_dfsSeq, hp]), cyclicSum_rotate]
  rw [Measure.map_congr hae, ← Measure.map_map (measurable_of_countable _) measurable_fst,
    Measure.map_fst_prod, uniformIndex_univ hn.ne', one_smul]

/-- **Lemma `lem:RW`, count form.** The law of the number of vertices `v` of `𝒯^n` with
`|𝒯^n_v| ≤ M` and `G(𝒯^n_v) = 1` (the truncated count when `M < n`) is the law of
`∑_{i=1}^{n} I_i^{(M)}(X_1, …, X_n)` under `P(· | S_n = -1)`. -/
theorem map_markCount_conditioned (μ : PMF ℕ) (G : PlaneTree → Prop) (M : ℕ∞) (n : ℕ) :
    (conditioned μ n).map (markCount (fun U => (U.vertexCount : ℕ∞) ≤ M ∧ G U)) =
      (bridgeLaw μ n).map (fun ω => cyclicSum G M (List.ofFn ω)) := by
  rw [← map_cyclicSum_conditioned]
  congr 1
  funext T
  rw [cyclicSum_dfsSeq]

/-- **Lemma `lem:RW`, untruncated count.** For `M ≥ n` (e.g. `M = ∞`), the law of the number
`#{u ∈ 𝒯^n : G(𝒯^n_u) = 1}` of marked vertices of `𝒯^n` is the law of
`∑_{i=1}^{n} I_i^{(M)}(X_1, …, X_n)` under `P(· | S_n = -1)`. -/
theorem map_markCount_conditioned_of_le (μ : PMF ℕ) (G : PlaneTree → Prop) {M : ℕ∞} {n : ℕ}
    (hM : (n : ℕ∞) ≤ M) :
    (conditioned μ n).map (markCount G) =
      (bridgeLaw μ n).map (fun ω => cyclicSum G M (List.ofFn ω)) := by
  rw [← map_cyclicSum_conditioned]
  refine Measure.map_congr ?_
  filter_upwards [ae_cond_mem (μ := bienayme μ) (s := {T : PlaneTree | T.vertexCount = n})
    MeasurableSet.of_discrete] with T hT
  rw [cyclicSum_dfsSeq_of_le G (le_of_eq_of_le (by rw [show T.vertexCount = n from hT]) hM)]

/-- The law `markedCountLaw μ G k n` of `#{u ∈ 𝒯^n : G_{k_n}(𝒯^n_u) = 1}` (`Setup/Marks.lean`)
is the law of `∑_{i=1}^{n} I_i^{(∞)}(X_1, …, X_n)` under `P(· | S_n = -1)`. -/
theorem markedCountLaw_eq (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ) (n : ℕ) :
    markedCountLaw μ G k n =
      (bridgeLaw μ n).map (fun ω => cyclicSum (G (k n)) ⊤ (List.ofFn ω)) :=
  map_markCount_conditioned_of_le μ (G (k n)) le_top

/-! ### Exchangeability of the cyclic indicators under the bridge (`B04`) -/

/-- Rotating the coordinates by one step rotates the list by one. -/
theorem ofFn_comp_finRotate {α : Type*} : ∀ {n : ℕ} (f : Fin n → α),
    List.ofFn (f ∘ finRotate n) = (List.ofFn f).rotate 1
  | 0, f => by simp
  | n + 1, f => by
    apply List.ext_getElem (by simp)
    intro j h1 h2
    rw [List.getElem_rotate, List.getElem_ofFn, List.getElem_ofFn, Function.comp_apply]
    congr 1
    ext
    rw [coe_finRotate]
    simp only [List.length_ofFn] at h1 ⊢
    split_ifs with h
    · have : j = n := by simpa [Fin.ext_iff] using h
      subst this
      simp
    · have : j ≠ n := fun hj => h (Fin.ext (by simpa using hj))
      rw [Nat.mod_eq_of_lt (by omega)]

theorem ofFn_comp_finRotate_pow {α : Type*} {n : ℕ} (f : Fin n → α) (i : ℕ) :
    List.ofFn (f ∘ ⇑(finRotate n ^ i)) = (List.ofFn f).rotate i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Equiv.Perm.coe_mul, ← Function.comp_assoc, ofFn_comp_finRotate, ih,
      List.rotate_rotate]

/-- The law of `(X_1, …, X_n)` is invariant under permutations of the coordinates. -/
theorem map_walkVecLaw_comp_perm (μ : PMF ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (walkVecLaw μ n).map (fun ω => ω ∘ σ) = walkVecLaw μ n := by
  refine Measure.ext_of_singleton fun x => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have : (fun ω : Fin n → ℤ => ω ∘ σ) ⁻¹' {x} = {x ∘ σ.symm} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      funext i
      simp
    · rintro rfl
      funext i
      simp
  rw [this, walkVecLaw_singleton, walkVecLaw_singleton]
  exact Equiv.prod_comp σ.symm (fun i => stepPMF μ (x i))

/-- The bridge law is invariant under permutations of the coordinates. -/
theorem map_bridgeLaw_comp_perm (μ : PMF ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (bridgeLaw μ n).map (fun ω => ω ∘ σ) = bridgeLaw μ n := by
  ext t ht
  rw [Measure.map_apply (measurable_of_countable _) ht, bridgeLaw, cond_apply
    (Set.to_countable _).measurableSet, cond_apply (Set.to_countable _).measurableSet]
  congr 1
  have hS : (fun ω : Fin n → ℤ => ω ∘ σ) ⁻¹' {ω | ∑ i, ω i = -1} = {ω | ∑ i, ω i = -1} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Function.comp_apply]
    rw [Equiv.sum_comp σ ω]
  conv_lhs => rw [← hS, ← Set.preimage_inter]
  rw [← Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    map_walkVecLaw_comp_perm]

/-- **`B04`, second part.** Under the bridge `P(· | S_n = -1)`, all cyclic indicators have the same
law: `P(I_{i+1}^{(M)}(X_1, …, X_n) = 1 | S_n = -1) = P(I_1^{(M)}(X_1, …, X_n) = 1 | S_n = -1)`. -/
theorem bridgeLaw_shiftIndicator_eq_one (μ : PMF ℕ) (G : PlaneTree → Prop) (M : ℕ∞) (n i : ℕ) :
    bridgeLaw μ n {ω | shiftIndicator G M (List.ofFn ω) i = 1} =
      bridgeLaw μ n {ω | firstIndicator G M (List.ofFn ω) = 1} := by
  have h : {ω : Fin n → ℤ | shiftIndicator G M (List.ofFn ω) i = 1} =
      (fun ω => ω ∘ ⇑(finRotate n ^ i)) ⁻¹' {ω | firstIndicator G M (List.ofFn ω) = 1} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, shiftIndicator, ofFn_comp_finRotate_pow]
  rw [h, ← Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    map_bridgeLaw_comp_perm]

/-- Consequently `E[∑_{i=1}^n I_i^{(M)}(X_1, …, X_n) | S_n = -1] = n P(I_1^{(M)} = 1 | S_n = -1)`.
-/
theorem lintegral_cyclicSum_bridgeLaw (μ : PMF ℕ) (G : PlaneTree → Prop) (M : ℕ∞) (n : ℕ) :
    ∫⁻ ω, (cyclicSum G M (List.ofFn ω) : ℝ≥0∞) ∂bridgeLaw μ n =
      n * bridgeLaw μ n {ω | firstIndicator G M (List.ofFn ω) = 1} := by
  have hind : ∀ (i : ℕ) (ω : Fin n → ℤ), (shiftIndicator G M (List.ofFn ω) i : ℝ≥0∞) =
      {ω : Fin n → ℤ | shiftIndicator G M (List.ofFn ω) i = 1}.indicator 1 ω := by
    intro i ω
    rcases shiftIndicator_eq_zero_or_eq_one G M (List.ofFn ω) i with h | h
    · rw [h, Set.indicator_of_notMem (by simp [h]), Nat.cast_zero]
    · rw [h, Set.indicator_of_mem (by simp [h]), Nat.cast_one, Pi.one_apply]
  simp only [cyclicSum, List.length_ofFn, Nat.cast_sum, hind]
  rw [lintegral_finsetSum _ (fun _ _ => measurable_of_countable _)]
  simp only [lintegral_indicator_one (Set.to_countable _).measurableSet,
    bridgeLaw_shiftIndicator_eq_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end PoissonDeclumping.Cyclic
