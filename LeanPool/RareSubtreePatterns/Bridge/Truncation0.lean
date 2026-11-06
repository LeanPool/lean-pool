/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bridge.WalkCalculus
public import LeanPool.RareSubtreePatterns.Probability.PoissonTV

/-!
# The probabilities `q` and `p`, the truncation coupling, and the strong Markov property at `ζ`

Work package WP4 (remainder) of the bridge plan (no toolkit). Source lines 1683–1696 (`q_n`,
proof of Lemma `lem:truncate`), 1720–1728 (cyclic invariance of `q_n`), 1736–1760 (`p_n`, proof
of Lemma `lem:pnqn`(i)), 1781 (uniform-vertex representation of `q_n`).

The indicators are those of `Cyclic/Indicators.lean`: `FirstMarked G M 𝐱` is `I_1^{(M)}(𝐱) = 1`,
`(List.ofFn ω).rotate i` is the `i`-th cyclic shift, `cyclicSum G M (List.ofFn ω)` is
`W_n^M = ∑_{i ≤ n} I_i^{(M)}(X_1, …, X_n)`. For the paper's quantities take `G = G_{k_n}` and
`M = M_n`.

## Main statements

* `qProb μ G M n = P(I_1^{(M)}(X_1..X_n) = 1 | S_n = -1)` and
  `pProb μ G M = P(I_1^{(M)}(X_1..X_M) = 1)`.
* `qProb_eq_uniformFringeLaw`: `q = P(G(𝒯^n_{U_n}) = 1, |𝒯^n_{U_n}| ≤ M)`;
  `bridgeLaw_real_firstMarked_rotate`, `bridgeLaw_real_shiftIndicator_eq_one`: every cyclic
  indicator has bridge probability `q`; `firstMarked_rotate_iff_drop`: non-cyclic form.
* `P09`: `cyclicSum_le_cyclicSum_length` (`W_n^M ≤ W_n^n`), `integral_cyclicSum_sub_truncated`
  (`E[W_n^n - W_n^M | S_n = -1] = n P(G(𝒯^n_{U_n}) = 1, |𝒯^n_{U_n}| > M)`) and the coupling bound
  `paperTVDist_cyclicSum_truncated_le`.
* Strong Markov property at `ζ`: `walkVecLaw_zeta_eq_inter_drop` (fresh increments after
  `ζ = j`), `pProb_eq` (`p = P(G(𝒯) = 1, |𝒯| ≤ M)`), `walkVecLaw_firstMarked_eq_pProb`,
  `pProb_le`, and the endpoint bound `walkVecLaw_firstMarked_abs_sum_gt_le`:
  `P(I_1^{(M)} = 1, |S_M| > r) ≤ ∑_{j=1}^{M} P(G(𝒯) = 1, |𝒯| = j) P(|S_{M-j}| > r - 1)`.

All statements hold for every `n` (at inadmissible `n` the bridge law is `0`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PoissonDeclumping.Bridge

open Lukasiewicz PlaneTree Cyclic

/-! ### The probabilities `q_n` and `p_n` -/

/-- `q = P(I_1^{(M)}(X_1, …, X_n) = 1 | S_n = -1)` (source lines 1683, 1724; with `M = M_n` and
`G = G_{k_n}` this is the paper's `q_n`). -/
noncomputable def qProb (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) : ℝ :=
  (bridgeLaw μ n).real {ω | FirstMarked G M (List.ofFn ω)}

/-- `p = P(I_1^{(M)}(X_1, …, X_M) = 1)` (source line 1736; the paper's `p_n` for `M = M_n`). By
locality of `I_1^{(M)}` it is also `P(I_1^{(M)}(X_1, …, X_n) = 1)` for every `n ≥ M`
(`walkVecLaw_firstMarked_eq_pProb`). -/
noncomputable def pProb (μ : PMF ℕ) (G : PlaneTree → Prop) (M : ℕ) : ℝ :=
  (walkVecLaw μ M).real {ω | FirstMarked G M (List.ofFn ω)}

instance instIsZeroOrProbabilityMeasureBridgeLaw (μ : PMF ℕ) (n : ℕ) :
    IsZeroOrProbabilityMeasure (bridgeLaw μ n) := by
  unfold bridgeLaw
  infer_instance

theorem isProbabilityMeasure_bridgeLaw {μ : PMF ℕ} {n : ℕ} (h : Admissible μ n) :
    IsProbabilityMeasure (bridgeLaw μ n) := by
  have hn : n ≠ 0 := fun h0 => not_admissible_zero μ (h0 ▸ h)
  refine cond_isProbabilityMeasure ?_
  rw [walkVecLaw_sum_eq_neg_one]
  exact mul_ne_zero (by exact_mod_cast hn) h.ne'

instance instIsFiniteMeasureUniformFringeLaw (μ : PMF ℕ) (n : ℕ) :
    IsFiniteMeasure (uniformFringeLaw μ n) := by
  unfold uniformFringeLaw conditioned
  infer_instance

theorem setOf_firstIndicator_eq_one (G : PlaneTree → Prop) (M : ℕ∞) {n : ℕ} :
    {ω : Fin n → ℤ | firstIndicator G M (List.ofFn ω) = 1} =
      {ω | FirstMarked G M (List.ofFn ω)} := by
  ext ω
  exact firstIndicator_eq_one_iff

/-- **`q = P(G(𝒯^n_{U_n}) = 1, |𝒯^n_{U_n}| ≤ M)`** (source lines 1695, 1781): the uniform-vertex
representation of `q`. -/
theorem qProb_eq_uniformFringeLaw (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) :
    qProb μ G M n = (uniformFringeLaw μ n).real {T | G T ∧ T.vertexCount ≤ M} := by
  rw [qProb, ← setOf_firstIndicator_eq_one, (uniformFringeLaw_real_truncated μ n G M).1]
  congr 1
  ext T
  simp only [Set.mem_ofPred_eq, Nat.cast_le]
  exact and_comm

/-- **Cyclic invariance of `q`** (source line 1724): every cyclic indicator
`I_{i+1}^{(M)}(X_1, …, X_n)` has bridge probability `q`. -/
theorem bridgeLaw_real_firstMarked_rotate (μ : PMF ℕ) (G : PlaneTree → Prop) (M n i : ℕ) :
    (bridgeLaw μ n).real {ω | FirstMarked G M ((List.ofFn ω).rotate i)} = qProb μ G M n := by
  rw [qProb, measureReal_def, measureReal_def,
    bridgeLaw_rotate μ n i (FirstMarked G M)]

/-- The same in the `firstIndicator`/`shiftIndicator` language of `Cyclic/Indicators.lean`. -/
theorem bridgeLaw_real_shiftIndicator_eq_one (μ : PMF ℕ) (G : PlaneTree → Prop) (M n i : ℕ) :
    (bridgeLaw μ n).real {ω | shiftIndicator G M (List.ofFn ω) i = 1} = qProb μ G M n := by
  rw [← bridgeLaw_real_firstMarked_rotate μ G M n i]
  congr 1
  ext ω
  exact firstIndicator_eq_one_iff

/-- Before the wrap-around, `I_{i+1}^{(M)}` only reads `x_{i+1}, …, x_{i+M}`: if `i + M ≤ |𝐱|`, then
`I_{i+1}^{(M)}(𝐱) = I_1^{(M)}(x_{i+1}, …, x_n)` (non-cyclic form). -/
theorem firstMarked_rotate_iff_drop {G : PlaneTree → Prop} {x : List ℤ} {i M : ℕ}
    (h : i + M ≤ x.length) :
    FirstMarked G M (x.rotate i) ↔ FirstMarked G M (x.drop i) := by
  rw [← firstMarked_take_iff, take_rotate_eq_take_drop h, firstMarked_take_iff]

/-! ### The truncation coupling (`P09`, Lemma `lem:truncate`(i), source lines 1692–1693) -/

theorem cyclicSum_le_length (G : PlaneTree → Prop) (M : ℕ∞) (x : List ℤ) :
    cyclicSum G M x ≤ x.length := by
  unfold cyclicSum
  calc ∑ i ∈ Finset.range x.length, shiftIndicator G M x i
      ≤ ∑ _i ∈ Finset.range x.length, 1 :=
        Finset.sum_le_sum fun i _ => firstIndicator_le_one G M _
    _ = x.length := by simp

/-- `0 ≤ W_n^M ≤ W_n^n`: the truncated count is at most the full count, for every cutoff. -/
theorem cyclicSum_le_cyclicSum_length {n : ℕ} (G : PlaneTree → Prop) (M : ℕ∞)
    (ω : Fin n → ℤ) :
    cyclicSum G M (List.ofFn ω) ≤ cyclicSum G n (List.ofFn ω) := by
  unfold cyclicSum
  refine Finset.sum_le_sum fun i _ => ?_
  unfold shiftIndicator
  rw [firstIndicator_of_length_le (M := (n : ℕ∞)) (by simp)]
  exact firstIndicator_mono le_top

/-- `E[∑_{i ≤ n} I_i^{(M)} | S_n = -1] = n P(I_1^{(M)} = 1 | S_n = -1)`, in `ℝ`. -/
theorem integral_cyclicSum_bridgeLaw (μ : PMF ℕ) (G : PlaneTree → Prop) (M : ℕ∞) (n : ℕ) :
    ∫ ω, (cyclicSum G M (List.ofFn ω) : ℝ) ∂bridgeLaw μ n =
      n * (bridgeLaw μ n).real {ω | firstIndicator G M (List.ofFn ω) = 1} := by
  have h := congrArg ENNReal.toReal (lintegral_cyclicSum_bridgeLaw μ G M n)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← measureReal_def] at h
  rw [← h, ← integral_toReal (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.natCast_lt_top _)]
  simp only [ENNReal.toReal_natCast]

theorem integrable_cyclicSum_bridgeLaw (μ : PMF ℕ) (G : PlaneTree → Prop) (M : ℕ∞) (n : ℕ) :
    Integrable (fun ω : Fin n → ℤ => (cyclicSum G M (List.ofFn ω) : ℝ)) (bridgeLaw μ n) := by
  refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable n
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have := cyclicSum_le_length G M (List.ofFn ω)
  rw [List.length_ofFn] at this
  exact_mod_cast this

/-- **`P09`** (source lines 1692–1693):
`E[W_n^n - W_n^M | S_n = -1] = n P(G(𝒯^n_{U_n}) = 1, |𝒯^n_{U_n}| > M)`. -/
theorem integral_cyclicSum_sub_truncated (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) :
    ∫ ω, ((cyclicSum G n (List.ofFn ω) : ℝ) - cyclicSum G M (List.ofFn ω)) ∂bridgeLaw μ n =
      n * (uniformFringeLaw μ n).real {T | G T ∧ M < T.vertexCount} := by
  rw [integral_sub (integrable_cyclicSum_bridgeLaw μ G _ n)
      (integrable_cyclicSum_bridgeLaw μ G _ n), integral_cyclicSum_bridgeLaw,
    integral_cyclicSum_bridgeLaw, ← mul_sub, ← uniformFringeLaw_real_eq_bridgeLaw,
    (uniformFringeLaw_real_truncated μ n G M).1]
  congr 1
  have hU : {T : PlaneTree | G T} =
      {T | (T.vertexCount : ℕ∞) ≤ (M : ℕ∞) ∧ G T} ∪ {T | G T ∧ M < T.vertexCount} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_union, Nat.cast_le]
    constructor
    · intro hG
      rcases le_or_gt T.vertexCount M with h | h
      · exact Or.inl ⟨h, hG⟩
      · exact Or.inr ⟨hG, h⟩
    · rintro (⟨-, hG⟩ | ⟨hG, -⟩) <;> exact hG
  have hD : Disjoint {T : PlaneTree | (T.vertexCount : ℕ∞) ≤ (M : ℕ∞) ∧ G T}
      {T | G T ∧ M < T.vertexCount} := by
    refine Set.disjoint_left.mpr fun T h h' => ?_
    simp only [Set.mem_ofPred_eq, Nat.cast_le] at h h'
    omega
  rw [hU, measureReal_union hD MeasurableSet.of_discrete]
  ring

/-- **Truncation coupling** (Lemma `lem:truncate`(i), source lines 1692–1693): the laws of the
truncated count `W_n^M = ∑_i I_i^{(M)}` and of the full count `W_n^n` under `P(· | S_n = -1)` are
within `n P(G(𝒯^n_{U_n}) = 1, |𝒯^n_{U_n}| > M)` in total variation. -/
theorem paperTVDist_cyclicSum_truncated_le (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) :
    paperTVDist ((bridgeLaw μ n).map (fun ω => cyclicSum G M (List.ofFn ω)))
        ((bridgeLaw μ n).map (fun ω => cyclicSum G n (List.ofFn ω))) ≤
      n * (uniformFringeLaw μ n).real {T | G T ∧ M < T.vertexCount} := by
  by_cases h : Admissible μ n
  · have := isProbabilityMeasure_bridgeLaw h
    rw [← integral_cyclicSum_sub_truncated]
    exact paperTVDist_map_le_integral_sub _ (measurable_of_countable _)
      (measurable_of_countable _)
      (Filter.Eventually.of_forall fun ω => cyclicSum_le_cyclicSum_length G M ω)
      ((integrable_cyclicSum_bridgeLaw μ G _ n).sub (integrable_cyclicSum_bridgeLaw μ G _ n))
  · rw [Cyclic.bridgeLaw_eq_zero_of_not_admissible μ h, Measure.map_zero, Measure.map_zero,
      paperTVDist_self]
    exact mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg

/-! ### The strong Markov property at `ζ` (source lines 1753–1760) -/

/-- **Strong Markov property at `ζ`, fresh increments.** For `j ≤ n`,
`P(ζ = j, T(𝐗) ∈ A, K(X_{j+1}, …, X_n)) = P(𝒯 ∈ A, |𝒯| = j) P(K(X_1, …, X_{n-j}))`. -/
theorem walkVecLaw_zeta_eq_inter_drop (μ : PMF ℕ) {j n : ℕ} (hj : j ≤ n) (A : Set PlaneTree)
    (K : List ℤ → Prop) :
    walkVecLaw μ n {ω | zeta (List.ofFn ω) = some j ∧ (∃ T ∈ A, ofSeq (List.ofFn ω) = some T) ∧
        K ((List.ofFn ω).drop j)} =
      bienayme μ (A ∩ {T | T.vertexCount = j}) * walkVecLaw μ (n - j) {b | K (List.ofFn b)} := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left, ← walkVecLaw_zeta_eq_inter μ j k A {b | K (List.ofFn b)}]
  congr 1
  ext ω
  have hdrop : (List.ofFn ω).drop j = List.ofFn (fun i : Fin k => ω (Fin.natAdd j i)) := by
    rw [ofFn_eq_append ω, List.drop_left' List.length_ofFn]
  simp only [Set.mem_ofPred_eq, hdrop]

/-- **`p = P(G(𝒯) = 1, |𝒯| ≤ M)`** (source lines 1753–1760, last sentence of the proof of
Lemma `lem:pnqn`(i): `∑_{j ≤ M} E[I_1^{(M)} 1_{ζ = j}] = p`). -/
theorem pProb_eq (μ : PMF ℕ) (G : PlaneTree → Prop) (M : ℕ) :
    pProb μ G M = (bienayme μ).real {T | G T ∧ T.vertexCount ≤ M} := by
  rw [pProb, ← setOf_firstIndicator_eq_one, measureReal_def, measureReal_def,
    walkVecLaw_firstIndicator_eq μ G le_rfl]
  congr 2
  ext T
  simp only [Set.mem_ofPred_eq]
  exact and_comm

/-- Locality: `P(I_1^{(M)}(X_1, …, X_n) = 1) = p` for every `n ≥ M`. -/
theorem walkVecLaw_firstMarked_eq_pProb (μ : PMF ℕ) (G : PlaneTree → Prop) {M n : ℕ}
    (hM : M ≤ n) :
    (walkVecLaw μ n).real {ω | FirstMarked G M (List.ofFn ω)} = pProb μ G M := by
  rw [pProb_eq, ← setOf_firstIndicator_eq_one, measureReal_def, measureReal_def,
    walkVecLaw_firstIndicator_eq μ G hM]
  congr 2
  ext T
  simp only [Set.mem_ofPred_eq]
  exact and_comm

/-- `p ≤ π`: `P(I_1^{(M)} = 1) ≤ P(G(𝒯) = 1)`. -/
theorem pProb_le (μ : PMF ℕ) (G : PlaneTree → Prop) (M : ℕ) :
    pProb μ G M ≤ (bienayme μ).real {T | G T} := by
  rw [pProb_eq]
  exact measureReal_mono fun T hT => hT.1

/-- **Endpoint bound at `ζ`** (source lines 1753–1760): decomposing according to `ζ = j ≤ M` and
using the fresh increments after `ζ`,
`P(I_1^{(M)} = 1, |S_M| > r) ≤ ∑_{j=1}^{M} P(G(𝒯) = 1, |𝒯| = j) P(|S_{M-j}| > r - 1)`. -/
theorem walkVecLaw_firstMarked_abs_sum_gt_le (μ : PMF ℕ) (G : PlaneTree → Prop) (M : ℕ)
    (r : ℝ) :
    (walkVecLaw μ M).real {ω | FirstMarked G M (List.ofFn ω) ∧ r < |((∑ i, ω i : ℤ) : ℝ)|} ≤
      ∑ j ∈ Finset.Icc 1 M, (bienayme μ).real {T | G T ∧ T.vertexCount = j} *
        (walkLaw μ (M - j)).real {x : ℤ | r - 1 < |(x : ℝ)|} := by
  set F : ℕ → Set (Fin M → ℤ) := fun j => {ω | zeta (List.ofFn ω) = some j ∧
    (∃ T ∈ {T : PlaneTree | G T}, ofSeq (List.ofFn ω) = some T) ∧
      (fun y : List ℤ => r - 1 < |((y.sum : ℤ) : ℝ)|) ((List.ofFn ω).drop j)} with hF
  have hsub : {ω : Fin M → ℤ | FirstMarked G M (List.ofFn ω) ∧ r < |((∑ i, ω i : ℤ) : ℝ)|} ⊆
      ⋃ j ∈ Finset.Icc 1 M, F j := by
    rintro ω ⟨⟨m, hz, hmM, T, hT, hG⟩, hr⟩
    obtain ⟨h1, h2, h3, -⟩ := zeta_eq_some_iff.mp hz
    simp only [Set.mem_iUnion, Finset.mem_Icc, exists_prop]
    refine ⟨m, ⟨h1, by exact_mod_cast hmM⟩, hz, ⟨T, hG, hT⟩, ?_⟩
    have hsplit : ∑ i, ω i = ((List.ofFn ω).take m).sum + ((List.ofFn ω).drop m).sum := by
      rw [← List.sum_append, List.take_append_drop, List.sum_ofFn]
    rw [hsplit, h3] at hr
    have habs : |(((-1 : ℤ) + ((List.ofFn ω).drop m).sum : ℤ) : ℝ)| ≤
        1 + |((((List.ofFn ω).drop m).sum : ℤ) : ℝ)| := by
      push_cast
      refine (abs_add_le _ _).trans ?_
      simp
    change r - 1 < |((((List.ofFn ω).drop m).sum : ℤ) : ℝ)|
    linarith
  have hF' : ∀ j ∈ Finset.Icc 1 M, walkVecLaw μ M (F j) =
      bienayme μ ({T | G T} ∩ {T | T.vertexCount = j}) *
        walkLaw μ (M - j) {x : ℤ | r - 1 < |(x : ℝ)|} := by
    intro j hj
    have h := walkVecLaw_zeta_eq_inter_drop μ (Finset.mem_Icc.mp hj).2 {T : PlaneTree | G T}
      (fun y : List ℤ => r - 1 < |((y.sum : ℤ) : ℝ)|)
    rw [walkLaw_apply]
    refine h.trans ?_
    congr 2
    ext b
    simp only [Set.mem_ofPred_eq, List.sum_ofFn]
  have hfin : ∀ j ∈ Finset.Icc 1 M, walkVecLaw μ M (F j) ≠ ∞ := fun j _ => measure_ne_top _ _
  calc (walkVecLaw μ M).real {ω | FirstMarked G M (List.ofFn ω) ∧ r < |((∑ i, ω i : ℤ) : ℝ)|}
      ≤ (walkVecLaw μ M).real (⋃ j ∈ Finset.Icc 1 M, F j) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (∑ j ∈ Finset.Icc 1 M, walkVecLaw μ M (F j)).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hfin) (measure_biUnion_finset_le _ _)
    _ = ∑ j ∈ Finset.Icc 1 M, (bienayme μ).real {T | G T ∧ T.vertexCount = j} *
        (walkLaw μ (M - j)).real {x : ℤ | r - 1 < |(x : ℝ)|} := by
        rw [ENNReal.toReal_sum hfin]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hF' j hj, ENNReal.toReal_mul, measureReal_def, measureReal_def]
        rfl

end PoissonDeclumping.Bridge
