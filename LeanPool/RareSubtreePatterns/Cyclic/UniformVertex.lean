/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Cyclic.RandomWalk

import Mathlib.Data.List.GetD

/-!
# Corollary `cor:cyclicshift`: the fringe subtree at a uniform vertex

Source lines 777–825 (Corollary 2.3 and its proof), 227–229 (`U01`, first part) and 914–920,
960–969 (`U05`).

Let `U_n` be a uniform vertex of `𝒯^n`, independent of `𝒯^n`; the law of `𝒯^n_{U_n}` is
`uniformFringeLaw μ n` (`Setup/Marks.lean`). We prove, following the paper's proof:

* `Cyclic.bridgeLaw_ofSeq_mem` (first step of the proof): the tree `T(X_1, …, X_n)` encoded by
  the bridge `(X_1, …, X_n)` under `P(· | S_n = -1)` has the law of `𝒯^n_{U_n}`; in indicator
  form `P(G(𝒯^n_{U_n}) = 1, |𝒯^n_{U_n}| ≤ M) = P(I_1^{(M)}(X_1, …, X_n) = 1 | S_n = -1)`
  (`Cyclic.uniformFringeLaw_truncated_eq_bridgeLaw`), and for `M = n` the paper's
  `P(G(𝒯^n_{U_n}) = 1) = P(I_1^{(n)} = 1 | S_n = -1)` (`Cyclic.uniformFringeLaw_eq_bridgeLaw`);
* `Cyclic.walkVecLaw_bridge_inter_ofSeq` (Markov property at `ζ`, `P01`):
  `P(T(𝐗) ∈ s, S_n = -1) = E[1_{𝒯 ∈ s} Ψ_{n-|𝒯|}(0)]` (the remainder endpoint is `0`), and the
  paper's form `∑_{m ≥ 1} P(𝒯 ∈ s, |𝒯| = m) Ψ_{n-m}(0)`
    (`Cyclic.walkVecLaw_bridge_inter_ofSeq_eq_tsum`);
* **Corollary `cor:cyclicshift`** in `ℝ≥0∞` (`Cyclic.uniformFringeLaw_eq`) and in `ℝ` exactly as
  stated (`Cyclic.uniformFringeLaw_real_eq`):
  `P(G(𝒯^n_{U_n}) = 1) = Ψ_n(-1)⁻¹ E[1_{G(𝒯) = 1} Ψ_{n-|𝒯|}(0)]`, with `Ψ_m = 0` for `m < 0`
  built into `walkProb`; and the truncated version (`Cyclic.uniformFringeLaw_real_truncated`);
* `U01`, first part: `E[#{u ∈ 𝒯^n : G(𝒯^n_u) = 1}] = n P(G(𝒯^n_{U_n}) = 1)`
  (`Cyclic.lintegral_markCount_conditioned`, `Cyclic.integral_markCount_conditioned`);
* `U05`: if the mark `G_{k_n}` forces the size `k_n`, then `A_n(ℓ) = 0` for every `ℓ ≥ 1`
  (`Cyclic.pairProb_eq_zero_of_forces_size`).

All identities hold for every `n`. The paper restricts to admissible `n`; at an inadmissible `n`
both sides vanish (`𝒯^n` is then the zero measure, `Ψ_n(-1) = 0`, and `0⁻¹ = 0` in `ℝ`). The
expectation `E` is the integral against `PlaneTree.bienayme μ`; no criticality is needed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PoissonDeclumping.Cyclic

open Lukasiewicz PlaneTree

/-! ### The law of `𝒯^n_{U_n}` -/

/-- The uniform law on `{0, …, n-1} ⊆ ℕ` is the image of the uniform law on `Fin n`. -/
theorem uniformOn_Iio_eq_map (n : ℕ) :
    (uniformOn (Set.Iio n) : Measure ℕ) = (uniformIndex n).map Fin.val := by
  classical
  refine Measure.ext_of_singleton fun i => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    ← Finset.coe_range, ← Finset.coe_singleton, uniformOn_apply_finset]
  by_cases hi : i < n
  · have hpre : (Fin.val ⁻¹' ({i} : Set ℕ) : Set (Fin n)) = {⟨i, hi⟩} := by
      ext j
      simp [Fin.ext_iff]
    rw [Finset.coe_singleton, hpre, uniformIndex_singleton, Finset.inter_singleton_of_mem
      (Finset.mem_range.mpr hi), Finset.card_singleton, Finset.card_range, Nat.cast_one, one_div]
  · have hpre : (Fin.val ⁻¹' ({i} : Set ℕ) : Set (Fin n)) = ∅ := by
      ext j
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hi (h ▸ j.2)
    rw [Finset.coe_singleton, hpre, measure_empty, Finset.inter_singleton_of_notMem
      (by simpa using hi), Finset.card_empty, Nat.cast_zero, ENNReal.zero_div]

/-- The law of `𝒯^n_{U_n}` is the image of `𝒯^n ⊗ Unif(Fin n)` under `(T, i) ↦ T_{u_i}`. -/
theorem uniformFringeLaw_eq_map (μ : PMF ℕ) (n : ℕ) :
    uniformFringeLaw μ n = ((conditioned μ n).prod (uniformIndex n)).map
      (fun p : PlaneTree × Fin n => p.1.fringeTrees.getD p.2 p.1) := by
  have hprod : (conditioned μ n).prod ((uniformIndex n).map Fin.val) =
      ((conditioned μ n).prod (uniformIndex n)).map (Prod.map id Fin.val) := by
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_of_countable _), Measure.map_id]
  rw [uniformFringeLaw, uniformOn_Iio_eq_map, hprod,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

/-- At an admissible size, the law of `𝒯^n_{U_n}` is a probability measure. -/
theorem isProbabilityMeasure_uniformFringeLaw {μ : PMF ℕ} {n : ℕ} (h : Admissible μ n) :
    IsProbabilityMeasure (uniformFringeLaw μ n) := by
  have := conditioned_isProbabilityMeasure h
  have hn : n ≠ 0 := fun h0 => not_admissible_zero μ (h0 ▸ h)
  have : IsProbabilityMeasure (uniformOn (Set.Iio n) : Measure ℕ) :=
    isProbabilityMeasure_uniformOn (Set.finite_Iio n) ⟨0, Nat.pos_of_ne_zero hn⟩
  rw [uniformFringeLaw]
  infer_instance

/-- **First step of the proof of `cor:cyclicshift`.** The tree `T(X_1, …, X_n)` encoded by the
first excursion of `(X_1, …, X_n)` under `P(· | S_n = -1)` has the law of `𝒯^n_{U_n}`. -/
theorem bridgeLaw_ofSeq_mem (μ : PMF ℕ) (n : ℕ) (s : Set PlaneTree) :
    bridgeLaw μ n {ω | ∃ T ∈ s, ofSeq (List.ofFn ω) = some T} = uniformFringeLaw μ n s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [bridgeLaw_eq_zero_of_not_admissible μ (not_admissible_zero μ), uniformFringeLaw,
      conditioned_eq_zero_of_not_admissible (not_admissible_zero μ), Measure.zero_prod,
      Measure.map_zero, Measure.coe_zero, Pi.zero_apply, Measure.coe_zero, Pi.zero_apply]
  rw [← map_shift_conditioned μ hn.ne', uniformFringeLaw_eq_map,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    Measure.map_apply (measurable_of_countable _) MeasurableSet.of_discrete]
  refine measure_congr (Filter.eventuallyEqSet_iff.mpr ?_)
  filter_upwards [ae_vertexCount_prod μ n] with p hp
  have hi : (p.2 : ℕ) < p.1.vertexCount := by rw [hp]; exact p.2.2
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [ofFn_toVec (by rw [List.length_rotate, length_dfsSeq, hp]), ofSeq_rotate_dfsSeq _ _ hi,
    List.getD_eq_getElem _ _ (lt_length_fringeTrees hi)]
  simp

/-- **`P(G(𝒯^n_{U_n}) = 1, |𝒯^n_{U_n}| ≤ M) = P(I_1^{(M)}(X_1, …, X_n) = 1 | S_n = -1)`.** -/
theorem uniformFringeLaw_truncated_eq_bridgeLaw (μ : PMF ℕ) (n : ℕ) (G : PlaneTree → Prop)
    (M : ℕ∞) :
    uniformFringeLaw μ n {T | (T.vertexCount : ℕ∞) ≤ M ∧ G T} =
      bridgeLaw μ n {ω | firstIndicator G M (List.ofFn ω) = 1} := by
  rw [← bridgeLaw_ofSeq_mem]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, firstIndicator_eq_one_iff, firstMarked_iff]
  constructor
  · rintro ⟨T, hT, h⟩
    exact ⟨T, h, hT⟩
  · rintro ⟨T, h, hT⟩
    exact ⟨T, hT, h⟩

/-- The fringe subtree at a uniform vertex of `𝒯^n` has at most `n` vertices almost surely. -/
theorem uniformFringeLaw_vertexCount_gt (μ : PMF ℕ) (n : ℕ) :
    uniformFringeLaw μ n {T | n < T.vertexCount} = 0 := by
  rw [← bridgeLaw_ofSeq_mem]
  refine measure_mono_null (fun ω hω => ?_) (measure_empty (μ := bridgeLaw μ n))
  obtain ⟨T, hT, hω⟩ := hω
  have hz := (zeta_eq_some_iff.mp (zeta_eq_of_ofSeq_eq_some hω)).2.1
  rw [List.length_ofFn] at hz
  exact absurd hT (not_lt.mpr hz)

/-- **First display of the proof of `cor:cyclicshift`:**
`P(G(𝒯^n_{U_n}) = 1) = P(I_1^{(n)}(X_1, …, X_n) = 1 | S_n = -1)`. -/
theorem uniformFringeLaw_eq_bridgeLaw (μ : PMF ℕ) (n : ℕ) (G : PlaneTree → Prop) :
    uniformFringeLaw μ n {T | G T} =
      bridgeLaw μ n {ω | firstIndicator G n (List.ofFn ω) = 1} := by
  rw [← uniformFringeLaw_truncated_eq_bridgeLaw]
  have h : {T : PlaneTree | (T.vertexCount : ℕ∞) ≤ n ∧ G T} =
      {T | G T} ∩ {T | n < T.vertexCount}ᶜ := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt, Nat.cast_le]
    exact and_comm
  rw [h, measure_inter_conull (by rw [compl_compl]; exact uniformFringeLaw_vertexCount_gt μ n)]

/-! ### The Markov property at `ζ` on the bridge (`P01`) -/

/-- `∫⁻ 1_{𝒯 ∈ s} g(|𝒯|) dP_μ = ∑_m P_μ(𝒯 ∈ s, |𝒯| = m) g(m)`. -/
theorem lintegral_indicator_vertexCount (μ : PMF ℕ) (s : Set PlaneTree) (g : ℕ → ℝ≥0∞) :
    ∫⁻ T, s.indicator (fun T => g T.vertexCount) T ∂bienayme μ =
      ∑' m : ℕ, bienayme μ (s ∩ {T | T.vertexCount = m}) * g m := by
  rw [lintegral_indicator MeasurableSet.of_discrete,
    ← lintegral_map (measurable_of_countable g) (measurable_of_countable _),
    lintegral_countable']
  refine tsum_congr fun m => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.restrict_apply MeasurableSet.of_discrete, mul_comm, Set.inter_comm]
  rfl

/-- **Markov property at `ζ` (`P01`).** `P(T(X_1, …, X_n) ∈ s, S_n = -1) = E[1_{𝒯 ∈ s}
  Ψ_{n-|𝒯|}(0)]`,
with `Ψ_{n-m}(0) = 0` for `m > n`: after the first excursion (ending at level `-1` at time `ζ`),
the walk must return from `-1` to `-1`, i.e. make a fresh walk of length `n - ζ` ending at `0`. -/
theorem walkVecLaw_bridge_inter_ofSeq (μ : PMF ℕ) (n : ℕ) (s : Set PlaneTree) :
    walkVecLaw μ n ({ω | ∑ i, ω i = -1} ∩ {ω | ∃ T ∈ s, ofSeq (List.ofFn ω) = some T}) =
      ∫⁻ T, s.indicator
        (fun T => if T.vertexCount ≤ n then walkLaw μ (n - T.vertexCount) {0} else 0) T
          ∂bienayme μ := by
  classical
  set A : Set (List ℤ) := {x | x ∈ bridgeSet n ∧ ∃ T ∈ s, ofSeq x = some T}
  have hA : ∀ x ∈ A, x.length = n ∧ ∀ a ∈ x, -1 ≤ a := fun x hx => bridgeSet_admissible n x hx.1
  have hAB : ∀ ω : Fin n → ℤ, List.ofFn ω ∈ A ↔
      ω ∈ {ω : Fin n → ℤ | ∑ i, ω i = -1} ∩ {ω | ∃ T ∈ s, ofSeq (List.ofFn ω) = some T} ∧
        ∀ i, -1 ≤ ω i := by
    intro ω
    change (List.ofFn ω ∈ bridgeSet n ∧ _) ↔ _
    rw [ofFn_mem_bridgeSet_iff]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  rw [walkVecLaw_eq_tsum μ hA hAB, lintegral_countable']
  have h1 : ∑' x : A, walkWeight μ x.1 = ∑' x : bridgeSet n,
      walkWeight μ x.1 * (ofSeq x.1).elim 0 (s.indicator 1) := by
    rw [tsum_subtype A (walkWeight μ), tsum_subtype (bridgeSet n)
      (fun x => walkWeight μ x * (ofSeq x).elim 0 (s.indicator 1))]
    refine tsum_congr fun x => ?_
    by_cases hx : x ∈ bridgeSet n
    · rw [Set.indicator_of_mem hx]
      cases hT : ofSeq x with
      | none =>
        have : x ∉ A := fun h => by obtain ⟨-, T, -, hT'⟩ := h; simp [hT] at hT'
        simp [Set.indicator_of_notMem this]
      | some T =>
        by_cases hTs : T ∈ s
        · have : x ∈ A := ⟨hx, T, hTs, hT⟩
          simp [Set.indicator_of_mem this, Set.indicator_of_mem hTs]
        · have : x ∉ A := fun h => by
            obtain ⟨-, U, hU, hU'⟩ := h
            rw [hT, Option.some.injEq] at hU'
            exact hTs (hU' ▸ hU)
          simp [Set.indicator_of_notMem this, Set.indicator_of_notMem hTs]
    · have : x ∉ A := fun h => hx h.1
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]
  rw [h1, tsum_bridge_mul_ofSeq]
  refine tsum_congr fun T => ?_
  rw [bienayme_apply_singleton]
  by_cases hTs : T ∈ s
  · rw [Set.indicator_of_mem hTs, Set.indicator_of_mem hTs]
    split_ifs
    · rw [walkLaw_singleton_eq_walkMass, Pi.one_apply, mul_one, mul_comm]
    · rw [zero_mul]
  · rw [Set.indicator_of_notMem hTs, Set.indicator_of_notMem hTs, zero_mul]
    split_ifs <;> simp

/-- **Markov property at `ζ`, the paper's form:**
`P(T(𝐗) ∈ s, S_n = -1) = ∑_{m ≥ 1} P(𝒯 ∈ s, |𝒯| = m) Ψ_{n-m}(0)`, with `Ψ_{n-m}(0) = 0` for
`m > n` (and the `m = 0` term vanishes since no tree has `0` vertices). -/
theorem walkVecLaw_bridge_inter_ofSeq_eq_tsum (μ : PMF ℕ) (n : ℕ) (s : Set PlaneTree) :
    walkVecLaw μ n ({ω | ∑ i, ω i = -1} ∩ {ω | ∃ T ∈ s, ofSeq (List.ofFn ω) = some T}) =
      ∑' m : ℕ, bienayme μ (s ∩ {T | T.vertexCount = m}) *
        (if m ≤ n then walkLaw μ (n - m) {0} else 0) := by
  rw [walkVecLaw_bridge_inter_ofSeq, ← lintegral_indicator_vertexCount μ s
    (fun m => if m ≤ n then walkLaw μ (n - m) {0} else 0)]

/-! ### Corollary `cor:cyclicshift` -/

/-- **Corollary `cor:cyclicshift`** in `ℝ≥0∞`:
`P(G(𝒯^n_{U_n}) = 1) = Ψ_n(-1)⁻¹ E[1_{G(𝒯) = 1} Ψ_{n-|𝒯|}(0)]`, where `Ψ_n(-1) = P(S_n = -1)`
and `Ψ_{n-m}(0) = P(S_{n-m} = 0)` for `m ≤ n`, `0` for `m > n`. -/
theorem uniformFringeLaw_eq (μ : PMF ℕ) (n : ℕ) (G : PlaneTree → Prop) :
    uniformFringeLaw μ n {T | G T} =
      (walkLaw μ n {-1})⁻¹ * ∫⁻ T, {T | G T}.indicator
        (fun T => if T.vertexCount ≤ n then walkLaw μ (n - T.vertexCount) {0} else 0) T
          ∂bienayme μ := by
  rw [← bridgeLaw_ofSeq_mem, bridgeLaw, cond_apply (Set.to_countable _).measurableSet,
    walkVecLaw_bridge_inter_ofSeq, walkLaw_singleton]

/-- **Corollary `cor:cyclicshift`**, exactly as stated, in `ℝ`:
`P(G(𝒯^n_{U_n}) = 1) = (1 / Ψ_n(-1)) E[1_{G(𝒯) = 1} Ψ_{n-|𝒯|}(0)]`, with `U_n` a uniform vertex of
`𝒯^n` independent of `𝒯^n`, `𝒯` a `μ`-Bienaymé tree, `Ψ_m(i) = P(S_m = i)` and `Ψ_m(i) = 0` for
`m < 0`. -/
theorem uniformFringeLaw_real_eq (μ : PMF ℕ) (n : ℕ) (G : PlaneTree → Prop) :
    (uniformFringeLaw μ n).real {T | G T} =
      (walkProb μ n (-1))⁻¹ *
        ∫ T, {T | G T}.indicator (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T
          ∂bienayme μ := by
  set F : PlaneTree → ℝ≥0∞ := {T | G T}.indicator
    (fun T => if T.vertexCount ≤ n then walkLaw μ (n - T.vertexCount) {0} else 0) with hF
  have hint : ∫ T, {T | G T}.indicator (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T
      ∂bienayme μ = (∫⁻ T, F T ∂bienayme μ).toReal := by
    rw [← integral_toReal (Measurable.of_discrete.aemeasurable) (Filter.Eventually.of_forall
      fun T => ?_)]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun T => ?_)
      simp only [hF]
      by_cases hT : T ∈ {T : PlaneTree | G T}
      · rw [Set.indicator_of_mem hT, Set.indicator_of_mem hT, walkProb_natCast_sub]
      · rw [Set.indicator_of_notMem hT, Set.indicator_of_notMem hT, ENNReal.toReal_zero]
    · simp only [hF]
      by_cases hT : T ∈ {T : PlaneTree | G T}
      · rw [Set.indicator_of_mem hT]
        split_ifs
        · exact measure_lt_top _ _
        · exact ENNReal.zero_lt_top
      · rw [Set.indicator_of_notMem hT]
        exact ENNReal.zero_lt_top
  rw [hint, walkProb_natCast_eq_toReal, ← ENNReal.toReal_inv, ← ENNReal.toReal_mul,
    ← uniformFringeLaw_eq, measureReal_def]

/-- **Corollary `cor:cyclicshift`, truncated version:**
`P(G(𝒯^n_{U_n}) = 1, |𝒯^n_{U_n}| ≤ M) = P(I_1^{(M)}(X_1, …, X_n) = 1 | S_n = -1)
= (1 / Ψ_n(-1)) E[1_{G(𝒯) = 1, |𝒯| ≤ M} Ψ_{n-|𝒯|}(0)]`. -/
theorem uniformFringeLaw_real_truncated (μ : PMF ℕ) (n : ℕ) (G : PlaneTree → Prop) (M : ℕ∞) :
    (bridgeLaw μ n).real {ω | firstIndicator G M (List.ofFn ω) = 1} =
        (uniformFringeLaw μ n).real {T | (T.vertexCount : ℕ∞) ≤ M ∧ G T} ∧
      (uniformFringeLaw μ n).real {T | (T.vertexCount : ℕ∞) ≤ M ∧ G T} =
        (walkProb μ n (-1))⁻¹ *
          ∫ T, {T | (T.vertexCount : ℕ∞) ≤ M ∧ G T}.indicator
            (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T ∂bienayme μ :=
  ⟨by rw [measureReal_def, measureReal_def, uniformFringeLaw_truncated_eq_bridgeLaw],
    uniformFringeLaw_real_eq μ n _⟩

/-- **Corollary `cor:cyclicshift`, bridge form:**
`P(G(𝒯^n_{U_n}) = 1) = P(I_1^{(n)}(X_1, …, X_n) = 1 | S_n = -1)`, in `ℝ`. -/
theorem uniformFringeLaw_real_eq_bridgeLaw (μ : PMF ℕ) (n : ℕ) (G : PlaneTree → Prop) :
    (uniformFringeLaw μ n).real {T | G T} =
      (bridgeLaw μ n).real {ω | firstIndicator G n (List.ofFn ω) = 1} := by
  rw [measureReal_def, measureReal_def, uniformFringeLaw_eq_bridgeLaw]

/-! ### `U01`, first part: expected count and uniform vertex -/

/-- `markCount G T` as the number of DFS indices `i < |T|` whose fringe tree is marked. -/
theorem markCount_eq_card (G : PlaneTree → Prop) (T : PlaneTree) [DecidablePred G] :
    markCount G T = (Finset.univ.filter fun i : Fin T.vertexCount =>
      G (T.fringeTrees.getD i T)).card := by
  classical
  rw [Finset.card_filter, Finset.sum_fin_eq_sum_range]
  unfold markCount
  rw [countP_eq_sum_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < T.fringeTrees.length := Finset.mem_range.mp hi
  have hi'' : i < T.vertexCount := hi'
  simp only [hi', ↓reduceDIte, List.getD_eq_getElem _ _ hi']
  simp [hi'']

/-- **`U01`, first part (source lines 227–229).** `E[#{u ∈ 𝒯^n : G(𝒯^n_u) = 1}] =
n P(G(𝒯^n_{U_n}) = 1)`, in `ℝ≥0∞`. -/
theorem lintegral_markCount_conditioned (μ : PMF ℕ) (n : ℕ) (G : PlaneTree → Prop) :
    ∫⁻ T, (markCount G T : ℝ≥0∞) ∂conditioned μ n = n * uniformFringeLaw μ n {T | G T} := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [conditioned_eq_zero_of_not_admissible (not_admissible_zero μ), lintegral_zero_measure,
      Nat.cast_zero, zero_mul]
  rw [uniformFringeLaw_eq_map, Measure.map_apply (measurable_of_countable _)
    MeasurableSet.of_discrete, Measure.prod_apply MeasurableSet.of_discrete,
    ← lintegral_const_mul _ (measurable_of_countable _)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_cond_mem (μ := bienayme μ) (s := {T : PlaneTree | T.vertexCount = n})
    MeasurableSet.of_discrete] with T hT
  change T.vertexCount = n at hT
  subst hT
  rw [uniformIndex, Measure.uniformOfFinset_apply, markCount_eq_card, Finset.card_univ,
    Fintype.card_fin]
  rw [ENNReal.mul_div_cancel (by simpa using hn.ne') (ENNReal.natCast_ne_top _)]
  rfl

/-- **`U01`, first part, in `ℝ`:** `E[#{u ∈ 𝒯^n : G(𝒯^n_u) = 1}] = n P(G(𝒯^n_{U_n}) = 1)`. -/
theorem integral_markCount_conditioned (μ : PMF ℕ) (n : ℕ) (G : PlaneTree → Prop) :
    ∫ T, (markCount G T : ℝ) ∂conditioned μ n = n * (uniformFringeLaw μ n).real {T | G T} := by
  have h := congrArg ENNReal.toReal (lintegral_markCount_conditioned μ n G)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← measureReal_def] at h
  rw [← h, ← integral_toReal Measurable.of_discrete.aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.natCast_lt_top _)]
  simp only [ENNReal.toReal_natCast]

/-! ### `U05`: marks forcing the size exclude nested pairs -/

/-- **`U05`.** If the mark `G_{k_n}` forces the size `k_n` (`G_{k_n}(τ) = 1 ⇒ |τ| = k_n`), then
`A_n(ℓ) = 0` for every `ℓ ≥ 1`: a fringe subtree cannot contain a proper fringe subtree of the
same size. -/
theorem pairProb_eq_zero_of_forces_size (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ)
    (n : ℕ) (hG : ∀ τ, G (k n) τ → τ.vertexCount = k n) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    pairProb μ G k n ℓ = 0 := by
  have h : {T : PlaneTree | ℓ + 1 ≤ T.vertexCount ∧ G (k n) T ∧
      ∃ U ∈ T.fringeTrees[ℓ]?, G (k n) U} = ∅ := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, hT, U, hU, hGU⟩
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hU
    exact not_forced_size_nested hG hG T hlt hℓ ⟨hT, hGU⟩
  rw [pairProb, h, measureReal_empty]

end PoissonDeclumping.Cyclic
