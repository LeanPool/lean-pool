/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bridge.ErrorTerms

import LeanPool.RareSubtreePatterns.RegularVariation.Consequences

/-!
# Endpoint smoothing: Lemma `lem:1` and Proposition `prop:b3bis` (`b_3 → 0`)

Work package WP6 of the bridge plan. Source lines 1860–1995 (Proposition 4.8, Lemma 4.9;
inventory `P12`, `B14`). Notation: `I_j^{(M)}` are the cyclic indicators of
`Bridge/ErrorTerms.lean` (`cycEvent`), `q_n = qProb`, `p_n = pProb`, `π_n = markProb`,
`Ψ_m = walkProb μ m`, `r_n = √(a_{M_n} a_n)`, and `b_3 = errorB3` is the third Chen–Stein error
term of `ChenStein.prop_AGG` for the bridge `P(· | S_n = -1)`.

* `windowCount G M K y = ∑_{j=0}^{K-M} I_1^{(M)}(y_{j+1}, …)` counts the indicators reading only
  `y_1, …, y_K`; `windowMean μ G M K N f s = E[f(1 + windowCount K) | S_N = s]`, and the paper's
  `h_n(k) = E[f(1 + ∑_{j=1}^{n-2M_n+1} I_j^{(M_n)}) | S_{n-M_n} = -1-k]` (source line 1873) is
  `endpointMean μ G M n f k = windowMean μ G M (n-M) (n-M) f (-1-k)`.

## Main statements

* `errorB3_eq_mul`, `sum_compl_cycNbhd_indicator` (cyclic exchangeability and the bookkeeping of
  the cyclic wrap, source lines 1873–1880): the indices outside `B_i` are those at forward
  distance `M, …, n - M`, and `b_3 = n |E[(I_1 - q) f(1 + ∑_{j ≤ n-2M+1} I_{M+j}) | S_n = -1]|`.
* `integral_blockIntegrand_eq` (block reduction, source lines 1880–1886): conditional
  independence of `(X_1..X_M)` and `(X_{M+1}..X_n)` given `S_M`, `S_n`, and subtraction of
  **any** constant `κ` from `h_n` (as `E[I_1 - q | S_n = -1] = 0`).
* `integral_cond_take` (Markov property at a deterministic time for bounded functions),
  `cond_walkVecLaw_real_firstMarked_drop` (exchangeability of the conditioned walk),
  `abs_windowMean_sub_le` (deletion estimate `eq:hne`), `abs_walkProb_div_sub_div_le` and
  `abs_windowMean_sub_windowMean_le` (deterministic endpoint smoothing).
* `eventually_abs_endpointMean_sub_le` (**corrected `eq:delta_vanish`**, via `eq:approx1` and
  `eq:approx3`): uniformly in `‖f‖_∞ ≤ 1` and in compatible endpoints `k, k'` with
  `|k|, |k'| ≤ r_n`, `|h_n(k) - h_n(k')| → 0`.
* `exists_eventually_mul_abs_integral_le` (the split `|S_{M_n}| ≤ r_n` / `> r_n` and the bounds
  on `R_n^1`, `R_n^2`), `eventually_lem1`, `tendsto_lem1` (**Lemma `lem:1`**, with a
  compatible base point).
* `eventually_errorB3_le` (**Proposition `prop:b3bis`**, uniform in the test function, which is
  what `exists_paperTVDist_cyclicSum_le_errorTerms` requires) and `tendsto_errorB3`.

## Departures from the source

* **Periodic laws (correction F2).** The paper's `Δ_n(k) = h_n(k) - h_n(0)` conditions on
  `S_{n-M_n} = -1`, a null event unless `d ∣ M_n` (`d` the span; admissible `n` have
  `d ∣ n - 1`). Here the base value is `h_n(k₀)` for a compatible `k₀`
  (`Ψ_{n-M_n}(-1-k₀) ≠ 0`, `|k₀| ≤ r_n`), and `eq:delta_vanish` is proved as an *oscillation*
  bound over pairs of compatible endpoints. `S_{M_n}` is compatible almost surely under the
  bridge; at incompatible endpoints the weight `Ψ_{n-M_n}(-1-S_{M_n})` vanishes.
* **No Skorokhod representation (correction F7).** `eq:approx3` is proved by the deterministic
  bound `|Ψ_t(s-y)/Ψ_N(s) - Ψ_t(s'-y)/Ψ_N(s')| ≤ (a_N/a_t)(2δ₁/L + 8Cδ₂/L²)`, uniform in `y`,
  from `LatticeLocal.equicont` at time `t = ⌊εn⌋`, `eventually_abs_mul_sub_le` at time
  `N = n - M_n` and `sup_le`; the small time fraction `ε` is chosen first, from the target.
* **Marginal tightness (F6)** replaces convergence in law of `S_{M_n}/a_{M_n}` (line 1912).
* The large-endpoint term and the small-endpoint term are bounded directly in walk form
  (Markov property at time `M_n` under the bridge) with `Ψ_{n-M_n} ≤ C/a_n`,
  `Ψ_n(-1) ≥ c/a_n`, instead of Lemma `lem:error_est`; `eq:approx1` uses Lemma `lem:error_est`
  with `N_n = n - M_n`, `z_n = 1 + r_n` and `p_n ≤ π_n` (instead of `p_n ≤ C q_n`).
* Assumption (M) is not used: Proposition `prop:b3bis` holds under bounded `n π_n` and the
  cutoff properties alone.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping.Bridge

open Lukasiewicz PlaneTree Cyclic

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

/-- The event `{I_1^{(M)}(𝐱) = 1}` on sequences. -/
def markSet (G : PlaneTree → Prop) (M : ℕ) : Set (List ℤ) := {x | FirstMarked G M x}

/-- `∑_{j=0}^{K-M} I_1^{(M)}(y_{j+1}, y_{j+2}, …)`: the indicators that read only the window
`(y_1, …, y_K)`. -/
noncomputable def windowCount (G : PlaneTree → Prop) (M K : ℕ) (y : List ℤ) : ℕ :=
  ∑ j ∈ Finset.range (K + 1 - M), (markSet G M).indicator (1 : List ℤ → ℕ) (y.drop j)

/-- `E[f(1 + ∑_{j=0}^{K-M} I_{j+1}^{(M)}) | S_N = s]`. -/
noncomputable def windowMean (μ : PMF ℕ) (G : PlaneTree → Prop) (M K N : ℕ) (f : ℕ → ℝ)
    (s : ℤ) : ℝ :=
  ∫ b, f (1 + windowCount G M K (List.ofFn b)) ∂cond (walkVecLaw μ N) {b | ∑ i, b i = s}

/-- The paper's `h_n(k) = E[f(1 + ∑_{j=1}^{n-2M+1} I_j^{(M)}) | S_{n-M} = -1-k]` (source line
1873, with `M = M_n`): the indicators of the second block `(X_{M+1}, …, X_n)`, of length
`n - M`, given its sum `-1 - k`. It is `0` at a null endpoint (`cond` of a null event). -/
noncomputable def endpointMean (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) (f : ℕ → ℝ)
    (k : ℤ) : ℝ :=
  windowMean μ G M (n - M) (n - M) f (-1 - k)

private theorem natCast_indicator_one {X : Type*} (s : Set X) (x : X) :
    ((s.indicator (1 : X → ℕ) x : ℕ) : ℝ) = s.indicator (1 : X → ℝ) x := by
  by_cases h : x ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    simp
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    simp

/-- Rewriting `1_{I_1^{(M)}(g(x)) = 1}` as the indicator of an event in `x`. -/
theorem indicator_markSet_eq {X : Type*} (G : PlaneTree → Prop) (M : ℕ) (g : X → List ℤ)
    (x : X) {R : Type*} [Zero R] [One R] :
    (markSet G M).indicator (1 : List ℤ → R) (g x) =
      {x | FirstMarked G M (g x)}.indicator (1 : X → R) x := by
  by_cases h : FirstMarked G M (g x)
  · rw [Set.indicator_of_mem (show g x ∈ markSet G M from h),
      Set.indicator_of_mem (show x ∈ {x | FirstMarked G M (g x)} from h)]
    rfl
  · rw [Set.indicator_of_notMem (show g x ∉ markSet G M from h),
      Set.indicator_of_notMem (show x ∉ {x | FirstMarked G M (g x)} from h)]

/-! ### Rotation invariance of the conditioned walk -/

/-- The law of `(X_1, …, X_N)` given `S_N = s` is invariant under permutations of the
coordinates. -/
theorem map_cond_walkVecLaw_comp_perm (μ : PMF ℕ) {N : ℕ} (s : ℤ) (σ : Equiv.Perm (Fin N)) :
    (cond (walkVecLaw μ N) {ω | ∑ i, ω i = s}).map (fun ω => ω ∘ σ) =
      cond (walkVecLaw μ N) {ω | ∑ i, ω i = s} := by
  ext t ht
  rw [Measure.map_apply (measurable_of_countable _) ht, cond_apply
    (Set.to_countable _).measurableSet, cond_apply (Set.to_countable _).measurableSet]
  congr 1
  have hS : (fun ω : Fin N → ℤ => ω ∘ σ) ⁻¹' {ω | ∑ i, ω i = s} = {ω | ∑ i, ω i = s} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Function.comp_apply]
    rw [Equiv.sum_comp σ ω]
  conv_lhs => rw [← hS, ← Set.preimage_inter]
  rw [← Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    map_walkVecLaw_comp_perm]

/-- Cyclic exchangeability of `(X_1, …, X_N)` given `S_N = s`, event form. -/
theorem cond_walkVecLaw_real_rotate (μ : PMF ℕ) (N j : ℕ) (s : ℤ) (P : List ℤ → Prop) :
    (cond (walkVecLaw μ N) {ω | ∑ i, ω i = s}).real {ω | P ((List.ofFn ω).rotate j)} =
      (cond (walkVecLaw μ N) {ω | ∑ i, ω i = s}).real {ω | P (List.ofFn ω)} := by
  have h : {ω : Fin N → ℤ | P ((List.ofFn ω).rotate j)} =
      (fun ω => ω ∘ ⇑(finRotate N ^ j)) ⁻¹' {ω | P (List.ofFn ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, ofFn_comp_finRotate_pow]
  rw [h, measureReal_def, ← Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet, map_cond_walkVecLaw_comp_perm, measureReal_def]

/-- Exchangeability of the conditioned walk for the indicators: for `j + M ≤ N`,
`P(I_{j+1}^{(M)} = 1 | S_N = s) = P(I_1^{(M)} = 1 | S_N = s)`. -/
theorem cond_walkVecLaw_real_firstMarked_drop (μ : PMF ℕ) (G : PlaneTree → Prop) {M N j : ℕ}
    (h : j + M ≤ N) (s : ℤ) :
    (cond (walkVecLaw μ N) {ω | ∑ i, ω i = s}).real
        {ω | FirstMarked G M ((List.ofFn ω).drop j)} =
      (cond (walkVecLaw μ N) {ω | ∑ i, ω i = s}).real
        {ω | FirstMarked G M ((List.ofFn ω).take M)} := by
  have h1 : {ω : Fin N → ℤ | FirstMarked G M ((List.ofFn ω).drop j)} =
      {ω | FirstMarked G M ((List.ofFn ω).rotate j)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    exact (firstMarked_rotate_iff_drop (by rw [List.length_ofFn]; exact h)).symm
  have h2 : {ω : Fin N → ℤ | FirstMarked G M ((List.ofFn ω).take M)} =
      {ω | FirstMarked G M (List.ofFn ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    exact firstMarked_take_iff
  rw [h1, h2, cond_walkVecLaw_real_rotate μ N j s (FirstMarked G M)]

/-! ### The Markov property at a deterministic time, for bounded functions -/

/-- **Markov property at the deterministic time `m`**, integral form: for a bounded `Φ` and
`m ≤ N`, `E[Φ(X_1..X_m) | S_N = s] = Ψ_N(s)⁻¹ E[Φ(X_1..X_m) Ψ_{N-m}(s - S_m)]`. -/
theorem integral_cond_take (μ : PMF ℕ) {m N : ℕ} (hmN : m ≤ N) (s : ℤ) (Φ : List ℤ → ℝ)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    ∫ ω, Φ ((List.ofFn ω).take m) ∂cond (walkVecLaw μ N) {ω | ∑ i, ω i = s} =
      (walkProb μ N s)⁻¹ * ∫ a, Φ (List.ofFn a) *
        walkProb μ ((N - m : ℕ) : ℤ) (s - ∑ i, a i) ∂walkVecLaw μ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmN
  rw [Nat.add_sub_cancel_left]
  have hS : MeasurableSet {ω : Fin (m + k) → ℤ | ∑ i, ω i = s} :=
    (Set.to_countable _).measurableSet
  rw [integral_cond_eq _ hS, walkProb_natCast μ (m + k) s]
  congr 1
  rw [integral_walkVecLaw_add μ m k _ (C := C) (abs_indicator_le_of_abs_le fun ω => hΦ _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  have hL : ∀ b : Fin k → ℤ, {ω : Fin (m + k) → ℤ | ∑ i, ω i = s}.indicator
      (fun ω => Φ ((List.ofFn ω).take m)) (Fin.append a b) =
      Φ (List.ofFn a) * {b : Fin k → ℤ | ∑ i, b i = s - ∑ i, a i}.indicator 1 b := by
    intro b
    by_cases hb : ∑ i, b i = s - ∑ i, a i
    · rw [Set.indicator_of_mem (show Fin.append a b ∈ {ω : Fin (m + k) → ℤ | ∑ i, ω i = s} by
        simp only [Set.mem_ofPred_eq, sum_append]; omega),
        Set.indicator_of_mem (show b ∈ {b : Fin k → ℤ | ∑ i, b i = s - ∑ i, a i} from hb),
        take_ofFn_append, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem (show Fin.append a b ∉ {ω : Fin (m + k) → ℤ | ∑ i, ω i = s} by
        simp only [Set.mem_ofPred_eq, sum_append]; omega),
        Set.indicator_of_notMem (show b ∉ {b : Fin k → ℤ | ∑ i, b i = s - ∑ i, a i} from hb),
        mul_zero]
  simp only [hL]
  rw [integral_const_mul, integral_indicator_one (Set.to_countable _).measurableSet,
    ← walkProb_natCast]

/-! ### The window counts -/

/-- `I_{j+1}^{(M)}` of `(y_1, …, y_K)` agrees with that of `y` when `j + M ≤ K`. -/
theorem mem_markSet_drop_take_iff {G : PlaneTree → Prop} {M K j : ℕ} {y : List ℤ}
    (h : j + M ≤ K) : (y.take K).drop j ∈ markSet G M ↔ y.drop j ∈ markSet G M := by
  change FirstMarked G M ((y.take K).drop j) ↔ FirstMarked G M (y.drop j)
  rw [← firstMarked_take_iff (x := (y.take K).drop j), List.drop_take, List.take_take,
    Nat.min_eq_left (by omega), firstMarked_take_iff]

/-- Locality: the window count of `(y_1, …, y_K)` only reads `y_1, …, y_K`. -/
theorem windowCount_take (G : PlaneTree → Prop) (M K : ℕ) (y : List ℤ) :
    windowCount G M K (y.take K) = windowCount G M K y := by
  unfold windowCount
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjK : j + M ≤ K := by rw [Finset.mem_range] at hj; omega
  by_cases h : y.drop j ∈ markSet G M
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((mem_markSet_drop_take_iff hjK).2 h)]
    rfl
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun h' => h ((mem_markSet_drop_take_iff hjK).1 h'))]

/-- Shrinking the window deletes the indicators `I_{j+1}`, `K' + 1 - M ≤ j < K + 1 - M`. -/
theorem windowCount_eq_add (G : PlaneTree → Prop) (M : ℕ) {K' K : ℕ} (h : K' ≤ K)
    (y : List ℤ) :
    windowCount G M K y = windowCount G M K' y +
      ∑ j ∈ Finset.Ico (K' + 1 - M) (K + 1 - M),
        (markSet G M).indicator (1 : List ℤ → ℕ) (y.drop j) := by
  unfold windowCount
  rw [Finset.sum_range_add_sum_Ico _ (by omega)]

private theorem abs_sub_le_two_mul {f : ℕ → ℝ} (hf : ∀ w, |f w| ≤ 1) (c d : ℕ) :
    |f (1 + (c + d)) - f (1 + c)| ≤ 2 * d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    calc |f (1 + (c + d)) - f (1 + c)| ≤ |f (1 + (c + d))| + |f (1 + c)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (hf _) (hf _)
      _ ≤ 2 * d := by linarith

private theorem integrable_of_abs_le {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsFiniteMeasure ν] {g : X → ℝ} (C : ℝ)
    (hg : ∀ x, |g x| ≤ C) : Integrable g ν :=
  Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hg x)

/-- **Deletion estimate** (source line `eq:hne`): removing the indicators `I_{j+1}`,
`K' + 1 - M ≤ j < K + 1 - M`, from the argument of `f` changes the conditional mean by at most
`2 ∑_j P(I_{j+1} = 1 | S_N = s)`. -/
theorem abs_windowMean_sub_le (μ : PMF ℕ) (G : PlaneTree → Prop) (M N : ℕ) {K' K : ℕ}
    (h : K' ≤ K) {f : ℕ → ℝ} (hf : ∀ w, |f w| ≤ 1) (s : ℤ) :
    |windowMean μ G M K N f s - windowMean μ G M K' N f s| ≤
      2 * ∑ j ∈ Finset.Ico (K' + 1 - M) (K + 1 - M),
        (cond (walkVecLaw μ N) {b | ∑ i, b i = s}).real
          {b | FirstMarked G M ((List.ofFn b).drop j)} := by
  set ν := cond (walkVecLaw μ N) {b : Fin N → ℤ | ∑ i, b i = s} with hν
  set J := Finset.Ico (K' + 1 - M) (K + 1 - M) with hJ
  unfold windowMean
  rw [← hν, ← integral_sub (integrable_of_abs_le ν 1 fun b => hf _)
    (integrable_of_abs_le ν 1 fun b => hf _)]
  set D : (Fin N → ℤ) → ℝ := fun b => 2 * ∑ j ∈ J,
    {b : Fin N → ℤ | FirstMarked G M ((List.ofFn b).drop j)}.indicator 1 b with hD
  have hDb : ∀ b, |D b| ≤ 2 * J.card := by
    intro b
    have h0 : ∀ j ∈ J, 0 ≤ {b : Fin N → ℤ | FirstMarked G M ((List.ofFn b).drop j)}.indicator
        (1 : (Fin N → ℤ) → ℝ) b := fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have h1 : ∀ j ∈ J, {b : Fin N → ℤ | FirstMarked G M ((List.ofFn b).drop j)}.indicator
        (1 : (Fin N → ℤ) → ℝ) b ≤ 1 := fun j _ => Set.indicator_le_self' (fun _ _ => zero_le_one) b
    rw [abs_of_nonneg (mul_nonneg zero_le_two (Finset.sum_nonneg h0))]
    have := Finset.sum_le_card_nsmul J _ 1 h1
    rw [nsmul_eq_mul, mul_one] at this
    linarith
  have hDint : ∫ b, D b ∂ν = 2 * ∑ j ∈ J,
      ν.real {b | FirstMarked G M ((List.ofFn b).drop j)} := by
    rw [hD, integral_const_mul, integral_finsetSum _ (fun j _ =>
      integrable_of_abs_le ν 1 fun b => by
        rw [abs_of_nonneg (indicator_one_mem_Icc _ _).1]
        exact (indicator_one_mem_Icc _ _).2)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_indicator_one (Set.to_countable _).measurableSet]
  rw [← hDint, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (integrable_of_abs_le ν _ hDb)
    (Eventually.of_forall fun b => ?_)
  rw [windowCount_eq_add G M h, Real.norm_eq_abs]
  refine (abs_sub_le_two_mul hf _ _).trans (le_of_eq ?_)
  rw [hD]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [natCast_indicator_one, indicator_markSet_eq G M (fun b : Fin N → ℤ => (List.ofFn b).drop j)]

/-! ### Endpoint smoothing at a fixed size -/

/-- The Markov property at time `K` for the window mean: for `K ≤ N`,
`E[f(1 + W_K) | S_N = s] = Ψ_N(s)⁻¹ E[f(1 + W_K) Ψ_{N-K}(s - S_K)]`. -/
theorem windowMean_eq (μ : PMF ℕ) (G : PlaneTree → Prop) (M : ℕ) {K N : ℕ} (hKN : K ≤ N)
    {f : ℕ → ℝ} (hf : ∀ w, |f w| ≤ 1) (s : ℤ) :
    windowMean μ G M K N f s = (walkProb μ N s)⁻¹ * ∫ a, f (1 + windowCount G M K (List.ofFn a)) *
      walkProb μ ((N - K : ℕ) : ℤ) (s - ∑ i, a i) ∂walkVecLaw μ K := by
  have h := integral_cond_take μ hKN s (fun y => f (1 + windowCount G M K y)) (C := 1)
    (fun y => hf _)
  simp only [windowCount_take] at h
  exact h

/-- Elementary bound for the difference of two ratios. -/
private theorem abs_div_sub_div_le {π π' β β' L δ₁ δ₂ C : ℝ} (hL : 0 < L) (hβ : L / 2 ≤ β)
    (hβ' : L / 2 ≤ β') (hββ' : |β - β'| ≤ 2 * δ₂) (hπ : |π - π'| ≤ δ₁) (hπ'0 : 0 ≤ π')
    (hπ' : π' ≤ C) : |π / β - π' / β'| ≤ 2 * δ₁ / L + 8 * C * δ₂ / L ^ 2 := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hβ'0 : 0 < β' := lt_of_lt_of_le (by positivity) hβ'
  have hδ₂ : 0 ≤ δ₂ := by linarith [abs_nonneg (β - β')]
  have hC : 0 ≤ C := hπ'0.trans hπ'
  have key : π / β - π' / β' = (π - π') / β + π' * (β' - β) / (β * β') := by
    field_simp
    ring
  rw [key]
  have h1 : |(π - π') / β| ≤ 2 * δ₁ / L := by
    rw [abs_div, abs_of_pos hβ0, div_le_div_iff₀ hβ0 hL]
    nlinarith [abs_nonneg (π - π')]
  have h2 : |π' * (β' - β) / (β * β')| ≤ 8 * C * δ₂ / L ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg hπ'0, abs_of_pos (mul_pos hβ0 hβ'0),
      div_le_div_iff₀ (mul_pos hβ0 hβ'0) (by positivity)]
    have hb : |β' - β| ≤ 2 * δ₂ := by rw [abs_sub_comm]; exact hββ'
    have hbb : L ^ 2 / 4 ≤ β * β' := by nlinarith
    calc π' * |β' - β| * L ^ 2 ≤ C * (2 * δ₂) * L ^ 2 := by gcongr
      _ = 8 * C * δ₂ * (L ^ 2 / 4) := by ring
      _ ≤ 8 * C * δ₂ * (β * β') := by gcongr
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- **The deterministic endpoint-smoothing bound** (replacing Skorokhod's representation and
dominated convergence at source lines 1987–1994, correction F7): uniformly in the position `y`,
`|Ψ_t(s - y)/Ψ_N(s) - Ψ_t(s' - y)/Ψ_N(s')| ≤ (a_N / a_t) (2δ₁/L + 8Cδ₂/L²)` when
`a_N Ψ_N(s)`, `a_N Ψ_N(s')` are `δ₂`-close to `L`, `s ≡ s' (mod d)`, `|s - s'|` is within the
equicontinuity range at time `t`, and `a_t Ψ_t ≤ C`. -/
theorem abs_walkProb_div_sub_div_le {d : ℕ} {L : ℝ} (hloc : LatticeLocal μ a d L) {t N : ℕ}
    {s s' : ℤ} {δ₁ δ₂ C η : ℝ} (hat : 0 < a t) (haN : 0 < a N)
    (hs : |a N * walkProb μ N s - L| ≤ δ₂) (hs' : |a N * walkProb μ N s' - L| ≤ δ₂)
    (hδ₂ : δ₂ ≤ L / 2) (hδ₁ : 0 ≤ δ₁) (hds : (d : ℤ) ∣ s - s')
    (heq : ∀ x y : ℤ, (d : ℤ) ∣ x + t → (d : ℤ) ∣ y + t → |((x - y : ℤ) : ℝ)| ≤ η * a t →
      |a t * walkProb μ t x - a t * walkProb μ t y| ≤ δ₁)
    (hss' : |((s - s' : ℤ) : ℝ)| ≤ η * a t) (hsup : ∀ x, walkProb μ t x ≤ C / a t) (y : ℤ) :
    |walkProb μ t (s - y) / walkProb μ N s - walkProb μ t (s' - y) / walkProb μ N s'| ≤
      a N / a t * (2 * δ₁ / L + 8 * C * δ₂ / L ^ 2) := by
  have hL := hloc.L_pos
  have hδ₂0 : 0 ≤ δ₂ := (abs_nonneg _).trans hs
  have hC : 0 ≤ C := by
    have h := (walkProb_nonneg μ t 0).trans (hsup 0)
    rw [le_div_iff₀ hat, zero_mul] at h
    exact h
  have hR : 0 ≤ a N / a t * (2 * δ₁ / L + 8 * C * δ₂ / L ^ 2) := by positivity
  by_cases hc : (d : ℤ) ∣ (s - y) + t
  · have hc' : (d : ℤ) ∣ (s' - y) + t := by
      have := Int.dvd_sub hc hds
      convert this using 1
      ring
    have hdiff := heq (s - y) (s' - y) hc hc'
      (by rw [show s - y - (s' - y) = s - s' by ring]; exact hss')
    set π := a t * walkProb μ t (s - y)
    set π' := a t * walkProb μ t (s' - y)
    set β := a N * walkProb μ N s
    set β' := a N * walkProb μ N s'
    have hβ : L / 2 ≤ β := by rw [abs_le] at hs; linarith
    have hβ' : L / 2 ≤ β' := by rw [abs_le] at hs'; linarith
    have hββ' : |β - β'| ≤ 2 * δ₂ := by
      rw [abs_le] at hs hs' ⊢
      constructor <;> linarith
    have hπ'0 : 0 ≤ π' := mul_nonneg hat.le (walkProb_nonneg μ _ _)
    have hπ' : π' ≤ C := by
      have := hsup (s' - y)
      rw [le_div_iff₀ hat] at this
      linarith
    have hb := abs_div_sub_div_le hL hβ hβ' hββ' hdiff hπ'0 hπ'
    have hP : walkProb μ t (s - y) / walkProb μ N s - walkProb μ t (s' - y) / walkProb μ N s' =
        a N / a t * (π / β - π' / β') := by
      have hψ : 0 < walkProb μ N s := by
        have : 0 < β := lt_of_lt_of_le (by positivity) hβ
        exact pos_of_mul_pos_right this haN.le
      have hψ' : 0 < walkProb μ N s' := by
        have : 0 < β' := lt_of_lt_of_le (by positivity) hβ'
        exact pos_of_mul_pos_right this haN.le
      simp only [π, π', β, β']
      field_simp
    rw [hP, abs_mul, abs_of_pos (div_pos haN hat)]
    exact mul_le_mul_of_nonneg_left hb (div_pos haN hat).le
  · have h0 : walkProb μ t (s - y) = 0 := by
      by_contra h
      exact hc (hloc.support t _ h)
    have h0' : walkProb μ t (s' - y) = 0 := by
      by_contra h
      refine hc ?_
      have := Int.dvd_add (hloc.support t _ h) hds
      convert this using 1
      ring
    rw [h0, h0', zero_div, zero_div, sub_zero, abs_zero]
    exact hR

/-- **Smoothing step** (proof of `eq:approx3`): a uniform bound on the ratio difference bounds
the difference of the window means after cutting the last `t` steps. -/
theorem abs_windowMean_sub_windowMean_le (μ : PMF ℕ) (G : PlaneTree → Prop) (M : ℕ)
    {t N : ℕ} (htN : t ≤ N) {f : ℕ → ℝ} (hf : ∀ w, |f w| ≤ 1) {s s' : ℤ} {B : ℝ}
    (hB : ∀ y : ℤ, |walkProb μ t (s - y) / walkProb μ N s -
      walkProb μ t (s' - y) / walkProb μ N s'| ≤ B) :
    |windowMean μ G M (N - t) N f s - windowMean μ G M (N - t) N f s'| ≤ B := by
  rw [windowMean_eq μ G M (Nat.sub_le N t) hf, windowMean_eq μ G M (Nat.sub_le N t) hf,
    Nat.sub_sub_self htN]
  set g : (Fin (N - t) → ℤ) → ℝ := fun a => f (1 + windowCount G M (N - t) (List.ofFn a))
  have hg : ∀ a, |g a| ≤ 1 := fun a => hf _
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hint : ∀ u : ℤ, Integrable (fun a => g a * walkProb μ t (u - ∑ i, a i))
      (walkVecLaw μ (N - t)) := fun u =>
    integrable_of_abs_le _ 1 fun a => by
      rw [abs_mul]
      have h1 : |walkProb μ t (u - ∑ i, a i)| ≤ 1 := by
        rw [abs_of_nonneg (walkProb_nonneg μ _ _)]; exact walkProb_le_one μ _ _
      exact (mul_le_mul (hg a) h1 (abs_nonneg _) zero_le_one).trans (by norm_num)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub ((hint s).const_mul _)
    ((hint s').const_mul _), ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := B) (Eventually.of_forall fun a => ?_)).trans ?_
  · rw [Real.norm_eq_abs]
    have : (walkProb μ N s)⁻¹ * (g a * walkProb μ t (s - ∑ i, a i)) -
        (walkProb μ N s')⁻¹ * (g a * walkProb μ t (s' - ∑ i, a i)) =
        g a * (walkProb μ t (s - ∑ i, a i) / walkProb μ N s -
          walkProb μ t (s' - ∑ i, a i) / walkProb μ N s') := by ring
    rw [this, abs_mul]
    calc |g a| * |walkProb μ t (s - ∑ i, a i) / walkProb μ N s -
          walkProb μ t (s' - ∑ i, a i) / walkProb μ N s'| ≤ 1 * B :=
          mul_le_mul (hg a) (hB _) (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  · rw [probReal_univ, mul_one]

/-! ### The oscillation of `h_n` over compatible endpoints -/

private theorem eventually_two_mul_le {M : ℕ → ℕ} (hM : IsCutoff M) :
    ∀ᶠ n in atTop, 2 * M n ≤ n := by
  filter_upwards [hM.isLittleO.bound (show (0 : ℝ) < 1 / 2 by norm_num)] with n hn
  rw [Real.norm_natCast, Real.norm_natCast] at hn
  have : ((2 * M n : ℕ) : ℝ) ≤ n := by push_cast; linarith
  exact_mod_cast this

private theorem tendsto_sub_cutoff {M : ℕ → ℕ} (hM : IsCutoff M) :
    Tendsto (fun n => n - M n) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_two_mul_le hM, eventually_ge_atTop (2 * b)] with n h1 h2
  omega

private theorem isLittleO_cutoff_sub {M : ℕ → ℕ} (hM : IsCutoff M) :
    (fun n => (M n : ℝ)) =o[atTop] (fun n => ((n - M n : ℕ) : ℝ)) := by
  refine hM.isLittleO.trans_isBigO (IsBigO.of_bound 2 ?_)
  filter_upwards [eventually_two_mul_le hM] with n hn
  rw [Real.norm_natCast, Real.norm_natCast]
  have : (n : ℝ) ≤ 2 * ((n - M n : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    have : (2 * M n : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact this

/-- `1 + r_n = o(a_{n - M_n})` for `r_n = √(a_{M_n} a_n)`. -/
theorem isLittleO_one_add_sqrt (hT : StableToolkit μ α a) {M : ℕ → ℕ} (hM : IsCutoff M) :
    (fun n => 1 + √(a (M n) * a n)) =o[atTop] (fun n => a (n - M n)) := by
  have hsq := hT.regularlyVarying.tendsto_sqrt_div hT.monotone hT.pos hT.rho_pos
    hM.tendsto_atTop hM.isLittleO
  have hz1 : (fun n => 1 + √(a (M n) * a n)) =o[atTop] a := by
    refine (isLittleO_iff_tendsto' ?_).2 ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn h
      exact absurd h (hT.pos n hn).ne'
    · have h1 : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hT.tendsto_atTop
      have h2 := h1.add hsq.2
      rw [add_zero] at h2
      refine h2.congr' (Eventually.of_forall fun n => ?_)
      simp only [add_div, one_div]
  obtain ⟨C, hC0, hC⟩ := hT.regularlyVarying.exists_le_mul_of_le_mul hT.monotone hT.pos
    hT.rho_pos.le 2
  refine hz1.trans_isBigO (IsBigO.of_bound C ?_)
  filter_upwards [eventually_two_mul_le hM, eventually_ge_atTop 2] with n hn hn2
  have h1 : 1 ≤ n - M n := by omega
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hT.pos n (by omega)),
    abs_of_pos (hT.pos _ h1)]
  refine hC (n - M n) n h1 ?_
  rw [Nat.cast_sub (by omega)]
  have : (2 * M n : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- **The endpoint oscillation of `h_n` vanishes** (corrected `eq:delta_vanish`, source lines
1925–1995; corrections F2, F7): uniformly over test functions `‖f‖_∞ ≤ 1` and over pairs of
*compatible* endpoints `k, k'` with `|k|, |k'| ≤ r_n = √(a_{M_n} a_n)`,
`|h_n(k) - h_n(k')| → 0` along admissible sizes. Compatibility (`Ψ_{n-M_n}(-1-k) ≠ 0`)
replaces the paper's base point `0`, which is a null endpoint unless `d ∣ M_n` (periodic case).
Only the cutoff properties and bounded `n π_n` are used. -/
theorem eventually_abs_endpointMean_sub_le (hT : StableToolkit μ α a)
    {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ} (hM : IsCutoff M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in admissibleSizes μ, ∀ f : ℕ → ℝ, (∀ w, |f w| ≤ 1) → ∀ x x' : ℤ,
      |(x : ℝ)| ≤ √(a (M n) * a n) → |(x' : ℝ)| ≤ √(a (M n) * a n) →
      walkProb μ ((n - M n : ℕ) : ℤ) (-1 - x) ≠ 0 →
      walkProb μ ((n - M n : ℕ) : ℤ) (-1 - x') ≠ 0 →
      |endpointMean μ (G (k n)) (M n) n f x - endpointMean μ (G (k n)) (M n) n f x'| ≤ ε := by
  obtain ⟨C₀, hC₀, hbr⟩ := exists_cond_take_le hT
  obtain ⟨C₂, hC₂⟩ := hbd
  obtain ⟨d, L, hloc⟩ := hT.lattice
  have hL := hloc.L_pos
  obtain ⟨Cs, hCs0, hCs⟩ := hT.exists_le_div_of_le_two_mul
  set C₂' : ℝ := max C₂ 1 with hC₂'
  have hC₂'0 : 0 < C₂' := lt_max_of_lt_right one_pos
  set e : ℝ := min (1 / 2) (ε / (12 * C₀ * C₂')) with he
  have he0 : 0 < e := lt_min (by norm_num) (by positivity)
  have he1 : e ≤ 1 / 2 := min_le_left _ _
  have he2 : e ≤ ε / (12 * C₀ * C₂') := min_le_right _ _
  obtain ⟨Ce, hCe0, hCe⟩ := hT.regularlyVarying.exists_le_mul_of_le_mul hT.monotone hT.pos
    hT.rho_pos.le (2 / e)
  set δ₁ : ℝ := ε * L / (12 * Ce) with hδ₁
  have hδ₁0 : 0 < δ₁ := by positivity
  set δ₂ : ℝ := min (L / 2) (ε * L ^ 2 / (48 * Ce * (Cs + 1))) with hδ₂
  have hδ₂0 : 0 < δ₂ := lt_min (by positivity) (by positivity)
  have hδ₂1 : δ₂ ≤ L / 2 := min_le_left _ _
  have hδ₂2 : δ₂ ≤ ε * L ^ 2 / (48 * Ce * (Cs + 1)) := min_le_right _ _
  obtain ⟨η, hη, N₁, hN₁⟩ := hloc.equicont δ₁ hδ₁0
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hsq := hT.regularlyVarying.tendsto_sqrt_div hT.monotone hT.pos hT.rho_pos
    hM.tendsto_atTop hM.isLittleO
  have hm0 : (fun _ : ℕ => ((0 : ℕ) : ℝ)) =o[atTop] (fun n => ((n - M n : ℕ) : ℝ)) := by simp
  have hen : Tendsto (fun n : ℕ => e * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop he0
  have hfl : Tendsto (fun n : ℕ => ⌊e * (n : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hen
  filter_upwards [hl (hbr (N := fun n => n - M n) (m := M)
      (z := fun n => 1 + √(a (M n) * a n)) (tendsto_sub_cutoff hM) (isLittleO_cutoff_sub hM)
      (isLittleO_one_add_sqrt hT hM)),
    hl (hT.eventually_abs_mul_sub_le hloc (N := fun n => n - M n) (m := fun _ => 0)
      (tendsto_sub_cutoff hM) hm0 (isLittleO_one_add_sqrt hT hM) hδ₂0),
    hC₂, hl (eventually_two_mul_le hM), hl (hen.eventually_ge_atTop 2),
    hl (hfl.eventually_ge_atTop N₁),
    hl (hsq.2.eventually (ge_mem_nhds (show (0 : ℝ) < η / (2 * Ce) by positivity))),
    hl (eventually_ge_atTop 1)]
    with n hbrn hloc_n hC₂n h2Mn hen2 hN₁n hrn hn1 f hf x x' hx hx' hψ hψ'
  set N := n - M n with hN
  set t := ⌊e * (n : ℝ)⌋₊ with ht
  set r := √(a (M n) * a n) with hr
  set G' := G (k n) with hG'
  have ht_low : e * n / 2 ≤ t := half_le_natFloor (by linarith)
  have ht_up : (t : ℝ) ≤ e * n := Nat.floor_le (by positivity)
  have ht1 : 1 ≤ t := by
    have : (1 : ℝ) ≤ t := by linarith
    exact_mod_cast this
  have htN : t ≤ N := by
    have h2t : ((2 * t : ℕ) : ℝ) ≤ n := by
      push_cast
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have : 2 * t ≤ n := by exact_mod_cast h2t
    omega
  have hN1 : 1 ≤ N := le_trans ht1 htN
  have hat : 0 < a t := hT.pos t ht1
  have haN : 0 < a N := hT.pos N hN1
  have han : 0 < a n := hT.pos n hn1
  have hnt : a n ≤ Ce * a t := by
    refine hCe t n ht1 ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ he0]
    linarith
  have haNn : a N ≤ a n := hT.monotone (Nat.sub_le n (M n))
  have hratio : a N / a t ≤ Ce := by
    rw [div_le_iff₀ hat]
    linarith
  -- the endpoints
  set s : ℤ := -1 - x with hs
  set s' : ℤ := -1 - x' with hs'
  have hsr : |(s : ℝ)| ≤ 1 + r := by
    rw [abs_le] at hx ⊢
    simp only [hs]
    push_cast
    constructor <;> linarith
  have hsr' : |(s' : ℝ)| ≤ 1 + r := by
    rw [abs_le] at hx' ⊢
    simp only [hs']
    push_cast
    constructor <;> linarith
  have hdN : (d : ℤ) ∣ s + N := hloc.support N s hψ
  have hdN' : (d : ℤ) ∣ s' + N := hloc.support N s' hψ'
  -- deletion of the last `t` indicators (`eq:approx1`)
  have hp : (n : ℝ) * pProb μ G' (M n) ≤ C₂' := by
    calc (n : ℝ) * pProb μ G' (M n) ≤ n * markProb μ G k n :=
          mul_le_mul_of_nonneg_left (pProb_le μ _ _) (Nat.cast_nonneg n)
      _ ≤ C₂' := hC₂n.trans (le_max_left _ _)
  have hp0 : 0 ≤ pProb μ G' (M n) := measureReal_nonneg
  have hdel : ∀ u : ℤ, |(u : ℝ)| ≤ 1 + r → walkProb μ (N : ℤ) u ≠ 0 →
      |windowMean μ G' (M n) N N f u - windowMean μ G' (M n) (N - t) N f u| ≤ ε / 6 := by
    intro u hu hψu
    refine (abs_windowMean_sub_le μ G' (M n) N (Nat.sub_le N t) hf u).trans ?_
    have hterm : ∀ j ∈ Finset.Ico (N - t + 1 - M n) (N + 1 - M n),
        (cond (walkVecLaw μ N) {b | ∑ i, b i = u}).real
          {b | FirstMarked G' (M n) ((List.ofFn b).drop j)} ≤ C₀ * pProb μ G' (M n) := by
      intro j hj
      have hjM : j + M n ≤ N := by rw [Finset.mem_Ico] at hj; omega
      rw [cond_walkVecLaw_real_firstMarked_drop μ G' hjM u]
      exact hbrn u hu hψu (FirstMarked G' (M n))
    have hcard : ((Finset.Ico (N - t + 1 - M n) (N + 1 - M n)).card : ℝ) ≤ t := by
      rw [Nat.card_Ico]
      exact_mod_cast (show N + 1 - M n - (N - t + 1 - M n) ≤ t by omega)
    calc 2 * ∑ j ∈ Finset.Ico (N - t + 1 - M n) (N + 1 - M n),
          (cond (walkVecLaw μ N) {b | ∑ i, b i = u}).real
            {b | FirstMarked G' (M n) ((List.ofFn b).drop j)}
        ≤ 2 * ∑ _j ∈ Finset.Ico (N - t + 1 - M n) (N + 1 - M n), C₀ * pProb μ G' (M n) := by
          gcongr with j hj
          exact hterm j hj
      _ = 2 * ((Finset.Ico (N - t + 1 - M n) (N + 1 - M n)).card *
            (C₀ * pProb μ G' (M n))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (t * (C₀ * pProb μ G' (M n))) := by gcongr
      _ ≤ 2 * (e * n * (C₀ * pProb μ G' (M n))) := by gcongr
      _ = 2 * e * C₀ * (n * pProb μ G' (M n)) := by ring
      _ ≤ 2 * e * C₀ * C₂' := by gcongr
      _ ≤ 2 * (ε / (12 * C₀ * C₂')) * C₀ * C₂' := by gcongr
      _ = ε / 6 := by field_simp; ring
  -- the smoothing step (`eq:approx3`)
  have hβ : ∀ u : ℤ, (d : ℤ) ∣ u + N → |(u : ℝ)| ≤ 1 + r →
      |a N * walkProb μ (N : ℤ) u - L| ≤ δ₂ := by
    intro u hdu hu
    have h := hloc_n 0 le_rfl u (by simpa using hdu) hu
    simpa using h
  have hds : (d : ℤ) ∣ s - s' := by
    have := Int.dvd_sub hdN hdN'
    convert this using 1
    ring
  have hss' : |((s - s' : ℤ) : ℝ)| ≤ η * a t := by
    have h1 : r ≤ η / (2 * Ce) * a n := by
      rw [div_le_iff₀ han] at hrn
      exact hrn
    have h2 : |((s - s' : ℤ) : ℝ)| ≤ 2 * r := by
      rw [abs_le] at hx hx' ⊢
      simp only [hs, hs']
      push_cast
      constructor <;> linarith
    have h3 : η / (2 * Ce) * a n ≤ η / (2 * Ce) * (Ce * a t) := by gcongr
    have h4 : η / (2 * Ce) * (Ce * a t) = η * a t / 2 := by field_simp
    nlinarith
  have hB := abs_walkProb_div_sub_div_le (C := Cs) (η := η) hloc hat haN (hβ s hdN hsr)
    (hβ s' hdN' hsr') hδ₂1 hδ₁0.le hds
    (fun x y hx hy hxy => hN₁ t hN₁n x y hx hy hxy) hss'
    (fun x => hCs t t ht1 ht1 (by omega) x)
  have hsm := abs_windowMean_sub_windowMean_le μ G' (M n) htN hf hB
  have hBle : a N / a t * (2 * δ₁ / L + 8 * Cs * δ₂ / L ^ 2) ≤ ε / 3 := by
    have h1 : 2 * δ₁ / L = ε / (6 * Ce) := by
      rw [hδ₁]
      field_simp
      ring
    have h2 : 8 * Cs * δ₂ / L ^ 2 ≤ ε / (6 * Ce) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : δ₂ * (48 * Ce * (Cs + 1)) ≤ ε * L ^ 2 := by
        rw [le_div_iff₀ (by positivity)] at hδ₂2
        exact hδ₂2
      nlinarith
    calc a N / a t * (2 * δ₁ / L + 8 * Cs * δ₂ / L ^ 2)
        ≤ Ce * (ε / (6 * Ce) + ε / (6 * Ce)) := by
          rw [h1]
          gcongr
      _ = ε / 3 := by field_simp; ring
  -- combine
  have hx_eq : endpointMean μ G' (M n) n f x = windowMean μ G' (M n) N N f s := rfl
  have hx'_eq : endpointMean μ G' (M n) n f x' = windowMean μ G' (M n) N N f s' := rfl
  rw [hx_eq, hx'_eq]
  have e1 := abs_sub_le (windowMean μ G' (M n) N N f s) (windowMean μ G' (M n) (N - t) N f s)
    (windowMean μ G' (M n) N N f s')
  have e2 := abs_sub_le (windowMean μ G' (M n) (N - t) N f s)
    (windowMean μ G' (M n) (N - t) N f s') (windowMean μ G' (M n) N N f s')
  have e3 := hdel s hsr hψ
  have e4 := hsm.trans hBle
  have e5 := hdel s' hsr' hψ'
  rw [abs_sub_comm] at e5
  linarith

/-! ### Block reduction of `b_3` -/

private theorem indicator_one_congr {X R : Type*} [Zero R] [One R] {s : Set X} {u v : X}
    (h : u ∈ s ↔ v ∈ s) : s.indicator (1 : X → R) u = s.indicator 1 v := by
  by_cases hu : u ∈ s
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (h.1 hu)]
    rfl
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (fun hv => hu (h.2 hv))]

/-- Cyclic exchangeability of the bridge, integral form. -/
theorem integral_bridgeLaw_rotate (μ : PMF ℕ) (n i : ℕ) (Φ : List ℤ → ℝ) :
    ∫ ω, Φ ((List.ofFn ω).rotate i) ∂bridgeLaw μ n = ∫ ω, Φ (List.ofFn ω) ∂bridgeLaw μ n := by
  conv_rhs => rw [← map_bridgeLaw_rotate μ n i]
  rw [integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only
  rw [ofFn_toVec (by simp)]

/-- The forward gaps `cycGap n i j` of the indices `j` outside the neighbourhood `B_i` are
exactly `M, …, n - M`. -/
theorem image_cycGap_compl_cycNbhd {M n : ℕ} (hM : 0 < M) (i : Fin n) :
    (Finset.univ \ cycNbhd n M i).image (fun j : Fin n => cycGap n i j) =
      Finset.Icc M (n - M) := by
  ext g
  simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_cycNbhd,
    Finset.mem_Icc]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have := i.2
    have := j.2
    unfold cycGap cycDist at *
    split_ifs at * <;> omega
  · rintro ⟨h1, h2⟩
    have hi := i.2
    by_cases hig : (i : ℕ) + g < n
    · refine ⟨⟨i + g, hig⟩, ?_, ?_⟩
      · simp only [cycDist]
        omega
      · simp only [cycGap]
        split_ifs <;> omega
    · refine ⟨⟨i + g - n, by omega⟩, ?_, ?_⟩
      · simp only [cycDist]
        omega
      · simp only [cycGap]
        split_ifs <;> omega

/-- **Bookkeeping of the cyclic wrap** (source lines 1873–1880): the indices outside the
neighbourhood `B_i` are those at forward distance `M, …, n - M` from `i`, so
`∑_{j ∉ B_i} I_j^{(M)}(𝐱)` is the window count of the block `(x_{i+M+1}, …, x_{i+n})` of the
`i`-th cyclic shift (`n - M` increments, `n - 2M + 1` indicators). -/
theorem sum_compl_cycNbhd_indicator (G : PlaneTree → Prop) {M n : ℕ} (hM : 0 < M)
    (ω : Fin n → ℤ) (i : Fin n) :
    ∑ j ∈ Finset.univ \ cycNbhd n M i, (cycEvent G M n j).indicator (1 : (Fin n → ℤ) → ℕ) ω =
      windowCount G M (n - M) (((List.ofFn ω).rotate i).drop M) := by
  set y := (List.ofFn ω).rotate i with hy
  have hylen : y.length = n := by simp [hy]
  set F : ℕ → ℕ := fun g => (markSet G M).indicator (1 : List ℤ → ℕ) (y.rotate g) with hF
  have h1 : ∀ j ∈ Finset.univ \ cycNbhd n M i,
      (cycEvent G M n j).indicator (1 : (Fin n → ℤ) → ℕ) ω = F (cycGap n i j) := by
    intro j _
    change _ = (markSet G M).indicator (1 : List ℤ → ℕ)
      (((List.ofFn ω).rotate i).rotate (cycGap n i j))
    rw [rotate_rotate_cycGap List.length_ofFn i.2 j.2]
    exact (indicator_markSet_eq G M (fun ω : Fin n → ℤ => (List.ofFn ω).rotate j) ω).symm
  rw [Finset.sum_congr rfl h1, ← Finset.sum_image (f := F)
    (fun j _ j' _ h => Fin.ext (cycGap_inj_right i.2 j.2 j'.2 h)),
    image_cycGap_compl_cycNbhd hM i, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  unfold windowCount
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [hF, List.drop_drop]
  refine indicator_one_congr ?_
  exact firstMarked_rotate_iff_drop (by rw [hylen]; omega)

/-- The integrand `(I_1^{(M)}(𝐲) - q) f(1 + ∑_{j=1}^{n-2M+1} I_{M+j}^{(M)}(𝐲))` of the reduced
form of `b_3` (source line 1877). -/
noncomputable def blockIntegrand (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) (f : ℕ → ℝ)
    (y : List ℤ) : ℝ :=
  ((markSet G M).indicator (1 : List ℤ → ℝ) y - qProb μ G M n) *
    f (1 + windowCount G M (n - M) (y.drop M))

/-- The integrand of `b_3` at index `i`, as a function of the `i`-th cyclic shift. -/
theorem errorB3_integrand_eq (μ : PMF ℕ) (G : PlaneTree → Prop) {M n : ℕ} (hM : 0 < M)
    (f : ℕ → ℝ) (i : Fin n) (ω : Fin n → ℤ) :
    ((cycEvent G M n i).indicator (1 : (Fin n → ℤ) → ℝ) ω -
      (bridgeLaw μ n).real (cycEvent G M n i)) *
      f (1 + ∑ j ∈ Finset.univ \ cycNbhd n M i,
        (cycEvent G M n j).indicator (1 : (Fin n → ℤ) → ℕ) ω) =
    blockIntegrand μ G M n f ((List.ofFn ω).rotate i) := by
  have hI : (cycEvent G M n i).indicator (1 : (Fin n → ℤ) → ℝ) ω =
      (markSet G M).indicator 1 ((List.ofFn ω).rotate i) :=
    (indicator_markSet_eq G M (fun ω : Fin n → ℤ => (List.ofFn ω).rotate i) ω).symm
  rw [sum_compl_cycNbhd_indicator G hM ω i, bridgeLaw_real_cycEvent, hI]
  rfl

/-- **Cyclic exchangeability for `b_3`** (source line 1877): all `n` terms of `b_3` are equal,
`b_3 = n |E[(I_1^{(M)} - q) f(1 + ∑_{j ≤ n - 2M + 1} I_{M+j}^{(M)}) | S_n = -1]|`. -/
theorem errorB3_eq_mul (μ : PMF ℕ) (G : PlaneTree → Prop) {M n : ℕ} (hM : 0 < M)
    (f : ℕ → ℝ) :
    errorB3 μ G M n f = n * |∫ ω, blockIntegrand μ G M n f (List.ofFn ω) ∂bridgeLaw μ n| := by
  unfold errorB3
  rw [Finset.sum_congr rfl
    (g := fun _ => |∫ ω, blockIntegrand μ G M n f (List.ofFn ω) ∂bridgeLaw μ n|)]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · intro i _
    congr 1
    rw [← integral_bridgeLaw_rotate μ n i]
    exact integral_congr_ae (Eventually.of_forall fun ω => errorB3_integrand_eq μ G hM f i ω)

/-! ### Subtracting a compatible base value and returning to the walk -/

/-- `|h_n(k)| ≤ ‖f‖_∞ ≤ 1` (also at null endpoints, where `h_n(k) = 0`). -/
theorem abs_endpointMean_le (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) {f : ℕ → ℝ}
    (hf : ∀ w, |f w| ≤ 1) (x : ℤ) : |endpointMean μ G M n f x| ≤ 1 := by
  unfold endpointMean windowMean
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := 1)
    (Eventually.of_forall fun b => by rw [Real.norm_eq_abs]; exact hf _)).trans ?_
  exact mul_le_of_le_one_right zero_le_one measureReal_le_one

/-- `|I_1^{(M)} - q| ≤ 1`. -/
theorem abs_indicator_sub_qProb_le (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ)
    (y : List ℤ) : |(markSet G M).indicator (1 : List ℤ → ℝ) y - qProb μ G M n| ≤ 1 := by
  have h1 := indicator_one_mem_Icc (markSet G M) y
  have h2 : 0 ≤ qProb μ G M n := measureReal_nonneg
  have h3 : qProb μ G M n ≤ 1 := measureReal_le_one
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2]

/-- Locality of `I_1^{(M)}`: it only reads the first `M` entries. -/
theorem indicator_markSet_take (G : PlaneTree → Prop) (M : ℕ) (y : List ℤ) :
    (markSet G M).indicator (1 : List ℤ → ℝ) (y.take M) =
      (markSet G M).indicator (1 : List ℤ → ℝ) y :=
  indicator_one_congr firstMarked_take_iff

/-- **Block reduction of `b_3`** (proof of Proposition `prop:b3bis`, source lines 1880–1886):
conditionally on `S_{M} = k` and `S_n = -1`, the blocks `(X_1..X_M)` and `(X_{M+1}..X_n)` are
independent, so `E[(I_1 - q) f(1 + ∑_j I_{M+j}) | S_n = -1] = E[(I_1 - q) h_n(S_M) | S_n = -1]`;
since `E[I_1 - q | S_n = -1] = 0`, any constant `κ` may be subtracted from `h_n` (correction F2:
the paper subtracts `h_n(0)`, a conditional mean at a null endpoint in the periodic case). -/
theorem integral_blockIntegrand_eq (μ : PMF ℕ) (G : PlaneTree → Prop) {M n : ℕ}
    (hn : Admissible μ n) (hMn : M ≤ n) {f : ℕ → ℝ} (hf : ∀ w, |f w| ≤ 1) (κ : ℝ) :
    ∫ ω, blockIntegrand μ G M n f (List.ofFn ω) ∂bridgeLaw μ n =
      ∫ ω, ((markSet G M).indicator (1 : List ℤ → ℝ) (List.ofFn ω) - qProb μ G M n) *
        (endpointMean μ G M n f ((List.ofFn ω).take M).sum - κ) ∂bridgeLaw μ n := by
  have := isProbabilityMeasure_bridgeLaw hn
  set q := qProb μ G M n with hq
  set F : List ℤ → ℝ := fun z => (markSet G M).indicator (1 : List ℤ → ℝ) z - q with hF
  set Gf : List ℤ → ℝ := fun z => f (1 + windowCount G M (n - M) z) with hGf
  set h : ℤ → ℝ := endpointMean μ G M n f with hh
  have hFb : ∀ z, |F z| ≤ 1 := fun z => abs_indicator_sub_qProb_le μ G M n z
  have hGb : ∀ z, |Gf z| ≤ 1 := fun z => hf _
  have hhb : ∀ x, |h x| ≤ 1 := fun x => abs_endpointMean_le μ G M n hf x
  have hFt : ∀ z, F (z.take M) = F z := fun z => by
    simp only [hF]
    rw [indicator_markSet_take]
  have step1 : ∫ ω, blockIntegrand μ G M n f (List.ofFn ω) ∂bridgeLaw μ n =
      ∫ ω, F ((List.ofFn ω).take M) * Gf ((List.ofFn ω).drop M)
        ∂cond (walkVecLaw μ n) {ω | ∑ i, ω i = -1} := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [blockIntegrand]
    rw [hFt]
  rw [step1, integral_cond_take_mul_drop μ hMn (-1) F Gf hFb hGb]
  change ∫ ω, F ((List.ofFn ω).take M) * h ((List.ofFn ω).take M).sum ∂bridgeLaw μ n = _
  have hint1 : Integrable (fun ω : Fin n → ℤ => F (List.ofFn ω) * h ((List.ofFn ω).take M).sum)
      (bridgeLaw μ n) := integrable_of_abs_le _ 1 fun ω => by
    rw [abs_mul]
    exact (mul_le_mul (hFb _) (hhb _) (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hint2 : Integrable (fun ω : Fin n → ℤ => F (List.ofFn ω)) (bridgeLaw μ n) :=
    integrable_of_abs_le _ 1 fun ω => hFb _
  have h0 : ∫ ω, F (List.ofFn ω) ∂bridgeLaw μ n = 0 := by
    simp only [hF]
    rw [integral_sub (integrable_of_abs_le _ 1 fun ω => by
        rw [abs_of_nonneg (indicator_one_mem_Icc _ _).1]; exact (indicator_one_mem_Icc _ _).2)
      (integrable_const _), integral_const, probReal_univ, one_smul]
    simp_rw [indicator_markSet_eq G M (fun ω : Fin n → ℤ => List.ofFn ω)]
    rw [integral_indicator_one (Set.to_countable _).measurableSet, hq, qProb, sub_self]
  calc ∫ ω, F ((List.ofFn ω).take M) * h ((List.ofFn ω).take M).sum ∂bridgeLaw μ n
      = ∫ ω, F (List.ofFn ω) * h ((List.ofFn ω).take M).sum ∂bridgeLaw μ n := by
        simp only [hFt]
    _ = ∫ ω, F (List.ofFn ω) * h ((List.ofFn ω).take M).sum ∂bridgeLaw μ n -
          κ * ∫ ω, F (List.ofFn ω) ∂bridgeLaw μ n := by rw [h0, mul_zero, sub_zero]
    _ = ∫ ω, F (List.ofFn ω) * (h ((List.ofFn ω).take M).sum - κ) ∂bridgeLaw μ n := by
        rw [← integral_const_mul, ← integral_sub hint1 (hint2.const_mul κ)]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only
        ring

/-- **Markov property at time `M` under the bridge**: the reduced `b_3` integrand in walk form,
`E[(I_1 - q)(h_n(S_M) - κ) | S_n = -1] =
Ψ_n(-1)⁻¹ E[(I_1 - q)(h_n(S_M) - κ) Ψ_{n-M}(-1 - S_M)]`. -/
theorem integral_bridgeLaw_eq_walk (μ : PMF ℕ) (G : PlaneTree → Prop) {M n : ℕ} (hMn : M ≤ n)
    {f : ℕ → ℝ} (hf : ∀ w, |f w| ≤ 1) (κ : ℝ) :
    ∫ ω, ((markSet G M).indicator (1 : List ℤ → ℝ) (List.ofFn ω) - qProb μ G M n) *
        (endpointMean μ G M n f ((List.ofFn ω).take M).sum - κ) ∂bridgeLaw μ n =
      (walkProb μ n (-1))⁻¹ * ∫ b, ((markSet G M).indicator (1 : List ℤ → ℝ) (List.ofFn b) -
        qProb μ G M n) * (endpointMean μ G M n f (∑ i, b i) - κ) *
          walkProb μ ((n - M : ℕ) : ℤ) (-1 - ∑ i, b i) ∂walkVecLaw μ M := by
  set Φ : List ℤ → ℝ := fun z => ((markSet G M).indicator (1 : List ℤ → ℝ) z - qProb μ G M n) *
    (endpointMean μ G M n f z.sum - κ) with hΦ
  have hΦb : ∀ z, |Φ z| ≤ 1 * (1 + |κ|) := fun z => by
    simp only [hΦ]
    rw [abs_mul]
    refine mul_le_mul (abs_indicator_sub_qProb_le μ G M n z) ?_ (abs_nonneg _) zero_le_one
    exact (abs_sub _ _).trans (by linarith [abs_endpointMean_le μ G M n hf z.sum])
  have h := integral_cond_take μ hMn (-1) Φ hΦb
  simp only [hΦ, indicator_markSet_take, List.sum_ofFn] at h
  exact h


/-! ### The final estimate -/

/-- `P(|S_m| > r)` computed from the increments. -/
theorem walkVecLaw_real_abs_sum_gt (μ : PMF ℕ) (m : ℕ) (r : ℝ) :
    (walkVecLaw μ m).real {b | r < |((∑ i, b i : ℤ) : ℝ)|} =
      (walkLaw μ m).real {x : ℤ | r < |(x : ℝ)|} := by
  rw [measureReal_def, measureReal_def, walkLaw_apply]
  rfl

/-- **The small/large endpoint split** (proof of Lemma `lem:1`, bounds on `R_n^1`, `R_n^2`,
source lines 1898–1924), at a fixed size: if `|h_n(k) - κ| ≤ ε'` at every compatible endpoint
`|k| ≤ r`, `|κ| ≤ 1` and `Ψ_{n-M} ≤ B`, then
`|E[(I_1 - q)(h_n(S_M) - κ) Ψ_{n-M}(-1 - S_M)]| ≤
B (ε' (p + q) + 2 P(I_1 = 1, |S_M| > r) + 2 q P(|S_M| > r))`. At an incompatible endpoint the
weight `Ψ_{n-M}(-1 - S_M)` vanishes. -/
theorem abs_walkIntegral_le (μ : PMF ℕ) (G : PlaneTree → Prop) {M n : ℕ} {f : ℕ → ℝ}
    (hf : ∀ w, |f w| ≤ 1) {κ ε' r B : ℝ} (hκ : |κ| ≤ 1) (hε' : 0 ≤ ε')
    (hosc : ∀ x : ℤ, |(x : ℝ)| ≤ r → walkProb μ ((n - M : ℕ) : ℤ) (-1 - x) ≠ 0 →
      |endpointMean μ G M n f x - κ| ≤ ε')
    (hB : ∀ x : ℤ, walkProb μ ((n - M : ℕ) : ℤ) x ≤ B) :
    |∫ b, ((markSet G M).indicator (1 : List ℤ → ℝ) (List.ofFn b) - qProb μ G M n) *
        (endpointMean μ G M n f (∑ i, b i) - κ) * walkProb μ ((n - M : ℕ) : ℤ) (-1 - ∑ i, b i)
        ∂walkVecLaw μ M| ≤
      B * (ε' * (pProb μ G M + qProb μ G M n) +
        2 * (walkVecLaw μ M).real
          {b | FirstMarked G M (List.ofFn b) ∧ r < |((∑ i, b i : ℤ) : ℝ)|} +
        2 * qProb μ G M n * (walkVecLaw μ M).real {b | r < |((∑ i, b i : ℤ) : ℝ)|}) := by
  have hB0 : 0 ≤ B := (walkProb_nonneg μ _ _).trans (hB 0)
  set q := qProb μ G M n with hq
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := measureReal_le_one
  set S0 : Set (Fin M → ℤ) := {b | FirstMarked G M (List.ofFn b)} with hS0
  set S1 : Set (Fin M → ℤ) := {b | FirstMarked G M (List.ofFn b) ∧
    r < |((∑ i, b i : ℤ) : ℝ)|} with hS1
  set S2 : Set (Fin M → ℤ) := {b | r < |((∑ i, b i : ℤ) : ℝ)|} with hS2
  set g : (Fin M → ℤ) → ℝ := fun b => B * (ε' * S0.indicator 1 b + ε' * q +
    2 * S1.indicator 1 b + 2 * q * S2.indicator 1 b) with hg
  have hI := fun (S : Set (Fin M → ℤ)) (b : Fin M → ℤ) => indicator_one_mem_Icc S b
  have hg0 : ∀ b, 0 ≤ g b := fun b => by
    have h0 := hI S0 b
    have h1 := hI S1 b
    have h2 := hI S2 b
    simp only [hg]
    exact mul_nonneg hB0 (add_nonneg (add_nonneg (add_nonneg (mul_nonneg hε' h0.1)
      (mul_nonneg hε' hq0)) (mul_nonneg zero_le_two h1.1))
      (mul_nonneg (mul_nonneg zero_le_two hq0) h2.1))
  have hgle : ∀ b, |g b| ≤ B * (ε' + ε' + 2 + 2) := fun b => by
    rw [abs_of_nonneg (hg0 b)]
    have h0 := hI S0 b
    have h1 := hI S1 b
    have h2 := hI S2 b
    simp only [hg]
    refine mul_le_mul_of_nonneg_left ?_ hB0
    have a1 := mul_le_mul_of_nonneg_left h0.2 hε'
    have a2 := mul_le_mul_of_nonneg_left hq1 hε'
    have a4 := mul_le_mul hq1 h2.2 h2.1 zero_le_one
    nlinarith [h1.2]
  have hint : ∀ S : Set (Fin M → ℤ), Integrable (S.indicator (1 : (Fin M → ℤ) → ℝ))
      (walkVecLaw μ M) := fun S => integrable_of_abs_le _ 1 fun b => by
    rw [abs_of_nonneg (hI S b).1]
    exact (hI S b).2
  have hpt : ∀ b : Fin M → ℤ, ‖((markSet G M).indicator (1 : List ℤ → ℝ) (List.ofFn b) - q) *
      (endpointMean μ G M n f (∑ i, b i) - κ) *
        walkProb μ ((n - M : ℕ) : ℤ) (-1 - ∑ i, b i)‖ ≤ g b := by
    intro b
    set y := ∑ i, b i with hy
    set P := walkProb μ ((n - M : ℕ) : ℤ) (-1 - y) with hP
    have hP0 : 0 ≤ P := walkProb_nonneg μ _ _
    have hPB : P ≤ B := hB _
    have hIb : (markSet G M).indicator (1 : List ℤ → ℝ) (List.ofFn b) = S0.indicator 1 b :=
      indicator_markSet_eq G M (fun b : Fin M → ℤ => List.ofFn b) b
    rw [hIb, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hP0]
    have h0 := hI S0 b
    have h1 := hI S1 b
    have h2 := hI S2 b
    have hIq : |S0.indicator (1 : (Fin M → ℤ) → ℝ) b - q| ≤ S0.indicator 1 b + q := by
      rw [abs_le]
      constructor <;> linarith
    have hhκ : |endpointMean μ G M n f y - κ| ≤ 2 :=
      (abs_sub _ _).trans (by linarith [abs_endpointMean_le μ G M n hf y])
    by_cases hPz : P = 0
    · rw [hPz, mul_zero]
      exact hg0 b
    by_cases hyr : |(y : ℝ)| ≤ r
    · have hosc' := hosc y hyr hPz
      calc |S0.indicator (1 : (Fin M → ℤ) → ℝ) b - q| * |endpointMean μ G M n f y - κ| * P
          ≤ (S0.indicator 1 b + q) * ε' * B := by
            have := mul_le_mul hIq hosc' (abs_nonneg _) (by linarith [h0.1])
            exact mul_le_mul this hPB hP0 (mul_nonneg (by linarith [h0.1]) hε')
        _ ≤ g b := by
          simp only [hg]
          have : 0 ≤ B * (2 * S1.indicator (1 : (Fin M → ℤ) → ℝ) b +
              2 * q * S2.indicator 1 b) :=
            mul_nonneg hB0 (add_nonneg (mul_nonneg zero_le_two h1.1)
              (mul_nonneg (mul_nonneg zero_le_two hq0) h2.1))
          linarith
    · have hyr' : r < |(y : ℝ)| := not_le.1 hyr
      have hS2b : S2.indicator (1 : (Fin M → ℤ) → ℝ) b = 1 := by
        rw [Set.indicator_of_mem (show b ∈ S2 from hyr')]
        rfl
      have hS1b : S1.indicator (1 : (Fin M → ℤ) → ℝ) b = S0.indicator 1 b := by
        by_cases h : b ∈ S0
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show b ∈ S1 from ⟨h, hyr'⟩)]
        · rw [Set.indicator_of_notMem h,
            Set.indicator_of_notMem (show b ∉ S1 from fun h' => h h'.1)]
      calc |S0.indicator (1 : (Fin M → ℤ) → ℝ) b - q| * |endpointMean μ G M n f y - κ| * P
          ≤ (S0.indicator 1 b + q) * 2 * B := by
            have := mul_le_mul hIq hhκ (abs_nonneg _) (by linarith [h0.1])
            exact mul_le_mul this hPB hP0 (mul_nonneg (by linarith [h0.1]) zero_le_two)
        _ ≤ g b := by
          simp only [hg]
          rw [hS1b, hS2b]
          have : 0 ≤ B * (ε' * S0.indicator (1 : (Fin M → ℤ) → ℝ) b + ε' * q) :=
            mul_nonneg hB0 (add_nonneg (mul_nonneg hε' h0.1) (mul_nonneg hε' hq0))
          linarith
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (integrable_of_abs_le _ _ hgle)
    (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  simp only [hg]
  rw [integral_const_mul]
  congr 1
  have i0 : Integrable (fun a => ε' * S0.indicator (1 : (Fin M → ℤ) → ℝ) a)
      (walkVecLaw μ M) := (hint S0).const_mul ε'
  have ic : Integrable (fun _ : Fin M → ℤ => ε' * q) (walkVecLaw μ M) := integrable_const _
  have i1 : Integrable (fun a => 2 * S1.indicator (1 : (Fin M → ℤ) → ℝ) a)
      (walkVecLaw μ M) := (hint S1).const_mul 2
  have i2 : Integrable (fun a => 2 * q * S2.indicator (1 : (Fin M → ℤ) → ℝ) a)
      (walkVecLaw μ M) := (hint S2).const_mul _
  have i01 : Integrable (fun a => ε' * S0.indicator (1 : (Fin M → ℤ) → ℝ) a + ε' * q)
      (walkVecLaw μ M) := i0.add ic
  have i012 : Integrable (fun a => ε' * S0.indicator (1 : (Fin M → ℤ) → ℝ) a + ε' * q +
      2 * S1.indicator (1 : (Fin M → ℤ) → ℝ) a) (walkVecLaw μ M) := i01.add i1
  have e0 : ∫ a, ε' * S0.indicator (1 : (Fin M → ℤ) → ℝ) a ∂walkVecLaw μ M =
      ε' * (walkVecLaw μ M).real S0 := by
    rw [integral_const_mul, integral_indicator_one (Set.to_countable _).measurableSet]
  have ec : ∫ _ : Fin M → ℤ, ε' * q ∂walkVecLaw μ M = ε' * q := by
    rw [integral_const, probReal_univ, one_smul]
  have e1 : ∫ a, 2 * S1.indicator (1 : (Fin M → ℤ) → ℝ) a ∂walkVecLaw μ M =
      2 * (walkVecLaw μ M).real S1 := by
    rw [integral_const_mul, integral_indicator_one (Set.to_countable _).measurableSet]
  have e2 : ∫ a, 2 * q * S2.indicator (1 : (Fin M → ℤ) → ℝ) a ∂walkVecLaw μ M =
      2 * q * (walkVecLaw μ M).real S2 := by
    rw [integral_const_mul, integral_indicator_one (Set.to_countable _).measurableSet]
  rw [integral_add i012 i2, integral_add i01 i1, integral_add i0 ic, e0, ec, e1, e2, pProb]
  ring

/-! ### Lemma `lem:1` and Proposition `prop:b3bis` -/

/-- **The combination step of Lemma `lem:1`** (source lines 1898–1924): for every `ε > 0` there
is `ε' > 0` such that, eventually along admissible sizes, for every test function
`‖f‖_∞ ≤ 1` and every constant `|κ| ≤ 1` with `|h_n(k) - κ| ≤ ε'` at all compatible endpoints
`|k| ≤ r_n = √(a_{M_n} a_n)`,
`n |E[(I_1^{(M_n)} - q_n)(h_n(S_{M_n}) - κ) | S_n = -1]| ≤ ε`. The large endpoints are
controlled by Lemma `lem:pnqn`(i) and marginal tightness (correction F6), the small ones by
`2 n q_n ε'`; only bounded `n π_n` and the cutoff properties are used. -/
theorem exists_eventually_mul_abs_integral_le (hT : StableToolkit μ α a)
    {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ} (hM : IsCutoff M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ε' : ℝ, 0 < ε' ∧ ∀ᶠ n in admissibleSizes μ, ∀ f : ℕ → ℝ, (∀ w, |f w| ≤ 1) →
      ∀ κ : ℝ, |κ| ≤ 1 →
      (∀ x : ℤ, |(x : ℝ)| ≤ √(a (M n) * a n) →
        walkProb μ ((n - M n : ℕ) : ℤ) (-1 - x) ≠ 0 →
        |endpointMean μ (G (k n)) (M n) n f x - κ| ≤ ε') →
      (n : ℝ) * |∫ ω, ((markSet (G (k n)) (M n)).indicator (1 : List ℤ → ℝ) (List.ofFn ω) -
          qProb μ (G (k n)) (M n) n) *
          (endpointMean μ (G (k n)) (M n) n f ((List.ofFn ω).take (M n)).sum - κ)
            ∂bridgeLaw μ n| ≤ ε := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := hT.exists_le_div_of_le_two_mul
  obtain ⟨c, hc, hlow⟩ := hT.exists_lower_bound_neg_one
  obtain ⟨C₂, hC₂⟩ := hbd
  obtain ⟨C₃, hC₃, hq⟩ := exists_qProb_le_mul_markProb hT G k hM.isLittleO
  set C₂' : ℝ := max C₂ 1 with hC₂'
  have hC₂'0 : 0 < C₂' := lt_max_of_lt_right one_pos
  set K : ℝ := C₁ / c + 1 with hK
  have hK0 : 0 < K := by positivity
  set ε' : ℝ := ε / (3 * K * C₂' * (1 + C₃)) with hε'
  have hε'0 : 0 < ε' := by positivity
  refine ⟨ε', hε'0, ?_⟩
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  have hsq := hT.regularlyVarying.tendsto_sqrt_div hT.monotone hT.pos hT.rho_pos
    hM.tendsto_atTop hM.isLittleO
  have hM1 : ∀ᶠ n in atTop, 1 ≤ M n := hM.tendsto_atTop.eventually_ge_atTop 1
  filter_upwards [hl (hT.eventually_walkLaw_tail_le hM1 hsq.1 hε'0),
    (isLittleO_walkVecLaw_firstMarked_abs_sum_gt_admissible hT G k hM).def hε'0, hC₂,
    hl (eventually_two_mul_le hM), hl (eventually_ge_atTop 2), hadm]
    with n htail hlo hC₂n h2Mn hn2 hadmn f hf κ hκ hosc
  have hn1 : 1 ≤ n := by omega
  have hMn : M n ≤ n := by omega
  have hNM : 1 ≤ n - M n := by omega
  have han : 0 < a n := hT.pos n hn1
  have hψ : 0 < walkProb μ n (-1) := (walkProb_neg_one_pos_iff μ n).2 hadmn
  have hψlow : c / a n ≤ walkProb μ n (-1) := hlow n hn1 hψ
  have hinv : (walkProb μ n (-1))⁻¹ ≤ a n / c := by
    calc (walkProb μ n (-1))⁻¹ ≤ (c / a n)⁻¹ := inv_anti₀ (by positivity) hψlow
      _ = a n / c := inv_div _ _
  have hB : ∀ x : ℤ, walkProb μ ((n - M n : ℕ) : ℤ) x ≤ C₁ / a n :=
    fun x => hC₁ n (n - M n) hn1 hNM (by omega) x
  set r := √(a (M n) * a n) with hr
  set p := pProb μ (G (k n)) (M n) with hp
  set q := qProb μ (G (k n)) (M n) n with hqdef
  set P1 := (walkVecLaw μ (M n)).real
    {b | FirstMarked (G (k n)) (M n) (List.ofFn b) ∧ r < |((∑ i, b i : ℤ) : ℝ)|} with hP1
  set P2 := (walkVecLaw μ (M n)).real {b | r < |((∑ i, b i : ℤ) : ℝ)|} with hP2
  have hmain := abs_walkIntegral_le μ (G (k n)) hf hκ hε'0.le hosc hB
  rw [integral_bridgeLaw_eq_walk μ _ hMn hf κ, abs_mul, abs_of_pos (inv_pos.2 hψ)]
  -- the estimates
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hP10 : 0 ≤ P1 := measureReal_nonneg
  have hP20 : 0 ≤ P2 := measureReal_nonneg
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hπ0 : 0 ≤ markProb μ G k n := measureReal_nonneg
  have e1 : (n : ℝ) * p ≤ C₂' :=
    (mul_le_mul_of_nonneg_left (pProb_le μ _ _) hn0).trans (hC₂n.trans (le_max_left _ _))
  have e2 : (n : ℝ) * q ≤ C₃ * C₂' := by
    calc (n : ℝ) * q ≤ n * (C₃ * markProb μ G k n) :=
          mul_le_mul_of_nonneg_left (hq n hn1 hadmn) hn0
      _ = C₃ * (n * markProb μ G k n) := by ring
      _ ≤ C₃ * C₂' := mul_le_mul_of_nonneg_left (hC₂n.trans (le_max_left _ _)) hC₃.le
  have hP1le : P1 ≤ ε' * p := by
    have h := hlo
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hP10, abs_of_nonneg hp0] at h
    exact h
  have hP2le : P2 ≤ ε' := by
    rw [hP2, walkVecLaw_real_abs_sum_gt]
    exact htail (M n) le_rfl
  have e3 : (n : ℝ) * P1 ≤ ε' * C₂' := by
    calc (n : ℝ) * P1 ≤ n * (ε' * p) := mul_le_mul_of_nonneg_left hP1le hn0
      _ = ε' * (n * p) := by ring
      _ ≤ ε' * C₂' := mul_le_mul_of_nonneg_left e1 hε'0.le
  have e4 : (n : ℝ) * q * P2 ≤ C₃ * C₂' * ε' :=
    mul_le_mul e2 hP2le hP20 (by positivity)
  have hX : (n : ℝ) * (ε' * (p + q) + 2 * P1 + 2 * q * P2) ≤ 3 * ε' * C₂' * (1 + C₃) := by
    calc (n : ℝ) * (ε' * (p + q) + 2 * P1 + 2 * q * P2)
        = ε' * (n * p) + ε' * (n * q) + 2 * (n * P1) + 2 * (n * q * P2) := by ring
      _ ≤ ε' * C₂' + ε' * (C₃ * C₂') + 2 * (ε' * C₂') + 2 * (C₃ * C₂' * ε') := by
          gcongr
      _ = 3 * ε' * C₂' * (1 + C₃) := by ring
  have hX0 : 0 ≤ ε' * (p + q) + 2 * P1 + 2 * q * P2 := by positivity
  calc (n : ℝ) * ((walkProb μ n (-1))⁻¹ * |∫ b, ((markSet (G (k n)) (M n)).indicator
          (1 : List ℤ → ℝ) (List.ofFn b) - q) *
          (endpointMean μ (G (k n)) (M n) n f (∑ i, b i) - κ) *
            walkProb μ ((n - M n : ℕ) : ℤ) (-1 - ∑ i, b i) ∂walkVecLaw μ (M n)|)
      ≤ n * (a n / c * (C₁ / a n * (ε' * (p + q) + 2 * P1 + 2 * q * P2))) := by
        gcongr
    _ = C₁ / c * (n * (ε' * (p + q) + 2 * P1 + 2 * q * P2)) := by
        field_simp
    _ ≤ K * (3 * ε' * C₂' * (1 + C₃)) := by
        gcongr
        rw [hK]
        linarith
    _ = ε := by
        rw [hε']
        field_simp

/-- **Lemma `lem:1`** (source lines 1872–1876, proof 1891–1995), with a compatible base point
(correction F2): for every `ε > 0`, eventually along admissible sizes, for every test function
`‖f‖_∞ ≤ 1` and every base point `k₀` with `|k₀| ≤ r_n = √(a_{M_n} a_n)` and
`Ψ_{n-M_n}(-1-k₀) ≠ 0`, with `Δ_n(k) = h_n(k) - h_n(k₀)`,
`n |E[(I_1^{(M_n)} - q_n) Δ_n(S_{M_n}) | S_n = -1]| ≤ ε`.
(The paper's base point is `k₀ = 0`, compatible exactly when `d ∣ M_n`; in the aperiodic case
`d = 1` it is always admissible here.) -/
theorem eventually_lem1 (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hM : IsCutoff M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in admissibleSizes μ, ∀ f : ℕ → ℝ, (∀ w, |f w| ≤ 1) → ∀ k₀ : ℤ,
      |(k₀ : ℝ)| ≤ √(a (M n) * a n) → walkProb μ ((n - M n : ℕ) : ℤ) (-1 - k₀) ≠ 0 →
      (n : ℝ) * |∫ ω, ((markSet (G (k n)) (M n)).indicator (1 : List ℤ → ℝ) (List.ofFn ω) -
          qProb μ (G (k n)) (M n) n) *
          (endpointMean μ (G (k n)) (M n) n f ((List.ofFn ω).take (M n)).sum -
            endpointMean μ (G (k n)) (M n) n f k₀) ∂bridgeLaw μ n| ≤ ε := by
  obtain ⟨ε', hε', hcore⟩ := exists_eventually_mul_abs_integral_le hT hM hbd hε
  filter_upwards [hcore, eventually_abs_endpointMean_sub_le hT hM hbd hε']
    with n h1 h2 f hf k₀ hk₀ hψ₀
  exact h1 f hf _ (abs_endpointMean_le μ _ _ n hf k₀)
    (fun x hx hψ => h2 f hf x k₀ hx hk₀ hψ hψ₀)

/-- **Lemma `lem:1`**, sequential form: for test functions `f_n` with `‖f_n‖_∞ ≤ 1` and
compatible base points `k₀(n)` with `|k₀(n)| ≤ r_n`,
`n E[(I_1^{(M_n)} - q_n) Δ_n(S_{M_n}) | S_n = -1] → 0` along admissible sizes. -/
theorem tendsto_lem1 (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hM : IsCutoff M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C)
    (f : ℕ → ℕ → ℝ) (hf : ∀ n w, |f n w| ≤ 1) (k₀ : ℕ → ℤ)
    (hk₀ : ∀ᶠ n in admissibleSizes μ, |(k₀ n : ℝ)| ≤ √(a (M n) * a n) ∧
      walkProb μ ((n - M n : ℕ) : ℤ) (-1 - k₀ n) ≠ 0) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, ((markSet (G (k n)) (M n)).indicator (1 : List ℤ → ℝ)
        (List.ofFn ω) - qProb μ (G (k n)) (M n) n) *
        (endpointMean μ (G (k n)) (M n) n (f n) ((List.ofFn ω).take (M n)).sum -
          endpointMean μ (G (k n)) (M n) n (f n) (k₀ n)) ∂bridgeLaw μ n)
      (admissibleSizes μ) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_lem1 hT hM hbd (half_pos hε), hk₀] with n h hk
  rw [Real.dist_eq, sub_zero, abs_mul, Nat.abs_cast]
  exact (h (f n) (hf n) (k₀ n) hk.1 hk.2).trans_lt (half_lt_self hε)

/-- **Proposition `prop:b3bis`, uniform form** (source lines 1862–1864, proof 1880–1886): for
every `ε > 0`, eventually along admissible sizes, `b_3^n(f) ≤ ε` for **every** test function
`‖f‖_∞ ≤ 1`. This is the form needed after `exists_paperTVDist_cyclicSum_le_errorTerms`,
whose test function depends on `n`. Proof: cyclic exchangeability and block reduction
(`errorB3_eq_mul`, `integral_blockIntegrand_eq`) with a compatible base value `κ = h_n(k₀)`
(correction F2; if no compatible endpoint `|k₀| ≤ r_n` exists, `κ = 0` and the small-endpoint
part is empty), then `exists_eventually_mul_abs_integral_le` and
`eventually_abs_endpointMean_sub_le`. Assumption (M) is not needed. -/
theorem eventually_errorB3_le (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in admissibleSizes μ, ∀ f : ℕ → ℝ, (∀ w, |f w| ≤ 1) →
      errorB3 μ (G (k n)) (M n) n f ≤ ε := by
  obtain ⟨ε', hε', hcore⟩ := exists_eventually_mul_abs_integral_le hT hM hbd hε
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  filter_upwards [hcore, eventually_abs_endpointMean_sub_le hT hM hbd hε', hadm,
    hl (eventually_two_mul_le hM), hl (eventually_ge_atTop 1)]
    with n h1 h2 hadmn h2Mn hn1 f hf
  have hM0 : 0 < M n := hM.pos n hn1
  have hMn : M n ≤ n := by omega
  rw [errorB3_eq_mul μ _ hM0 f]
  by_cases hex : ∃ k₀ : ℤ, |(k₀ : ℝ)| ≤ √(a (M n) * a n) ∧
      walkProb μ ((n - M n : ℕ) : ℤ) (-1 - k₀) ≠ 0
  · obtain ⟨k₀, hk₀, hψ₀⟩ := hex
    rw [integral_blockIntegrand_eq μ _ hadmn hMn hf (endpointMean μ (G (k n)) (M n) n f k₀)]
    exact h1 f hf _ (abs_endpointMean_le μ _ _ n hf k₀)
      (fun x hx hψ => h2 f hf x k₀ hx hk₀ hψ hψ₀)
  · rw [integral_blockIntegrand_eq μ _ hadmn hMn hf 0]
    exact h1 f hf 0 (by simp) (fun x hx hψ => absurd ⟨x, hx, hψ⟩ hex)

/-- `b_3` is nonnegative. -/
theorem errorB3_nonneg (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) (f : ℕ → ℝ) :
    0 ≤ errorB3 μ G M n f :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **Proposition `prop:b3bis`** (source lines 1862–1864): for test functions `f_n` with
`‖f_n‖_∞ ≤ 1`, if `(n π_n)` is bounded then `b_3^n → 0` along admissible sizes (periodic offspring
laws included, correction F2). -/
theorem tendsto_errorB3 (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hM : IsCutoff M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C)
    (f : ℕ → ℕ → ℝ) (hf : ∀ n w, |f n w| ≤ 1) :
    Tendsto (fun n => errorB3 μ (G (k n)) (M n) n (f n)) (admissibleSizes μ) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_errorB3_le hT hM hbd (half_pos hε)] with n h
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (errorB3_nonneg μ _ _ n _)]
  exact (h (f n) (hf n)).trans_lt (half_lt_self hε)

end PoissonDeclumping.Bridge
