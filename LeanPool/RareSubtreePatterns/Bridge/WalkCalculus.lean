/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Cyclic.Markov

/-!
# Walk calculus: basic identities, Markov properties and exchangeability

Work package WP1 (remainder) of the bridge plan. Source lines 719–730 (the walk `S_k`), 777–825
(`Ψ_m`), 1641–1645 (Markov property at a deterministic time, proof of Lemma `lem:error_est`),
1720–1728, 1952, 2049 (cyclic exchangeability), 1881 (conditional independence of the blocks
given `S_{M_n}` and `S_n`, proof of Proposition `prop:b3bis`), 2058–2073 (two disjoint blocks,
proof of Lemma `lem:extreme_means`).

`walkProb μ m x = Ψ_m(x) = P(S_m = x)` (`Setup/Walk.lean`), `walkVecLaw μ n` is the law of
`(X_1, …, X_n)` (a product measure on `Fin n → ℤ`), and `bridgeLaw μ n` its conditioning on
`S_n = -1`. Already available upstream (`Cyclic/WalkBridge.lean`): `walkLaw_eq_map_sum`,
`walkProb_natCast`, `walkProb_nonneg`, `walkProb_le_one`, `walkProb_of_neg`, `walkProb_neg_one`
(Dwass), `walkProb_neg_one_pos_iff`, `walkVecLaw_map_split`.

## Main statements

* `walkProb_zero_left`, `hasSum_walkProb`, `summable_walkProb`: `Ψ_0 = δ_0`, `∑_x Ψ_m(x) = 1`.
* `walkProb_add` (Chapman–Kolmogorov): `Ψ_{m+k}(s) = ∑_x Ψ_m(x) Ψ_k(s - x)`.
* `walkVecLaw_take_inter_sum`, `walkVecLaw_real_take_inter_sum` (**Markov property at a
  deterministic time** `m ≤ n`, for an arbitrary event `H` on the first `m` increments):
  `P(H(X_1..X_m), S_n = s) = E[1_{H(X_1..X_m)} Ψ_{n-m}(s - S_m)]`; conditional forms
  `cond_real_take`, `cond_real_take_eq_integral_div` (valid for every endpoint `s`; both sides
  vanish when `Ψ_n(s) = 0`).
* `map_take_walkVecLaw`, `map_drop_walkVecLaw`, `walkVecLaw_take`, `walkVecLaw_drop`: prefix and
  suffix laws; `walkVecLaw_take_inter_drop`: independence of the two blocks.
* `walkVecLaw_take_drop_sum`, `cond_take_drop`, `cond_take_of_take_sum`, `cond_drop_of_take_sum`:
  **conditional independence** of `(X_1..X_m)` and `(X_{m+1}..X_n)` given `S_m = j, S_n = s`,
  with the conditional laws of the two blocks; `integral_cond_take_mul_drop`: the resulting block
  reduction `E[F(X_1..X_m) G(X_{m+1}..X_n) | S_n = s] = E[F(X_1..X_m) h(S_m) | S_n = s]` with
  `h(k) = E[G(X_1..X_{n-m}) | S_{n-m} = s - k]`, for bounded `F`, `G`.
* `walkVecLaw_two_blocks`, `walkVecLaw_two_blocks_inter_sum` and
  `walkVecLaw_real_two_blocks_inter_sum`: two disjoint blocks
  `(X_1..X_{m₁})`, `(X_{j+1}..X_{j+m₂})` (`m₁ ≤ j`, `j + m₂ ≤ n`) are independent, and
  `P(H₁, H₂, S_n = s) = E[1_{H₁} 1_{H₂} Ψ_{n-m₁-m₂}(s - S_{m₁} - S'_{m₂})]`.
* `map_walkVecLaw_rotate`, `map_bridgeLaw_rotate`, `bridgeLaw_rotate`, `walkVecLaw_rotate`:
  **cyclic exchangeability** of the walk and of the bridge; `take_rotate_eq_take_drop`: the
  first `M` entries of the `i`-th cyclic shift are `(x_{i+1}, …, x_{i+M})` when `i + M ≤ n`.
* `uniformFringeLaw_real_mul_walkProb`: Corollary `cor:cyclicshift` in multiplied form,
  `P(𝒯^n_{U_n} ∈ A) Ψ_n(-1) = E[1_{𝒯 ∈ A} Ψ_{n-|𝒯|}(0)]` for every `n`.

The paper's sequences are indexed from `1`; ours from `0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PoissonDeclumping.Bridge

open Lukasiewicz PlaneTree Cyclic

/-! ### Basics -/

theorem walkProb_zero_left (μ : PMF ℕ) (x : ℤ) : walkProb μ 0 x = if x = 0 then 1 else 0 := by
  rw [walkProb, ite_eq_left le_rfl]
  change (Measure.dirac (0 : ℤ)).real {x} = _
  rw [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton x)]
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [Set.indicator_of_notMem (by simpa [eq_comm] using hx), ite_eq_right hx]
    rfl

theorem tsum_walkLaw_singleton (μ : PMF ℕ) (m : ℕ) : ∑' x : ℤ, walkLaw μ m {x} = 1 := by
  have h := Measure.tsum_indicator_apply_singleton (walkLaw μ m) Set.univ MeasurableSet.univ
  simpa only [Set.indicator_univ, measure_univ] using h

theorem hasSum_walkProb (μ : PMF ℕ) (m : ℕ) : HasSum (fun x : ℤ => walkProb μ m x) 1 := by
  have h := ENNReal.hasSum_toReal (f := fun x : ℤ => walkLaw μ m {x})
    (by rw [tsum_walkLaw_singleton]; exact ENNReal.one_ne_top)
  rw [← ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _), tsum_walkLaw_singleton,
    ENNReal.toReal_one] at h
  simpa only [walkProb_natCast_eq_toReal] using h

theorem tsum_walkProb (μ : PMF ℕ) (m : ℕ) : ∑' x : ℤ, walkProb μ m x = 1 :=
  (hasSum_walkProb μ m).tsum_eq

theorem summable_walkProb (μ : PMF ℕ) (m : ℤ) : Summable (walkProb μ m) := by
  rcases lt_or_ge m 0 with hm | hm
  · have h : walkProb μ m = 0 := funext fun x => walkProb_of_neg μ hm x
    rw [h]
    exact summable_zero
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    exact (hasSum_walkProb μ k).summable

/-! ### Chapman–Kolmogorov -/

theorem walkLaw_add_eq_map (μ : PMF ℕ) (m k : ℕ) :
    walkLaw μ (m + k) = ((walkLaw μ m).prod (walkLaw μ k)).map (fun p => p.1 + p.2) := by
  rw [← walkVecLaw_map_sum_pair, Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _), walkLaw_eq_map_sum]
  congr 1
  funext ω
  simp only [Function.comp_apply]
  exact Fin.sum_univ_add ω

theorem walkLaw_add_singleton (μ : PMF ℕ) (m k : ℕ) (s : ℤ) :
    walkLaw μ (m + k) {s} = ∑' x, walkLaw μ m {x} * walkLaw μ k {s - x} := by
  rw [walkLaw_add_eq_map, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _), Measure.prod_apply (Set.to_countable _).measurableSet,
    lintegral_countable']
  refine tsum_congr fun x => ?_
  rw [mul_comm]
  congr 2
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  omega

theorem walkProb_add (μ : PMF ℕ) (m k : ℕ) (s : ℤ) :
    walkProb μ ((m + k : ℕ) : ℤ) s = ∑' x, walkProb μ m x * walkProb μ k (s - x) := by
  simp only [walkProb_natCast_eq_toReal]
  rw [walkLaw_add_singleton, ENNReal.tsum_toReal_eq
    (fun x => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul]

/-! ### Splitting the increments -/

theorem walkVecLaw_eq_map_append (μ : PMF ℕ) (m k : ℕ) :
    walkVecLaw μ (m + k) =
      ((walkVecLaw μ m).prod (walkVecLaw μ k)).map (fun p => Fin.append p.1 p.2) := by
  rw [← walkVecLaw_map_split, Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _)]
  conv_lhs => rw [← Measure.map_id (μ := walkVecLaw μ (m + k))]
  congr 1
  funext ω
  exact Fin.append_castAdd_natAdd.symm

theorem lintegral_walkVecLaw_add (μ : PMF ℕ) (m k : ℕ) (F : (Fin (m + k) → ℤ) → ℝ≥0∞) :
    ∫⁻ ω, F ω ∂walkVecLaw μ (m + k) =
      ∫⁻ a, ∫⁻ b, F (Fin.append a b) ∂walkVecLaw μ k ∂walkVecLaw μ m := by
  rw [walkVecLaw_eq_map_append, lintegral_map (measurable_of_countable _)
    (measurable_of_countable _), lintegral_prod _ (measurable_of_countable _).aemeasurable]

theorem sum_append {m k : ℕ} (a : Fin m → ℤ) (b : Fin k → ℤ) :
    ∑ i, Fin.append a b i = ∑ i, a i + ∑ i, b i := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem take_ofFn_append {m k : ℕ} (a : Fin m → ℤ) (b : Fin k → ℤ) :
    (List.ofFn (Fin.append a b)).take m = List.ofFn a := by
  rw [List.ofFn_fin_append, List.take_left' List.length_ofFn]

theorem drop_ofFn_append {m k : ℕ} (a : Fin m → ℤ) (b : Fin k → ℤ) :
    (List.ofFn (Fin.append a b)).drop m = List.ofFn b := by
  rw [List.ofFn_fin_append, List.drop_left' List.length_ofFn]


/-! ### Markov property at a deterministic time -/

/-- **Markov property at the deterministic time `m`** (source lines 1641–1645), measure form:
`P(H(X_1, …, X_m), S_n = s) = E[1_{H(X_1, …, X_m)} Ψ_{n-m}(s - S_m)]`. -/
theorem walkVecLaw_take_inter_sum (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) (H : List ℤ → Prop)
    (s : ℤ) :
    walkVecLaw μ n {ω | H ((List.ofFn ω).take m) ∧ ∑ i, ω i = s} =
      ∫⁻ a, {a : Fin m → ℤ | H (List.ofFn a)}.indicator
        (fun a => walkLaw μ (n - m) {s - ∑ i, a i}) a ∂walkVecLaw μ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [← lintegral_indicator_one (Set.to_countable _).measurableSet, lintegral_walkVecLaw_add,
    Nat.add_sub_cancel_left]
  refine lintegral_congr fun a => ?_
  by_cases ha : H (List.ofFn a)
  · rw [Set.indicator_of_mem (show a ∈ {a : Fin m → ℤ | H (List.ofFn a)} from ha),
      walkLaw_singleton, ← lintegral_indicator_one (Set.to_countable _).measurableSet]
    refine lintegral_congr fun b => ?_
    have hiff : Fin.append a b ∈ {ω : Fin (m + k) → ℤ | H ((List.ofFn ω).take m) ∧
        ∑ i, ω i = s} ↔ b ∈ {b : Fin k → ℤ | ∑ j, b j = s - ∑ i, a i} := by
      simp only [Set.mem_ofPred_eq, take_ofFn_append, sum_append, ha, true_and]
      omega
    by_cases hb : b ∈ {b : Fin k → ℤ | ∑ j, b j = s - ∑ i, a i}
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (hiff.mpr hb)]
      rfl
    · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (mt hiff.mp hb)]
  · rw [Set.indicator_of_notMem (show a ∉ {a : Fin m → ℤ | H (List.ofFn a)} from ha)]
    refine lintegral_eq_zero_of_ae_eq_zero ?_ |>.trans rfl
    refine Filter.Eventually.of_forall fun b => Set.indicator_of_notMem ?_ _
    simp only [Set.mem_ofPred_eq, take_ofFn_append, ha, false_and, not_false_eq_true]

/-- **Markov property at the deterministic time `m`**, in `ℝ` (source lines 1641–1645):
`P(H(X_1, …, X_m), S_n = s) = E[1_{H(X_1, …, X_m)} Ψ_{n-m}(s - S_m)]` for `m ≤ n`. -/
theorem walkVecLaw_real_take_inter_sum (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n)
    (H : List ℤ → Prop) (s : ℤ) :
    (walkVecLaw μ n).real {ω | H ((List.ofFn ω).take m) ∧ ∑ i, ω i = s} =
      ∫ a, {a : Fin m → ℤ | H (List.ofFn a)}.indicator 1 a *
        walkProb μ ((n - m : ℕ) : ℤ) (s - ∑ i, a i) ∂walkVecLaw μ m := by
  have hfin : ∀ᵐ a ∂walkVecLaw μ m, {a : Fin m → ℤ | H (List.ofFn a)}.indicator
      (fun a => walkLaw μ (n - m) {s - ∑ i, a i}) a < ∞ := by
    refine Filter.Eventually.of_forall fun a => ?_
    by_cases ha : H (List.ofFn a)
    · rw [Set.indicator_of_mem (show a ∈ {a : Fin m → ℤ | H (List.ofFn a)} from ha)]
      exact measure_lt_top _ _
    · rw [Set.indicator_of_notMem (show a ∉ {a : Fin m → ℤ | H (List.ofFn a)} from ha)]
      exact ENNReal.zero_lt_top
  rw [measureReal_def, walkVecLaw_take_inter_sum μ hmn,
    ← integral_toReal (measurable_of_countable _).aemeasurable hfin]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  by_cases ha : H (List.ofFn a)
  · simp only [Set.indicator_of_mem (show a ∈ {a : Fin m → ℤ | H (List.ofFn a)} from ha),
      Pi.one_apply, one_mul, walkProb_natCast_eq_toReal]
  · simp only [Set.indicator_of_notMem (show a ∉ {a : Fin m → ℤ | H (List.ofFn a)} from ha),
      ENNReal.toReal_zero, zero_mul]

/-- **Markov property at the deterministic time `m`, conditional form** (source line 1641):
`P(H(X_1, …, X_m) | S_n = s) = Ψ_n(s)⁻¹ E[1_{H(X_1, …, X_m)} Ψ_{n-m}(s - S_m)]`. It holds for every
endpoint `s`: if `Ψ_n(s) = 0` both sides vanish. -/
theorem cond_real_take (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) (H : List ℤ → Prop) (s : ℤ) :
    (cond (walkVecLaw μ n) {ω | ∑ i, ω i = s}).real {ω | H ((List.ofFn ω).take m)} =
      (walkProb μ n s)⁻¹ * ∫ a, {a : Fin m → ℤ | H (List.ofFn a)}.indicator 1 a *
        walkProb μ ((n - m : ℕ) : ℤ) (s - ∑ i, a i) ∂walkVecLaw μ m := by
  rw [measureReal_def, cond_apply (Set.to_countable _).measurableSet, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, ← walkProb_natCast,
    ← walkVecLaw_real_take_inter_sum μ hmn]
  congr 2
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact and_comm

/-- The paper's form of `cond_real_take`: `E[H(X_1, …, X_m) | S_n = s] =
E[H(X_1, …, X_m) Ψ_{n-m}(s - S_m) / Ψ_n(s)]` (source line 1641). -/
theorem cond_real_take_eq_integral_div (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n)
    (H : List ℤ → Prop) (s : ℤ) :
    (cond (walkVecLaw μ n) {ω | ∑ i, ω i = s}).real {ω | H ((List.ofFn ω).take m)} =
      ∫ a, {a : Fin m → ℤ | H (List.ofFn a)}.indicator 1 a *
        (walkProb μ ((n - m : ℕ) : ℤ) (s - ∑ i, a i) / walkProb μ n s) ∂walkVecLaw μ m := by
  rw [cond_real_take μ hmn, inv_mul_eq_div, ← integral_div]
  simp only [mul_div_assoc]

/-! ### Prefix and suffix laws -/

/-- The law of the first `m` increments `(X_1, …, X_m)` of `(X_1, …, X_n)`, `m ≤ n`. -/
theorem map_take_walkVecLaw (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (walkVecLaw μ n).map (fun ω => toVec m ((List.ofFn ω).take m)) = walkVecLaw μ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have h : (fun ω : Fin (m + k) → ℤ => toVec m ((List.ofFn ω).take m)) =
      Prod.fst ∘ (fun ω : Fin (m + k) → ℤ => ((fun i : Fin m => ω (Fin.castAdd k i)),
        (fun j : Fin k => ω (Fin.natAdd m j)))) := by
    funext ω
    rw [ofFn_eq_append ω, List.take_left' List.length_ofFn, toVec_ofFn]
    rfl
  rw [h, ← Measure.map_map measurable_fst (measurable_of_countable _), walkVecLaw_map_split,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- **Suffix law.** The increments `(X_{m+1}, …, X_n)` after a deterministic time `m ≤ n` have the
law of `(X_1, …, X_{n-m})`. -/
theorem map_drop_walkVecLaw (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (walkVecLaw μ n).map (fun ω => toVec (n - m) ((List.ofFn ω).drop m)) =
      walkVecLaw μ (n - m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_sub_cancel_left]
  have h : (fun ω : Fin (m + k) → ℤ => toVec k ((List.ofFn ω).drop m)) =
      Prod.snd ∘ (fun ω : Fin (m + k) → ℤ => ((fun i : Fin m => ω (Fin.castAdd k i)),
        (fun j : Fin k => ω (Fin.natAdd m j)))) := by
    funext ω
    rw [ofFn_eq_append ω, List.drop_left' List.length_ofFn, toVec_ofFn]
    rfl
  rw [h, ← Measure.map_map measurable_snd (measurable_of_countable _), walkVecLaw_map_split,
    Measure.map_snd_prod, measure_univ, one_smul]

/-- Suffix law, event form: `P(K(X_{m+1}, …, X_n)) = P(K(X_1, …, X_{n-m}))`. -/
theorem walkVecLaw_drop (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) (K : List ℤ → Prop) :
    walkVecLaw μ n {ω | K ((List.ofFn ω).drop m)} =
      walkVecLaw μ (n - m) {b | K (List.ofFn b)} := by
  rw [← map_drop_walkVecLaw μ hmn, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [ofFn_toVec (by simp)]

/-- Prefix law, event form: `P(H(X_1, …, X_m)) = P(H(X_1, …, X_m))` computed in length `n ≥ m`. -/
theorem walkVecLaw_take (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) (H : List ℤ → Prop) :
    walkVecLaw μ n {ω | H ((List.ofFn ω).take m)} = walkVecLaw μ m {a | H (List.ofFn a)} := by
  rw [← map_take_walkVecLaw μ hmn, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [ofFn_toVec (by simp [hmn])]

/-! ### Cyclic exchangeability -/

/-- `toVec n (x.rotate i)` is the coordinate permutation `ω ∘ (finRotate n)^i`. -/
theorem toVec_rotate_ofFn {n : ℕ} (ω : Fin n → ℤ) (i : ℕ) :
    toVec n ((List.ofFn ω).rotate i) = ω ∘ ⇑(finRotate n ^ i) := by
  rw [← ofFn_comp_finRotate_pow, toVec_ofFn]

/-- **Cyclic exchangeability of the walk** (`(X_1, …, X_n)` is invariant under cyclic shifts). -/
theorem map_walkVecLaw_rotate (μ : PMF ℕ) (n i : ℕ) :
    (walkVecLaw μ n).map (fun ω => toVec n ((List.ofFn ω).rotate i)) = walkVecLaw μ n := by
  simp_rw [toVec_rotate_ofFn]
  exact map_walkVecLaw_comp_perm μ _

/-- **Cyclic exchangeability of the bridge** (source lines 1720, 1728, 1952, 2049):
`(X_{i+1}, …, X_n, X_1, …, X_i)` under `P(· | S_n = -1)` has the law of `(X_1, …, X_n)` under
`P(· | S_n = -1)`. -/
theorem map_bridgeLaw_rotate (μ : PMF ℕ) (n i : ℕ) :
    (bridgeLaw μ n).map (fun ω => toVec n ((List.ofFn ω).rotate i)) = bridgeLaw μ n := by
  simp_rw [toVec_rotate_ofFn]
  exact map_bridgeLaw_comp_perm μ _

/-- Cyclic exchangeability of the bridge, event form. -/
theorem bridgeLaw_rotate (μ : PMF ℕ) (n i : ℕ) (P : List ℤ → Prop) :
    bridgeLaw μ n {ω | P ((List.ofFn ω).rotate i)} = bridgeLaw μ n {ω | P (List.ofFn ω)} := by
  conv_rhs => rw [← map_bridgeLaw_rotate μ n i]
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [ofFn_toVec (by simp)]

/-- Cyclic exchangeability of the walk, event form. -/
theorem walkVecLaw_rotate (μ : PMF ℕ) (n i : ℕ) (P : List ℤ → Prop) :
    walkVecLaw μ n {ω | P ((List.ofFn ω).rotate i)} = walkVecLaw μ n {ω | P (List.ofFn ω)} := by
  conv_rhs => rw [← map_walkVecLaw_rotate μ n i]
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [ofFn_toVec (by simp)]

/-- Before the wrap-around, the first `M` entries of a cyclic shift are a contiguous block:
`(x_{i+1}, …, x_{i+M})`. -/
theorem take_rotate_eq_take_drop {α : Type*} {x : List α} {i M : ℕ} (h : i + M ≤ x.length) :
    (x.rotate i).take M = (x.drop i).take M := by
  rw [List.rotate_eq_drop_append_take (by omega), List.take_append_of_le_length (by simp; omega)]


/-! ### Independent blocks, conditionally on the sums (source line 1881) -/

/-- The two blocks `(X_1, …, X_m)` and `(X_{m+1}, …, X_n)` are independent, also jointly with their
sums: `P(H(X_1..X_m), K(X_{m+1}..X_n), S_m = j, S_n = s) =
P(H(X_1..X_m), S_m = j) P(K(X_1..X_{n-m}), S_{n-m} = s - j)`. -/
theorem walkVecLaw_take_drop_sum (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) (H K : List ℤ → Prop)
    (j s : ℤ) :
    walkVecLaw μ n {ω | H ((List.ofFn ω).take m) ∧ K ((List.ofFn ω).drop m) ∧
        ((List.ofFn ω).take m).sum = j ∧ ∑ i, ω i = s} =
      walkVecLaw μ m {a | H (List.ofFn a) ∧ ∑ i, a i = j} *
        walkVecLaw μ (n - m) {b | K (List.ofFn b) ∧ ∑ i, b i = s - j} := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_sub_cancel_left]
  have hset : {ω : Fin (m + k) → ℤ | H ((List.ofFn ω).take m) ∧ K ((List.ofFn ω).drop m) ∧
      ((List.ofFn ω).take m).sum = j ∧ ∑ i, ω i = s} =
      (fun ω : Fin (m + k) → ℤ => ((fun i : Fin m => ω (Fin.castAdd k i)),
        (fun j : Fin k => ω (Fin.natAdd m j)))) ⁻¹'
        ({a | H (List.ofFn a) ∧ ∑ i, a i = j} ×ˢ {b | K (List.ofFn b) ∧ ∑ i, b i = s - j}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod]
    rw [ofFn_eq_append ω, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn,
      Fin.sum_univ_add, List.sum_ofFn]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h3⟩, h2, by omega⟩
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩
      exact ⟨h1, h2, h3, by omega⟩
  rw [hset, ← Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    walkVecLaw_map_split, Measure.prod_prod]

/-- `P(S_m = j, S_n = s) = Ψ_m(j) Ψ_{n-m}(s - j)`, in `ℝ≥0∞`. -/
theorem walkVecLaw_take_sum_sum (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) (j s : ℤ) :
    walkVecLaw μ n {ω | ((List.ofFn ω).take m).sum = j ∧ ∑ i, ω i = s} =
      walkLaw μ m {j} * walkLaw μ (n - m) {s - j} := by
  have h := walkVecLaw_take_drop_sum μ hmn (fun _ => True) (fun _ => True) j s
  simp only [true_and] at h
  rw [h, walkLaw_singleton, walkLaw_singleton]

/-- **Conditional independence of the blocks given `S_m` and `S_n`** (source line 1881):
under `P(· | S_m = j, S_n = s)`, the blocks `(X_1, …, X_m)` and `(X_{m+1}, …, X_n)` are
independent, with the laws of `(X_1, …, X_m)` given `S_m = j` and of `(X_1, …, X_{n-m})` given
`S_{n-m} = s - j`. (All three conditional laws are `0` when the conditioning event is null.) -/
theorem cond_take_drop (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) (H K : List ℤ → Prop) (j s : ℤ) :
    cond (walkVecLaw μ n) {ω | ((List.ofFn ω).take m).sum = j ∧ ∑ i, ω i = s}
        {ω | H ((List.ofFn ω).take m) ∧ K ((List.ofFn ω).drop m)} =
      cond (walkVecLaw μ m) {a | ∑ i, a i = j} {a | H (List.ofFn a)} *
        cond (walkVecLaw μ (n - m)) {b | ∑ i, b i = s - j} {b | K (List.ofFn b)} := by
  have h1 := walkVecLaw_take_drop_sum μ hmn H K j s
  have h2 := walkVecLaw_take_drop_sum μ hmn (fun _ => True) (fun _ => True) j s
  simp only [true_and] at h2
  rw [cond_apply (Set.to_countable _).measurableSet, cond_apply (Set.to_countable _).measurableSet,
    cond_apply (Set.to_countable _).measurableSet, h2]
  have e1 : {ω : Fin n → ℤ | ((List.ofFn ω).take m).sum = j ∧ ∑ i, ω i = s} ∩
      {ω | H ((List.ofFn ω).take m) ∧ K ((List.ofFn ω).drop m)} =
      {ω | H ((List.ofFn ω).take m) ∧ K ((List.ofFn ω).drop m) ∧
        ((List.ofFn ω).take m).sum = j ∧ ∑ i, ω i = s} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  have e2 : {a : Fin m → ℤ | ∑ i, a i = j} ∩ {a | H (List.ofFn a)} =
      {a | H (List.ofFn a) ∧ ∑ i, a i = j} := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  have e3 : {b : Fin (n - m) → ℤ | ∑ i, b i = s - j} ∩ {b | K (List.ofFn b)} =
      {b | K (List.ofFn b) ∧ ∑ i, b i = s - j} := by
    ext b
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  rw [e1, e2, e3, h1, ENNReal.mul_inv (Or.inr (measure_ne_top _ _)) (Or.inl (measure_ne_top _ _)),
    mul_mul_mul_comm]

/-- Under `P(· | S_m = j, S_n = s)`, the first block has the law of `(X_1, …, X_m)` given
`S_m = j`. -/
theorem cond_take_of_take_sum (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) (H : List ℤ → Prop)
    (j s : ℤ) (hs : walkLaw μ (n - m) {s - j} ≠ 0) :
    cond (walkVecLaw μ n) {ω | ((List.ofFn ω).take m).sum = j ∧ ∑ i, ω i = s}
        {ω | H ((List.ofFn ω).take m)} =
      cond (walkVecLaw μ m) {a | ∑ i, a i = j} {a | H (List.ofFn a)} := by
  have h := cond_take_drop μ hmn H (fun _ => True) j s
  simp only [and_true, Set.ofPred_true] at h
  have hu : cond (walkVecLaw μ (n - m)) {b | ∑ i, b i = s - j} Set.univ = 1 := by
    rw [cond_apply (Set.to_countable _).measurableSet, Set.inter_univ, ← walkLaw_singleton,
      ENNReal.inv_mul_cancel hs (measure_ne_top _ _)]
  rw [h, hu, mul_one]

/-- Under `P(· | S_m = j, S_n = s)`, the second block has the law of `(X_1, …, X_{n-m})` given
`S_{n-m} = s - j`. -/
theorem cond_drop_of_take_sum (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) (K : List ℤ → Prop)
    (j s : ℤ) (hj : walkLaw μ m {j} ≠ 0) :
    cond (walkVecLaw μ n) {ω | ((List.ofFn ω).take m).sum = j ∧ ∑ i, ω i = s}
        {ω | K ((List.ofFn ω).drop m)} =
      cond (walkVecLaw μ (n - m)) {b | ∑ i, b i = s - j} {b | K (List.ofFn b)} := by
  have h := cond_take_drop μ hmn (fun _ => True) K j s
  simp only [true_and, Set.ofPred_true] at h
  have hu : cond (walkVecLaw μ m) {a | ∑ i, a i = j} Set.univ = 1 := by
    rw [cond_apply (Set.to_countable _).measurableSet, Set.inter_univ, ← walkLaw_singleton,
      ENNReal.inv_mul_cancel hj (measure_ne_top _ _)]
  rw [h, hu, one_mul]

/-! ### Integrals of bounded functions of the blocks -/

theorem abs_indicator_le_of_abs_le {α : Type*} {s : Set α} {f : α → ℝ} {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) (x : α) : |s.indicator f x| ≤ C := by
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    exact hf x
  · rw [Set.indicator_of_notMem hx, abs_zero]
    exact (abs_nonneg _).trans (hf x)

/-- Fubini for bounded functions of `(X_1, …, X_{m+k})`. -/
theorem integral_walkVecLaw_add (μ : PMF ℕ) (m k : ℕ) (Φ : (Fin (m + k) → ℤ) → ℝ) {C : ℝ}
    (hΦ : ∀ ω, |Φ ω| ≤ C) :
    ∫ ω, Φ ω ∂walkVecLaw μ (m + k) =
      ∫ a, ∫ b, Φ (Fin.append a b) ∂walkVecLaw μ k ∂walkVecLaw μ m := by
  rw [walkVecLaw_eq_map_append, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  refine integral_prod _ (Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => ?_))
  rw [Real.norm_eq_abs]
  exact hΦ _

/-- `E[G(X_1, …, X_k); S_k = t] = Ψ_k(t) E[G(X_1, …, X_k) | S_k = t]` (both sides vanish if
`Ψ_k(t) = 0`). -/
theorem integral_indicator_sum_eq (μ : PMF ℕ) (k : ℕ) (G : (Fin k → ℤ) → ℝ) (t : ℤ) :
    ∫ b, {b : Fin k → ℤ | ∑ i, b i = t}.indicator G b ∂walkVecLaw μ k =
      walkProb μ k t * ∫ b, G b ∂cond (walkVecLaw μ k) {b | ∑ i, b i = t} := by
  rw [integral_indicator (Set.to_countable _).measurableSet, ProbabilityTheory.cond,
    integral_smul_measure,
    walkProb_natCast, smul_eq_mul, ENNReal.toReal_inv, ← measureReal_def]
  by_cases h0 : (walkVecLaw μ k).real {b | ∑ i, b i = t} = 0
  · have h0' : walkVecLaw μ k {b | ∑ i, b i = t} = 0 := (measureReal_eq_zero_iff).mp h0
    rw [Measure.restrict_eq_zero.mpr h0', integral_zero_measure, h0, zero_mul]
  · rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]

/-- `∫ f d P(· | S) = P(S)⁻¹ ∫ 1_S f dP`, in `ℝ`. -/
theorem integral_cond_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {S : Set Ω}
    (hS : MeasurableSet S) (f : Ω → ℝ) :
    ∫ x, f x ∂cond P S = (P.real S)⁻¹ * ∫ x, S.indicator f x ∂P := by
  rw [ProbabilityTheory.cond, integral_smul_measure, integral_indicator hS, smul_eq_mul,
    ENNReal.toReal_inv, measureReal_def]

private theorem integral_cond_take_mul_drop_aux (μ : PMF ℕ) (m k : ℕ) (s : ℤ)
    (F G : List ℤ → ℝ) {CF CG : ℝ} (hF : ∀ x, |F x| ≤ CF) (hG : ∀ x, |G x| ≤ CG) :
    ∫ ω, F ((List.ofFn ω).take m) * G ((List.ofFn ω).drop m)
        ∂cond (walkVecLaw μ (m + k)) {ω | ∑ i, ω i = s} =
      ∫ ω, F ((List.ofFn ω).take m) *
        (∫ b, G (List.ofFn b) ∂cond (walkVecLaw μ k)
          {b | ∑ i, b i = s - ((List.ofFn ω).take m).sum})
        ∂cond (walkVecLaw μ (m + k)) {ω | ∑ i, ω i = s} := by
  have hCG : 0 ≤ CG := (abs_nonneg _).trans (hG [])
  have hCF : 0 ≤ CF := (abs_nonneg _).trans (hF [])
  have hh : ∀ t : ℤ, |∫ b, G (List.ofFn b) ∂cond (walkVecLaw μ k)
      {b : Fin k → ℤ | ∑ i, b i = t}| ≤ CG := by
    intro t
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := CG)
      (Filter.Eventually.of_forall fun b => ?_)).trans ?_
    · rw [Real.norm_eq_abs]
      exact hG _
    · exact mul_le_of_le_one_right hCG measureReal_le_one
  have hS : MeasurableSet {ω : Fin (m + k) → ℤ | ∑ i, ω i = s} :=
    (Set.to_countable _).measurableSet
  rw [integral_cond_eq _ hS, integral_cond_eq _ hS]
  congr 1
  rw [integral_walkVecLaw_add μ m k _ (C := CF * CG) (abs_indicator_le_of_abs_le fun ω => by
      rw [abs_mul]
      exact mul_le_mul (hF _) (hG _) (abs_nonneg _) hCF)]
  rw [integral_walkVecLaw_add μ m k _ (C := CF * CG) (abs_indicator_le_of_abs_le fun ω => by
      rw [abs_mul]
      exact mul_le_mul (hF _) (hh _) (abs_nonneg _) hCF)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  have hL : ∀ b : Fin k → ℤ, {ω : Fin (m + k) → ℤ | ∑ i, ω i = s}.indicator
      (fun ω => F ((List.ofFn ω).take m) * G ((List.ofFn ω).drop m)) (Fin.append a b) =
      F (List.ofFn a) * {b : Fin k → ℤ | ∑ i, b i = s - ∑ i, a i}.indicator
        (fun b => G (List.ofFn b)) b := by
    intro b
    by_cases hb : ∑ i, b i = s - ∑ i, a i
    · rw [Set.indicator_of_mem (show Fin.append a b ∈ {ω : Fin (m + k) → ℤ | ∑ i, ω i = s} by
        simp only [Set.mem_ofPred_eq, sum_append]; omega),
        Set.indicator_of_mem (show b ∈ {b : Fin k → ℤ | ∑ i, b i = s - ∑ i, a i} from hb),
        take_ofFn_append, drop_ofFn_append]
    · rw [Set.indicator_of_notMem (show Fin.append a b ∉ {ω : Fin (m + k) → ℤ | ∑ i, ω i = s} by
        simp only [Set.mem_ofPred_eq, sum_append]; omega),
        Set.indicator_of_notMem (show b ∉ {b : Fin k → ℤ | ∑ i, b i = s - ∑ i, a i} from hb),
        mul_zero]
  have hR : ∀ b : Fin k → ℤ, {ω : Fin (m + k) → ℤ | ∑ i, ω i = s}.indicator
      (fun ω => F ((List.ofFn ω).take m) * ∫ b, G (List.ofFn b) ∂cond (walkVecLaw μ k)
        {b | ∑ i, b i = s - ((List.ofFn ω).take m).sum}) (Fin.append a b) =
      (F (List.ofFn a) * ∫ b, G (List.ofFn b) ∂cond (walkVecLaw μ k)
        {b | ∑ i, b i = s - ∑ i, a i}) *
        {b : Fin k → ℤ | ∑ i, b i = s - ∑ i, a i}.indicator 1 b := by
    intro b
    by_cases hb : ∑ i, b i = s - ∑ i, a i
    · rw [Set.indicator_of_mem (show Fin.append a b ∈ {ω : Fin (m + k) → ℤ | ∑ i, ω i = s} by
        simp only [Set.mem_ofPred_eq, sum_append]; omega),
        Set.indicator_of_mem (show b ∈ {b : Fin k → ℤ | ∑ i, b i = s - ∑ i, a i} from hb),
        take_ofFn_append, List.sum_ofFn, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem (show Fin.append a b ∉ {ω : Fin (m + k) → ℤ | ∑ i, ω i = s} by
        simp only [Set.mem_ofPred_eq, sum_append]; omega),
        Set.indicator_of_notMem (show b ∉ {b : Fin k → ℤ | ∑ i, b i = s - ∑ i, a i} from hb),
        mul_zero]
  simp only [hL, hR]
  rw [integral_const_mul, integral_const_mul, integral_indicator_sum_eq,
    integral_indicator_one (Set.to_countable _).measurableSet, ← walkProb_natCast]
  ring

/-- **Block reduction under the endpoint conditioning** (the computation of source line 1881):
for bounded `F`, `G` and `m ≤ n`,
`E[F(X_1..X_m) G(X_{m+1}..X_n) | S_n = s] = E[F(X_1..X_m) h(S_m) | S_n = s]`, where
`h(k) = E[G(X_1..X_{n-m}) | S_{n-m} = s - k]`. -/
theorem integral_cond_take_mul_drop (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) (s : ℤ)
    (F G : List ℤ → ℝ) {CF CG : ℝ} (hF : ∀ x, |F x| ≤ CF) (hG : ∀ x, |G x| ≤ CG) :
    ∫ ω, F ((List.ofFn ω).take m) * G ((List.ofFn ω).drop m)
        ∂cond (walkVecLaw μ n) {ω | ∑ i, ω i = s} =
      ∫ ω, F ((List.ofFn ω).take m) *
        (∫ b, G (List.ofFn b) ∂cond (walkVecLaw μ (n - m))
          {b | ∑ i, b i = s - ((List.ofFn ω).take m).sum})
        ∂cond (walkVecLaw μ n) {ω | ∑ i, ω i = s} := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_sub_cancel_left]
  exact integral_cond_take_mul_drop_aux μ m k s F G hF hG


/-! ### Two disjoint blocks (plan WP1.5, source lines 2058–2073) -/

/-- Independence of a prefix block and the following increments:
`P(H(X_1..X_m), K(X_{m+1}..X_n)) = P(H(X_1..X_m)) P(K(X_1..X_{n-m}))`. -/
theorem walkVecLaw_take_inter_drop (μ : PMF ℕ) {m n : ℕ} (hmn : m ≤ n) (H K : List ℤ → Prop) :
    walkVecLaw μ n {ω | H ((List.ofFn ω).take m) ∧ K ((List.ofFn ω).drop m)} =
      walkVecLaw μ m {a | H (List.ofFn a)} * walkVecLaw μ (n - m) {b | K (List.ofFn b)} := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_sub_cancel_left]
  have hset : {ω : Fin (m + k) → ℤ | H ((List.ofFn ω).take m) ∧ K ((List.ofFn ω).drop m)} =
      (fun ω : Fin (m + k) → ℤ => ((fun i : Fin m => ω (Fin.castAdd k i)),
        (fun j : Fin k => ω (Fin.natAdd m j)))) ⁻¹'
        ({a | H (List.ofFn a)} ×ˢ {b | K (List.ofFn b)}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod]
    rw [ofFn_eq_append ω, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]
  rw [hset, ← Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    walkVecLaw_map_split, Measure.prod_prod]

/-- **Independence of two disjoint blocks** (source lines 2058, 2073): for `m₁ ≤ j` and
`j + m₂ ≤ n`,
`P(H₁(X_1..X_{m₁}), H₂(X_{j+1}..X_{j+m₂})) = P(H₁(X_1..X_{m₁})) P(H₂(X_1..X_{m₂}))`. -/
theorem walkVecLaw_two_blocks (μ : PMF ℕ) {m₁ j m₂ n : ℕ} (hj : m₁ ≤ j) (hn : j + m₂ ≤ n)
    (H₁ H₂ : List ℤ → Prop) :
    walkVecLaw μ n {ω | H₁ ((List.ofFn ω).take m₁) ∧ H₂ (((List.ofFn ω).drop j).take m₂)} =
      walkVecLaw μ m₁ {a | H₁ (List.ofFn a)} * walkVecLaw μ m₂ {c | H₂ (List.ofFn c)} := by
  obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h := walkVecLaw_take_inter_drop μ (show m₁ ≤ n by omega) H₁
    (fun y => H₂ ((y.drop g).take m₂))
  simp only [List.drop_drop] at h
  rw [h, walkVecLaw_drop μ (show g ≤ n - m₁ by omega) (fun y => H₂ (y.take m₂)),
    walkVecLaw_take μ (show m₂ ≤ n - m₁ - g by omega)]

theorem ofFn_append_append_append {a₁ a₂ a₃ a₄ : ℕ} (a : Fin a₁ → ℤ) (b : Fin a₂ → ℤ)
    (c : Fin a₃ → ℤ) (d : Fin a₄ → ℤ) :
    List.ofFn (Fin.append (Fin.append (Fin.append a b) c) d) =
      (List.ofFn a ++ List.ofFn b) ++ (List.ofFn c ++ List.ofFn d) := by
  simp only [List.ofFn_fin_append, List.append_assoc]

/-- **Markov property for two disjoint blocks** (plan WP1.5; source lines 2058–2065): for
`m₁ ≤ j` and `j + m₂ ≤ n`,
`P(H₁(X_1..X_{m₁}), H₂(X_{j+1}..X_{j+m₂}), S_n = s) =
E[1_{H₁(X)} 1_{H₂(X')} Ψ_{n-m₁-m₂}(s - S_{m₁} - S'_{m₂})]`, with `X`, `X'` independent copies of
the increments (the remaining `n - m₁ - m₂` increments form a fresh walk). -/
theorem walkVecLaw_two_blocks_inter_sum (μ : PMF ℕ) {m₁ j m₂ n : ℕ} (hj : m₁ ≤ j)
    (hn : j + m₂ ≤ n) (H₁ H₂ : List ℤ → Prop) (s : ℤ) :
    walkVecLaw μ n {ω | H₁ ((List.ofFn ω).take m₁) ∧ H₂ (((List.ofFn ω).drop j).take m₂) ∧
        ∑ i, ω i = s} =
      ∫⁻ a, ∫⁻ c, {a : Fin m₁ → ℤ | H₁ (List.ofFn a)}.indicator (fun a =>
        {c : Fin m₂ → ℤ | H₂ (List.ofFn c)}.indicator (fun c =>
          walkLaw μ (n - m₁ - m₂) {s - ∑ i, a i - ∑ i, c i}) c) a
        ∂walkVecLaw μ m₂ ∂walkVecLaw μ m₁ := by
  obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le hj
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show m₁ + g + m₂ + r - m₁ - m₂ = g + r by omega]
  have hconv : ∀ t : ℤ, ∫⁻ b, ∫⁻ d, {e : Fin (g + r) → ℤ | ∑ i, e i = t}.indicator 1
      (Fin.append b d) ∂walkVecLaw μ r ∂walkVecLaw μ g = walkLaw μ (g + r) {t} := by
    intro t
    rw [← lintegral_walkVecLaw_add, lintegral_indicator_one (Set.to_countable _).measurableSet,
      walkLaw_singleton]
  rw [← lintegral_indicator_one (Set.to_countable _).measurableSet,
    lintegral_walkVecLaw_add μ (m₁ + g + m₂) r, lintegral_walkVecLaw_add μ (m₁ + g) m₂,
    lintegral_walkVecLaw_add μ m₁ g]
  refine lintegral_congr fun a => ?_
  rw [lintegral_lintegral_swap (measurable_of_countable _).aemeasurable]
  refine lintegral_congr fun c => ?_
  have hmem : ∀ (b : Fin g → ℤ) (d : Fin r → ℤ),
      Fin.append (Fin.append (Fin.append a b) c) d ∈ {ω : Fin (m₁ + g + m₂ + r) → ℤ |
        H₁ ((List.ofFn ω).take m₁) ∧ H₂ (((List.ofFn ω).drop (m₁ + g)).take m₂) ∧
          ∑ i, ω i = s} ↔
        H₁ (List.ofFn a) ∧ H₂ (List.ofFn c) ∧
          Fin.append b d ∈ {e : Fin (g + r) → ℤ | ∑ i, e i = s - ∑ i, a i - ∑ i, c i} := by
    intro b d
    simp only [Set.mem_ofPred_eq, ofFn_append_append_append, sum_append]
    rw [List.take_append_of_le_length (by simp), List.take_left' List.length_ofFn,
      List.drop_left' (by simp), List.take_left' List.length_ofFn]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by omega⟩
  by_cases ha : H₁ (List.ofFn a)
  · rw [Set.indicator_of_mem (show a ∈ {a : Fin m₁ → ℤ | H₁ (List.ofFn a)} from ha)]
    by_cases hc : H₂ (List.ofFn c)
    · rw [Set.indicator_of_mem (show c ∈ {c : Fin m₂ → ℤ | H₂ (List.ofFn c)} from hc), ← hconv]
      refine lintegral_congr fun b => lintegral_congr fun d => ?_
      by_cases hbd : Fin.append b d ∈
          {e : Fin (g + r) → ℤ | ∑ i, e i = s - ∑ i, a i - ∑ i, c i}
      · rw [Set.indicator_of_mem hbd, Set.indicator_of_mem ((hmem b d).mpr ⟨ha, hc, hbd⟩)]
        rfl
      · rw [Set.indicator_of_notMem hbd,
          Set.indicator_of_notMem (fun h => hbd ((hmem b d).mp h).2.2)]
    · rw [Set.indicator_of_notMem (show c ∉ {c : Fin m₂ → ℤ | H₂ (List.ofFn c)} from hc)]
      have h0 : ∀ (b : Fin g → ℤ) (d : Fin r → ℤ), {ω : Fin (m₁ + g + m₂ + r) → ℤ |
          H₁ ((List.ofFn ω).take m₁) ∧ H₂ (((List.ofFn ω).drop (m₁ + g)).take m₂) ∧
            ∑ i, ω i = s}.indicator (1 : (Fin (m₁ + g + m₂ + r) → ℤ) → ℝ≥0∞)
            (Fin.append (Fin.append (Fin.append a b) c) d) = 0 :=
        fun b d => Set.indicator_of_notMem (fun h => hc ((hmem b d).mp h).2.1) _
      refine (lintegral_congr fun b => ?_).trans lintegral_zero
      refine (lintegral_congr fun d => ?_).trans lintegral_zero
      exact h0 b d
  · rw [Set.indicator_of_notMem (show a ∉ {a : Fin m₁ → ℤ | H₁ (List.ofFn a)} from ha)]
    have h0 : ∀ (b : Fin g → ℤ) (d : Fin r → ℤ), {ω : Fin (m₁ + g + m₂ + r) → ℤ |
        H₁ ((List.ofFn ω).take m₁) ∧ H₂ (((List.ofFn ω).drop (m₁ + g)).take m₂) ∧
          ∑ i, ω i = s}.indicator (1 : (Fin (m₁ + g + m₂ + r) → ℤ) → ℝ≥0∞)
            (Fin.append (Fin.append (Fin.append a b) c) d) = 0 :=
      fun b d => Set.indicator_of_notMem (fun h => ha ((hmem b d).mp h).1) _
    refine (lintegral_congr fun b => ?_).trans lintegral_zero
    refine (lintegral_congr fun d => ?_).trans lintegral_zero
    exact h0 b d


/-- **Markov property for two disjoint blocks**, in `ℝ` (plan WP1.5; source lines 2058–2065):
for `m₁ ≤ j` and `j + m₂ ≤ n`,
`P(H₁(X_1..X_{m₁}), H₂(X_{j+1}..X_{j+m₂}), S_n = s) =
E[1_{H₁(X)} 1_{H₂(X')} Ψ_{n-m₁-m₂}(s - S_{m₁} - S'_{m₂})]` for independent copies `X`, `X'`. -/
theorem walkVecLaw_real_two_blocks_inter_sum (μ : PMF ℕ) {m₁ j m₂ n : ℕ} (hj : m₁ ≤ j)
    (hn : j + m₂ ≤ n) (H₁ H₂ : List ℤ → Prop) (s : ℤ) :
    (walkVecLaw μ n).real {ω | H₁ ((List.ofFn ω).take m₁) ∧
        H₂ (((List.ofFn ω).drop j).take m₂) ∧ ∑ i, ω i = s} =
      ∫ a, ∫ c, {a : Fin m₁ → ℤ | H₁ (List.ofFn a)}.indicator 1 a *
        {c : Fin m₂ → ℤ | H₂ (List.ofFn c)}.indicator 1 c *
          walkProb μ ((n - m₁ - m₂ : ℕ) : ℤ) (s - ∑ i, a i - ∑ i, c i)
        ∂walkVecLaw μ m₂ ∂walkVecLaw μ m₁ := by
  rw [measureReal_def, walkVecLaw_two_blocks_inter_sum μ hj hn]
  have hF1 : ∀ (a : Fin m₁ → ℤ) (c : Fin m₂ → ℤ),
      {a : Fin m₁ → ℤ | H₁ (List.ofFn a)}.indicator (fun a =>
        {c : Fin m₂ → ℤ | H₂ (List.ofFn c)}.indicator (fun c =>
          walkLaw μ (n - m₁ - m₂) {s - ∑ i, a i - ∑ i, c i}) c) a ≤ 1 := by
    intro a c
    refine (Set.indicator_le_self _ _ a).trans ?_
    exact (Set.indicator_le_self _ _ c).trans prob_le_one
  have hin : ∀ a : Fin m₁ → ℤ, ∫⁻ c, {a : Fin m₁ → ℤ | H₁ (List.ofFn a)}.indicator (fun a =>
      {c : Fin m₂ → ℤ | H₂ (List.ofFn c)}.indicator (fun c =>
        walkLaw μ (n - m₁ - m₂) {s - ∑ i, a i - ∑ i, c i}) c) a ∂walkVecLaw μ m₂ ≤ 1 := by
    intro a
    refine (lintegral_mono (hF1 a)).trans ?_
    rw [lintegral_const, measure_univ, mul_one]
  rw [← integral_toReal (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall fun a => (hin a).trans_lt ENNReal.one_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  beta_reduce
  rw [← integral_toReal (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall fun c => (hF1 a c).trans_lt ENNReal.one_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  beta_reduce
  by_cases ha : H₁ (List.ofFn a)
  · rw [Set.indicator_of_mem (show a ∈ {a : Fin m₁ → ℤ | H₁ (List.ofFn a)} from ha),
      Set.indicator_of_mem (show a ∈ {a : Fin m₁ → ℤ | H₁ (List.ofFn a)} from ha)]
    by_cases hc : H₂ (List.ofFn c)
    · rw [Set.indicator_of_mem (show c ∈ {c : Fin m₂ → ℤ | H₂ (List.ofFn c)} from hc),
        Set.indicator_of_mem (show c ∈ {c : Fin m₂ → ℤ | H₂ (List.ofFn c)} from hc),
        Pi.one_apply, Pi.one_apply, one_mul, one_mul, walkProb_natCast_eq_toReal]
    · rw [Set.indicator_of_notMem (show c ∉ {c : Fin m₂ → ℤ | H₂ (List.ofFn c)} from hc),
        Set.indicator_of_notMem (show c ∉ {c : Fin m₂ → ℤ | H₂ (List.ofFn c)} from hc),
        ENNReal.toReal_zero, mul_zero, zero_mul]
  · rw [Set.indicator_of_notMem (show a ∉ {a : Fin m₁ → ℤ | H₁ (List.ofFn a)} from ha),
      Set.indicator_of_notMem (show a ∉ {a : Fin m₁ → ℤ | H₁ (List.ofFn a)} from ha),
      ENNReal.toReal_zero, zero_mul, zero_mul]

/-! ### Corollary `cor:cyclicshift` in multiplied form (plan WP1.8) -/

/-- **Corollary `cor:cyclicshift`, multiplied form** (source lines 783–824), valid for every `n`
(both sides vanish at inadmissible `n`):
`P(𝒯^n_{U_n} ∈ A) Ψ_n(-1) = E[1_{𝒯 ∈ A} Ψ_{n-|𝒯|}(0)]`. -/
theorem uniformFringeLaw_real_mul_walkProb (μ : PMF ℕ) (n : ℕ) (A : Set PlaneTree) :
    (uniformFringeLaw μ n).real A * walkProb μ n (-1) =
      ∫ T, A.indicator (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T ∂bienayme μ := by
  have hE : uniformFringeLaw μ n A * walkVecLaw μ n {ω | ∑ i, ω i = -1} =
      walkVecLaw μ n ({ω | ∑ i, ω i = -1} ∩ {ω | ∃ T ∈ A, ofSeq (List.ofFn ω) = some T}) := by
    rw [← bridgeLaw_ofSeq_mem, bridgeLaw, cond_apply (Set.to_countable _).measurableSet]
    by_cases h0 : walkVecLaw μ n {ω | ∑ i, ω i = -1} = 0
    · rw [h0, mul_zero]
      exact (measure_mono_null Set.inter_subset_left h0).symm
    · rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]
  have hfin : ∀ᵐ T ∂bienayme μ, A.indicator
      (fun T => if T.vertexCount ≤ n then walkLaw μ (n - T.vertexCount) {0} else 0) T < ∞ := by
    refine Filter.Eventually.of_forall fun T => ?_
    by_cases hT : T ∈ A
    · rw [Set.indicator_of_mem hT]
      split_ifs
      · exact measure_lt_top _ _
      · exact ENNReal.zero_lt_top
    · rw [Set.indicator_of_notMem hT]
      exact ENNReal.zero_lt_top
  have hint : ∫ T, A.indicator (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T ∂bienayme μ =
      (∫⁻ T, A.indicator (fun T => if T.vertexCount ≤ n then walkLaw μ (n - T.vertexCount) {0}
        else 0) T ∂bienayme μ).toReal := by
    rw [← integral_toReal Measurable.of_discrete.aemeasurable hfin]
    refine integral_congr_ae (Filter.Eventually.of_forall fun T => ?_)
    beta_reduce
    by_cases hT : T ∈ A
    · rw [Set.indicator_of_mem hT, Set.indicator_of_mem hT, walkProb_natCast_sub]
    · rw [Set.indicator_of_notMem hT, Set.indicator_of_notMem hT, ENNReal.toReal_zero]
  rw [hint, ← walkVecLaw_bridge_inter_ofSeq, ← hE, ENNReal.toReal_mul, ← measureReal_def,
    ← measureReal_def, walkProb_natCast]

end PoissonDeclumping.Bridge
