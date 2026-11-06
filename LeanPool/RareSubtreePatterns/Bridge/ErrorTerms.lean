/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bridge.Truncation

import LeanPool.RareSubtreePatterns.ChenStein.AGG

/-!
# The Chen–Stein error terms `b_1` and `b_2`: Proposition `prop:b1` and Lemma `lem:boundb2`

Work package WP5 of the bridge plan. Source lines 1615–1619 and 1709–1725 (the Chen–Stein
setting), 1797–1807 (Proposition 4.6) and 1815–1857 (Lemma 4.7, `P11`, audit finding 5).

The indicators are `I_{i+1}^{(M)}(X_1, …, X_n) = 1_{cycEvent G M n i}` (`0`-based `i : Fin n`)
on the probability space `(Fin n → ℤ, P(· | S_n = -1))`, and the neighbourhoods are
`B_i = cycNbhd n M i = {j : |i - j|_cyc < M}`. The error terms `errorB1`, `errorB2`, `errorB3`
are literally the three sums of `ChenStein.prop_AGG` for `P = bridgeLaw μ n`,
`E = cycEvent G M n`, `B = cycNbhd n M`; `b_3` is only defined here (it is bounded in the
endpoint-smoothing package).

## Main statements

* `cycDist`, `cycNbhd`, `mem_cycNbhd_self`, `card_cycNbhd_le` (`|B_i| ≤ 2M`), `cycGap` and
  `cycGap_mem_Icc_or` (bookkeeping of cyclic gaps).
* `cycEvent`, `errorB1`, `errorB2`, `errorB3`; `bridgeLaw_real_cycEvent` (`P(E_i) = q`),
  `sum_bridgeLaw_real_cycEvent` (`∑ P(E_i) = n q`), `cyclicSum_ofFn_eq_sum_indicator`
  (`W_n^M = ∑ 1_{E_i}`).
* `exists_paperTVDist_cyclicSum_le_errorTerms`: Proposition `prop:AGG` instantiated,
  `d_TV(W_n^M, Po(n q)) ≤ 2 (b_1 + b_2 + b_3(f))` for some `‖f‖_∞ ≤ 1`.
* `errorB1_le`, `tendsto_mul_two_mul_cutoff_mul_qProb_sq`, `tendsto_errorB1`
  (**Proposition `prop:b1`**): `b_1 ≤ n · 2M_n · q_n² → 0` for bounded `n π_n`.
* `bridgeLaw_real_cycEvent_inter`, `errorB2_le` (cyclic exchangeability:
  `b_2 ≤ 2n ∑_{ℓ=1}^{M-1} P(I_1 I_{1+ℓ} | S_n = -1)`), `firstMarked_pair_take_iff` (locality of
  the pair in the first `2M` increments), `tendsto_errorB2` (**Lemma `lem:boundb2`**).

The pair at cyclic distance `ℓ < M_n` sits at forward gap `ℓ` or `n - ℓ`; both are reduced to
gap `ℓ` by rotating the cycle (`cycGap_mem_Icc_or`, `bridgeLaw_real_cycEvent_inter`), so only
`P(I_1 I_{1+ℓ} | S_n = -1)` with `1 ≤ ℓ ≤ M_n - 1` is bounded, by Lemma `lem:error_est` on the
first `2 M_n` increments and the two-start bound of `Bridge/PairBound.lean`.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping.Bridge

open Lukasiewicz PlaneTree Cyclic

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

/-! ### Cyclic distance and neighbourhoods -/

/-- The cyclic distance `|i - j|_cyc = min(|i - j|, n - |i - j|)` (source lines 1617, 1715),
with `|i - j| = max i j - min i j`. -/
def cycDist (n i j : ℕ) : ℕ := min (max i j - min i j) (n - (max i j - min i j))

/-- The Chen–Stein neighbourhood `B_i = {j ∈ [n] : |i - j|_cyc < M}` (source lines 1617, 1715),
with `0`-based indices `Fin n`. -/
def cycNbhd (n M : ℕ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j : Fin n => cycDist n i j < M

theorem mem_cycNbhd {n M : ℕ} {i j : Fin n} : j ∈ cycNbhd n M i ↔ cycDist n i j < M := by
  simp [cycNbhd]

theorem mem_cycNbhd_self {n M : ℕ} (hM : 0 < M) (i : Fin n) : i ∈ cycNbhd n M i := by
  rw [mem_cycNbhd, cycDist]
  omega

/-- The forward gap from `i` to `j` on the cycle `ℤ / nℤ`, in `{0, …, n - 1}`: `j ≡ i + gap`. -/
def cycGap (n i j : ℕ) : ℕ := if i ≤ j then j - i else j + n - i

theorem cycGap_inj_right {n i j j' : ℕ} (hi : i < n) (hj : j < n) (hj' : j' < n)
    (h : cycGap n i j = cycGap n i j') : j = j' := by
  unfold cycGap at h
  split_ifs at h <;> omega

theorem cycGap_inj_left {n i j j' : ℕ} (hj : j < n) (hj' : j' < n)
    (h : cycGap n j i = cycGap n j' i) : j = j' := by
  unfold cycGap at h
  split_ifs at h <;> omega

/-- A neighbour `j ≠ i` of `i` is at forward gap `ℓ ∈ [1, M - 1]` from `i`, or `i` is at
forward gap `ℓ ∈ [1, M - 1]` from `j`. -/
theorem cycGap_mem_Icc_or {n M i j : ℕ} (hi : i < n) (hj : j < n) (hne : j ≠ i)
    (h : cycDist n i j < M) :
    cycGap n i j ∈ Finset.Icc 1 (M - 1) ∨ cycGap n j i ∈ Finset.Icc 1 (M - 1) := by
  simp only [Finset.mem_Icc]
  unfold cycGap cycDist at *
  split_ifs <;> omega

/-- `|B_i| ≤ 2 M` (source line 1803). -/
theorem card_cycNbhd_le (n M : ℕ) (i : Fin n) : (cycNbhd n M i).card ≤ 2 * M := by
  have hmaps : Set.MapsTo (fun j : Fin n => cycGap n i j) ↑(cycNbhd n M i)
      ↑(Finset.range M ∪ Finset.Ioo (n - M) n) := by
    intro j hj
    rw [Finset.mem_coe, mem_cycNbhd] at hj
    simp only [Finset.coe_union, Finset.coe_range, Finset.coe_Ioo, Set.mem_union, Set.mem_Iio,
      Set.mem_Ioo]
    have := i.2
    have := j.2
    unfold cycGap cycDist at *
    split_ifs <;> omega
  have hinj : Set.InjOn (fun j : Fin n => cycGap n i j) ↑(cycNbhd n M i) :=
    fun j _ j' _ h => Fin.ext (cycGap_inj_right i.2 j.2 j'.2 h)
  calc (cycNbhd n M i).card ≤ (Finset.range M ∪ Finset.Ioo (n - M) n).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ (Finset.range M).card + (Finset.Ioo (n - M) n).card := Finset.card_union_le _ _
    _ ≤ 2 * M := by simp only [Finset.card_range, Nat.card_Ioo]; omega

/-- Rotating by `i` and then by the gap from `i` to `j` is rotating by `j`. -/
theorem rotate_rotate_cycGap {β : Type*} {x : List β} {n i j : ℕ} (hx : x.length = n)
    (hi : i < n) (hj : j < n) : (x.rotate i).rotate (cycGap n i j) = x.rotate j := by
  rw [List.rotate_rotate]
  unfold cycGap
  split_ifs with h
  · rw [Nat.add_sub_cancel' h]
  · rw [show i + (j + n - i) = j + n by omega, ← List.rotate_mod, hx, Nat.add_mod_right,
      Nat.mod_eq_of_lt hj]

/-! ### The cyclic indicator events and the Chen–Stein error terms -/

/-- The event `{I_{i+1}^{(M)}(X_1, …, X_n) = 1}` (`0`-based index `i : Fin n`). -/
def cycEvent (G : PlaneTree → Prop) (M n : ℕ) (i : Fin n) : Set (Fin n → ℤ) :=
  {ω | FirstMarked G M ((List.ofFn ω).rotate i)}

theorem measurableSet_cycEvent (G : PlaneTree → Prop) (M n : ℕ) (i : Fin n) :
    MeasurableSet (cycEvent G M n i) :=
  (Set.to_countable _).measurableSet

/-- The error term `b_1 = ∑_i ∑_{j ∈ B_i} q_i q_j` of Proposition `prop:AGG` for the indicators
`I_i^{(M)}` under `P(· | S_n = -1)` (source lines 1607, 1719). -/
noncomputable def errorB1 (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ cycNbhd n M i,
    (bridgeLaw μ n).real (cycEvent G M n i) * (bridgeLaw μ n).real (cycEvent G M n j)

/-- The error term `b_2 = ∑_i ∑_{j ∈ B_i \ {i}} E[I_i I_j]` (source lines 1607, 1719). -/
noncomputable def errorB2 (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ cycNbhd n M i \ {i},
    (bridgeLaw μ n).real (cycEvent G M n i ∩ cycEvent G M n j)

/-- The error term `b_3 = ∑_i |E[(I_i - q_i) f(1 + ∑_{j ∉ B_i} I_j)]|` (source lines 1607,
1721–1725), for a test function `f`. -/
noncomputable def errorB3 (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ i : Fin n, |∫ ω, ((cycEvent G M n i).indicator (1 : (Fin n → ℤ) → ℝ) ω -
      (bridgeLaw μ n).real (cycEvent G M n i)) *
    f (1 + ∑ j ∈ Finset.univ \ cycNbhd n M i,
      (cycEvent G M n j).indicator (1 : (Fin n → ℤ) → ℕ) ω) ∂bridgeLaw μ n|

/-- Every cyclic indicator has bridge probability `q` (cyclic exchangeability, source line
1724). -/
theorem bridgeLaw_real_cycEvent (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) (i : Fin n) :
    (bridgeLaw μ n).real (cycEvent G M n i) = qProb μ G M n :=
  bridgeLaw_real_firstMarked_rotate μ G M n i

/-- `λ = ∑_i P(I_i^{(M)} = 1 | S_n = -1) = n q`. -/
theorem sum_bridgeLaw_real_cycEvent (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) :
    ∑ i : Fin n, (bridgeLaw μ n).real (cycEvent G M n i) = n * qProb μ G M n := by
  simp only [bridgeLaw_real_cycEvent, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- `W_n^M = ∑_i I_i^{(M)}` as a sum of indicators of the events `cycEvent`. -/
theorem cyclicSum_ofFn_eq_sum_indicator (G : PlaneTree → Prop) (M : ℕ) {n : ℕ}
    (ω : Fin n → ℤ) :
    cyclicSum G M (List.ofFn ω) =
      ∑ i : Fin n, (cycEvent G M n i).indicator (1 : (Fin n → ℤ) → ℕ) ω := by
  rw [cyclicSum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold shiftIndicator
  by_cases h : FirstMarked G M ((List.ofFn ω).rotate i)
  · rw [firstIndicator_eq_one_iff.mpr h, Set.indicator_of_mem (show ω ∈ cycEvent G M n i from h)]
    rfl
  · rw [firstIndicator_eq_zero_iff.mpr h,
      Set.indicator_of_notMem (show ω ∉ cycEvent G M n i from h)]

/-- **Proposition `prop:AGG` instantiated** (source lines 1615–1619, 1709–1725): at every
admissible `n` and cutoff `M ≥ 1`, with `P = P(· | S_n = -1)`, `E_i = {I_{i+1}^{(M)} = 1}` and
`B_i = cycNbhd n M i`, there is `f` with `‖f‖_∞ ≤ 1` such that
`d_TV(W_n^M, Po(n q)) ≤ 2 (b_1 + b_2 + b_3(f))`. -/
theorem exists_paperTVDist_cyclicSum_le_errorTerms (μ : PMF ℕ) (G : PlaneTree → Prop)
    {M n : ℕ} (hn : Admissible μ n) (hM : 0 < M) :
    ∃ f : ℕ → ℝ, (∀ k, |f k| ≤ 1) ∧
      paperTVDist ((bridgeLaw μ n).map (fun ω => cyclicSum G M (List.ofFn ω)))
          (poissonMeasure (Real.toNNReal ((n : ℝ) * qProb μ G M n))) ≤
        2 * (errorB1 μ G M n + errorB2 μ G M n + errorB3 μ G M n f) := by
  have := isProbabilityMeasure_bridgeLaw hn
  obtain ⟨f, hf, h⟩ := ChenStein.prop_AGG (bridgeLaw μ n) n (cycEvent G M n)
    (measurableSet_cycEvent G M n) (cycNbhd n M) (mem_cycNbhd_self hM)
  refine ⟨f, hf, ?_⟩
  have hW : (fun ω : Fin n → ℤ => cyclicSum G M (List.ofFn ω)) =
      fun ω => ∑ i : Fin n, (cycEvent G M n i).indicator (1 : (Fin n → ℤ) → ℕ) ω :=
    funext fun ω => cyclicSum_ofFn_eq_sum_indicator G M ω
  rw [hW, ← sum_bridgeLaw_real_cycEvent]
  exact h

/-! ### Bounding `b_1` (Proposition `prop:b1`) -/

/-- `b_1 ≤ n · 2M · q²` (source line 1803). -/
theorem errorB1_le (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) :
    errorB1 μ G M n ≤ n * (2 * M) * qProb μ G M n ^ 2 := by
  unfold errorB1
  simp only [bridgeLaw_real_cycEvent, Finset.sum_const, nsmul_eq_mul]
  have hq : 0 ≤ qProb μ G M n * qProb μ G M n := mul_self_nonneg _
  calc ∑ i : Fin n, ((cycNbhd n M i).card : ℝ) * (qProb μ G M n * qProb μ G M n)
      ≤ ∑ _i : Fin n, ((2 * M : ℕ) : ℝ) * (qProb μ G M n * qProb μ G M n) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_cycNbhd_le n M i) hq
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring


/-- `b_1` is nonnegative. -/
theorem errorB1_nonneg (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) : 0 ≤ errorB1 μ G M n :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg measureReal_nonneg measureReal_nonneg

/-- Bounded mean: `n² π_n² = O(1)` along admissible sizes. -/
theorem isBigO_mul_mul_markProb_sq_one {G : ℕ → PlaneTree → Prop} {k : ℕ → ℕ}
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) :
    (fun n : ℕ => (n : ℝ) * ((n : ℝ) * markProb μ G k n ^ 2)) =O[admissibleSizes μ]
      (fun _ => (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := hbd
  refine IsBigO.of_bound (C ^ 2) ?_
  filter_upwards [hC] with n hn
  have h0 : 0 ≤ (n : ℝ) * markProb μ G k n := mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg
  rw [norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (n : ℝ) * ((n : ℝ) * markProb μ G k n ^ 2) = ((n : ℝ) * markProb μ G k n) ^ 2 := by ring
    _ ≤ C ^ 2 := pow_le_pow_left₀ h0 hn 2

/-- `n M_n π_n² → 0` along admissible sizes when `(n π_n)` is bounded and `M_n = o(n)`. -/
theorem tendsto_mul_cutoff_mul_markProb_sq {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hM : IsCutoff M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) :
    Tendsto (fun n : ℕ => (n : ℝ) * M n * markProb μ G k n ^ 2) (admissibleSizes μ) (𝓝 0) := by
  have h2 := isBigO_mul_mul_markProb_sq_one hbd
  have h1 : (fun n : ℕ => (M n : ℝ) * ((n : ℝ) * markProb μ G k n ^ 2)) =o[admissibleSizes μ]
      (fun n : ℕ => (n : ℝ) * ((n : ℝ) * markProb μ G k n ^ 2)) :=
    (hM.isLittleO.mono inf_le_left).mul_isBigO (isBigO_refl _ _)
  refine ((isLittleO_one_iff ℝ).mp (h1.trans_isBigO h2)).congr fun n => ?_
  ring

/-- **Proposition `prop:b1`** (source lines 1797–1807): if `(n π_n)` is bounded, then
`n · 2M_n · q_n² → 0` along admissible sizes (via Corollary `cor:pip`). -/
theorem tendsto_mul_two_mul_cutoff_mul_qProb_sq (hT : StableToolkit μ α a)
    {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ} (hM : IsCutoff M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) :
    Tendsto (fun n : ℕ => (n : ℝ) * (2 * M n) * qProb μ (G (k n)) (M n) n ^ 2)
      (admissibleSizes μ) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_qProb_le_mul_markProb hT G k hM.isLittleO
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  have hlim := (tendsto_mul_cutoff_mul_markProb_sq hM hbd).const_mul (2 * C ^ 2)
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hlim
  filter_upwards [hadm] with n hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h0 => not_admissible_zero μ (h0 ▸ hn)
  have hq0 : 0 ≤ qProb μ (G (k n)) (M n) n := measureReal_nonneg
  have hq := hC n hn1 hn
  have hq2 : qProb μ (G (k n)) (M n) n ^ 2 ≤ (C * markProb μ G k n) ^ 2 :=
    pow_le_pow_left₀ hq0 hq 2
  calc (n : ℝ) * (2 * M n) * qProb μ (G (k n)) (M n) n ^ 2
      ≤ (n : ℝ) * (2 * M n) * (C * markProb μ G k n) ^ 2 := by gcongr
    _ = 2 * C ^ 2 * ((n : ℝ) * M n * markProb μ G k n ^ 2) := by ring

/-- **Proposition `prop:b1`** (source lines 1797–1807): if `(n π_n)` is bounded, then
`b_1^n → 0` along admissible sizes. -/
theorem tendsto_errorB1 (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hM : IsCutoff M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) :
    Tendsto (fun n => errorB1 μ (G (k n)) (M n) n) (admissibleSizes μ) (𝓝 0) :=
  squeeze_zero (fun n => errorB1_nonneg μ _ _ n) (fun n => errorB1_le μ _ _ n)
    (tendsto_mul_two_mul_cutoff_mul_qProb_sq hT hM hbd)

/-! ### Bounding `b_2` (Lemma `lem:boundb2`) -/

/-- `E[I_1^{(M)} I_{1+ℓ}^{(M)} | S_n = -1]`. -/
noncomputable def pairBridge (μ : PMF ℕ) (G : PlaneTree → Prop) (M n ℓ : ℕ) : ℝ :=
  (bridgeLaw μ n).real
    {ω | FirstMarked G M (List.ofFn ω) ∧ FirstMarked G M ((List.ofFn ω).rotate ℓ)}

/-- **Cyclic exchangeability for pairs**: `P(I_{i+1} = I_{j+1} = 1 | S_n = -1)` only depends on
the forward gap from `i` to `j` (source line 1823, "by cyclic invariance"). -/
theorem bridgeLaw_real_cycEvent_inter (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ)
    (i j : Fin n) :
    (bridgeLaw μ n).real (cycEvent G M n i ∩ cycEvent G M n j) =
      pairBridge μ G M n (cycGap n i j) := by
  have h := bridgeLaw_rotate μ n i
    (fun x => FirstMarked G M x ∧ FirstMarked G M (x.rotate (cycGap n i j)))
  rw [pairBridge, measureReal_def, measureReal_def, ← h]
  congr 2
  ext ω
  simp only [cycEvent, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [rotate_rotate_cycGap (List.length_ofFn) i.2 j.2]

/-- `b_2 ≤ 2 n ∑_{ℓ=1}^{M-1} E[I_1^{(M)} I_{1+ℓ}^{(M)} | S_n = -1]` (cyclic exchangeability;
the pairs at cyclic distance `ℓ` are at forward gap `ℓ` or `n - ℓ`). -/
theorem errorB2_le (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) :
    errorB2 μ G M n ≤ n * (2 * ∑ ℓ ∈ Finset.Icc 1 (M - 1), pairBridge μ G M n ℓ) := by
  unfold errorB2
  rw [show (n : ℝ) * (2 * ∑ ℓ ∈ Finset.Icc 1 (M - 1), pairBridge μ G M n ℓ) =
      ∑ _i : Fin n, (∑ ℓ ∈ Finset.Icc 1 (M - 1), pairBridge μ G M n ℓ +
        ∑ ℓ ∈ Finset.Icc 1 (M - 1), pairBridge μ G M n ℓ) by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_filter_add_sum_filter_not (cycNbhd n M i \ {i})
    (fun j : Fin n => cycGap n i j ∈ Finset.Icc 1 (M - 1))]
  have hnn : ∀ ℓ ∈ Finset.Icc 1 (M - 1), 0 ≤ pairBridge μ G M n ℓ :=
    fun _ _ => measureReal_nonneg
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum_of_injOn (fun j : Fin n => cycGap n i j)
      (fun j _ j' _ h => Fin.ext (cycGap_inj_right i.2 j.2 j'.2 h)) ?_
      (fun j _ => (bridgeLaw_real_cycEvent_inter μ G M n i j).le) (fun ℓ hℓ _ => hnn ℓ hℓ)
    intro ℓ hℓ
    rw [Finset.mem_image] at hℓ
    obtain ⟨j, hj, rfl⟩ := hℓ
    exact (Finset.mem_filter.mp hj).2
  · refine Finset.sum_le_sum_of_injOn (fun j : Fin n => cycGap n j i)
      (fun j _ j' _ h => Fin.ext (cycGap_inj_left j.2 j'.2 h)) ?_
      (fun j _ => ?_) (fun ℓ hℓ _ => hnn ℓ hℓ)
    · intro ℓ hℓ
      rw [Finset.mem_image] at hℓ
      obtain ⟨j, hj, rfl⟩ := hℓ
      rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton, mem_cycNbhd] at hj
      obtain ⟨⟨hjB, hji⟩, hnot⟩ := hj
      exact (cycGap_mem_Icc_or i.2 j.2 (fun h => hji (Fin.ext h)) hjB).resolve_left hnot
    · rw [Set.inter_comm]
      exact (bridgeLaw_real_cycEvent_inter μ G M n j i).le

/-- Locality of the pair event: for `ℓ + M ≤ K ≤ |x|`, the pair `I_1^{(M)} I_{1+ℓ}^{(M)}` only
reads the first `K` entries. -/
theorem firstMarked_pair_take_iff {G : PlaneTree → Prop} {M ℓ K : ℕ} {x : List ℤ}
    (hℓ : ℓ + M ≤ K) (hK : K ≤ x.length) :
    (FirstMarked G M (x.take K) ∧ FirstMarked G M ((x.take K).rotate ℓ)) ↔
      (FirstMarked G M x ∧ FirstMarked G M (x.rotate ℓ)) := by
  rw [firstMarked_rotate_iff_drop (by rw [List.length_take]; omega),
    firstMarked_rotate_iff_drop (by omega)]
  refine and_congr ?_ ?_
  · rw [← firstMarked_take_iff (x := x.take K), List.take_take, Nat.min_eq_left (by omega),
      firstMarked_take_iff]
  · rw [← firstMarked_take_iff (x := (x.take K).drop ℓ), List.drop_take, List.take_take,
      Nat.min_eq_left (by omega), firstMarked_take_iff]

/-- `b_2` is nonnegative. -/
theorem errorB2_nonneg (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) : 0 ≤ errorB2 μ G M n :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => measureReal_nonneg

/-- **Lemma `lem:boundb2`** (source lines 1815–1857, audit finding 5): under Assumption (C)
and bounded `n π_n`, `b_2^n → 0` along admissible sizes. Proof: cyclic exchangeability
(`errorB2_le`), bridge removal (Lemma `lem:error_est` with `N_n = n`, window `2 M_n`, endpoint
`-1`), the two-start bound `P(I_1 I_{1+ℓ}) ≤ π_n² + A_n(ℓ)` (`walkVecLaw_real_pair_le_markProb`,
proved by conditioning on `ζ`), and `∑_{ℓ ≤ M_n} A_n(ℓ) = o(n π_n²)`. -/
theorem tendsto_errorB2 (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hM : IsCutoff M) (hC : NonClustering μ G k M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) :
    Tendsto (fun n => errorB2 μ (G (k n)) (M n) n) (admissibleSizes μ) (𝓝 0) := by
  obtain ⟨C₀, hC₀, hbr⟩ := exists_cond_take_le hT
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  have hz : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n => a ((fun n : ℕ => n) n)) := by
    rw [isLittleO_one_left_iff]
    exact tendsto_abs_atTop_atTop.comp hT.tendsto_atTop
  have h2Mo : (fun n => ((2 * M n : ℕ) : ℝ)) =o[atTop] (fun n => (n : ℝ)) := by
    have := hM.isLittleO.const_mul_left 2
    refine this.congr_left fun n => ?_
    push_cast
    ring
  have h2M : ∀ᶠ n in atTop, 2 * M n ≤ n := by
    filter_upwards [hM.isLittleO.bound (show (0 : ℝ) < 1 / 2 by norm_num)] with n hn
    rw [Real.norm_natCast, Real.norm_natCast] at hn
    have : ((2 * M n : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  -- the eventual bound `b_2 ≤ 2 C₀ (n M_n π_n² + n ∑_{ℓ ≤ M_n} A_n(ℓ))`
  have hbound : ∀ᶠ n in admissibleSizes μ, errorB2 μ (G (k n)) (M n) n ≤
      2 * C₀ * ((n : ℝ) * M n * markProb μ G k n ^ 2 +
        (n : ℝ) * ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ) := by
    filter_upwards [hl (hbr (N := fun n => n) (m := fun n => 2 * M n) (z := fun _ => 1)
      tendsto_id h2Mo hz), hl h2M, hadm] with n hn h2Mn hadmn
    have hψ : walkProb μ n (-1) ≠ 0 := ((walkProb_neg_one_pos_iff μ n).2 hadmn).ne'
    have hpair : ∀ ℓ ∈ Finset.Icc 1 (M n - 1), pairBridge μ (G (k n)) (M n) n ℓ ≤
        C₀ * (markProb μ G k n ^ 2 + pairProb μ G k n ℓ) := by
      intro ℓ hℓ
      have hℓM : ℓ + M n ≤ 2 * M n := by
        have := (Finset.mem_Icc.mp hℓ).2
        omega
      have h := hn (-1) (by simp) hψ
        (fun y => FirstMarked (G (k n)) (M n) y ∧ FirstMarked (G (k n)) (M n) (y.rotate ℓ))
      have hset : {ω : Fin n → ℤ | FirstMarked (G (k n)) (M n) ((List.ofFn ω).take (2 * M n)) ∧
          FirstMarked (G (k n)) (M n) (((List.ofFn ω).take (2 * M n)).rotate ℓ)} =
          {ω | FirstMarked (G (k n)) (M n) (List.ofFn ω) ∧
            FirstMarked (G (k n)) (M n) ((List.ofFn ω).rotate ℓ)} := by
        ext ω
        simp only [Set.mem_ofPred_eq]
        exact firstMarked_pair_take_iff hℓM (by rw [List.length_ofFn]; exact h2Mn)
      rw [hset] at h
      calc pairBridge μ (G (k n)) (M n) n ℓ ≤ C₀ * (walkVecLaw μ (2 * M n)).real
            {ω | FirstMarked (G (k n)) (M n) (List.ofFn ω) ∧
              FirstMarked (G (k n)) (M n) ((List.ofFn ω).rotate ℓ)} := h
        _ ≤ C₀ * (markProb μ G k n ^ 2 + pairProb μ G k n ℓ) :=
          mul_le_mul_of_nonneg_left (walkVecLaw_real_pair_le_markProb μ G k n hℓM) hC₀.le
    have hA0 : ∀ ℓ, 0 ≤ pairProb μ G k n ℓ := fun _ => measureReal_nonneg
    have hsumA : ∑ ℓ ∈ Finset.Icc 1 (M n - 1), pairProb μ G k n ℓ ≤
        ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Nat.sub_le _ _))
        fun ℓ _ _ => hA0 ℓ
    have hcard : ((Finset.Icc 1 (M n - 1)).card : ℝ) ≤ M n := by
      rw [Nat.card_Icc]
      exact_mod_cast (show M n - 1 + 1 - 1 ≤ M n by omega)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc errorB2 μ (G (k n)) (M n) n
        ≤ n * (2 * ∑ ℓ ∈ Finset.Icc 1 (M n - 1), pairBridge μ (G (k n)) (M n) n ℓ) :=
          errorB2_le μ _ _ n
      _ ≤ n * (2 * ∑ ℓ ∈ Finset.Icc 1 (M n - 1),
            C₀ * (markProb μ G k n ^ 2 + pairProb μ G k n ℓ)) := by
          gcongr with ℓ hℓ
          exact hpair ℓ hℓ
      _ = 2 * C₀ * ((n : ℝ) * ((Finset.Icc 1 (M n - 1)).card * markProb μ G k n ^ 2) +
            n * ∑ ℓ ∈ Finset.Icc 1 (M n - 1), pairProb μ G k n ℓ) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ 2 * C₀ * ((n : ℝ) * (M n * markProb μ G k n ^ 2) +
            n * ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ) := by
          gcongr
      _ = _ := by ring
  -- the bound tends to zero
  have hA : Tendsto (fun n : ℕ => (n : ℝ) * ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ)
      (admissibleSizes μ) (𝓝 0) :=
    (isLittleO_one_iff ℝ).mp (((isBigO_refl (fun n : ℕ => (n : ℝ)) _).mul_isLittleO
      hC).trans_isBigO (isBigO_mul_mul_markProb_sq_one hbd))
  have hlim := ((tendsto_mul_cutoff_mul_markProb_sq hM hbd).add hA).const_mul (2 * C₀)
  rw [add_zero, mul_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall fun n => errorB2_nonneg μ _ _ n) hbound hlim

end PoissonDeclumping.Bridge
