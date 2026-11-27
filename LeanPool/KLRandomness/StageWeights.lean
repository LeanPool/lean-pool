/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SparseListWeights
public import LeanPool.KLRandomness.EffectiveNormalizationStrategy
public import LeanPool.KLRandomness.DropEvents
public import LeanPool.KLRandomness.EarlyLateWagers
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual all-time wager weights for a finite stage

For a fresh scan, a position receives at most one wager along any input.
The all-time absolute wager on a finite support is therefore a finite sum,
even though the relevant query times need not have a uniform finite bound.
Its pathwise square budget gives the Cauchy--Schwarz bound used in Section 5.

The incidence estimate for the actual executable sparse list then bounds the
average expected all-time support wager under any probability law. In
particular, the law may be the current finite affine stage law.
-/

@[expose] public section

namespace Klr.StageWeights

open MeasureTheory
open scoped BigOperators

/-- The absolute wager charged to a position, zero if that position is never
queried on this input. Freshness makes the series have at most one nonzero term. -/
noncomputable def wagerAt (π : ScanRule) (w : List Bool → ℝ) (a : ℕ) (X : Cantor) : ℝ := by
  classical
  exact ∑' t : ℕ, if π.query (π.transcript X t) = a then |w (π.transcript X t)| else 0

/-- The all-time absolute wager charged to a finite support. -/
noncomputable def supportWager (π : ScanRule) (w : List Bool → ℝ)
    (S : Finset ℕ) (X : Cantor) : ℝ :=
  ∑ a ∈ S, wagerAt π w a X

theorem wagerAt_nonneg (π : ScanRule) (w : List Bool → ℝ) (a : ℕ) (X : Cantor) :
    0 ≤ wagerAt π w a X := by
  classical
  exact tsum_nonneg fun t => by split_ifs <;> positivity

theorem supportWager_nonneg (π : ScanRule) (w : List Bool → ℝ) (S : Finset ℕ) (X : Cantor) :
    0 ≤ supportWager π w S X :=
  Finset.sum_nonneg fun a _ => wagerAt_nonneg π w a X

theorem wagerAt_eq_of_query (π : ScanRule) (w : List Bool → ℝ) (X : Cantor) (t : ℕ) :
    wagerAt π w (π.query (π.transcript X t)) X = |w (π.transcript X t)| := by
  classical
  rw [wagerAt, tsum_eq_single t]
  · simp
  · intro s hst
    have hq : π.query (π.transcript X s) ≠ π.query (π.transcript X t) :=
      fun h => hst (π.query_injective X h)
    simp [hq]

theorem wagerAt_eq_zero_of_not_queried (π : ScanRule) (w : List Bool → ℝ)
    (a : ℕ) (X : Cantor) (ha : ∀ t, π.query (π.transcript X t) ≠ a) :
    wagerAt π w a X = 0 := by
  classical
  simp [wagerAt, ha]

theorem measurable_wagerAt (π : ScanRule) (w : List Bool → ℝ) (a : ℕ) :
    Measurable (wagerAt π w a) := by
  classical
  apply Measurable.tsum
  intro t
  exact DropEvents.measurable_transcript_eval π t
    (fun v => if π.query v = a then |w v| else 0)

theorem measurable_supportWager (π : ScanRule) (w : List Bool → ℝ) (S : Finset ℕ) :
    Measurable (supportWager π w S) :=
  Finset.measurable_sum S fun a _ => measurable_wagerAt π w a

/-- All query times in a fixed finite support form a finite set, by freshness. -/
theorem finite_queryTimes (π : ScanRule) (S : Finset ℕ) (X : Cantor) :
    {t : ℕ | π.query (π.transcript X t) ∈ S}.Finite :=
  S.finite_toSet.preimage (π.query_injective X).injOn

/-- All query times at which a scan visits the given finite support on an input. -/
noncomputable def queryTimes (π : ScanRule) (S : Finset ℕ) (X : Cantor) : Finset ℕ :=
  (finite_queryTimes π S X).toFinset

@[simp] theorem mem_queryTimes (π : ScanRule) (S : Finset ℕ) (X : Cantor) (t : ℕ) :
    t ∈ queryTimes π S X ↔ π.query (π.transcript X t) ∈ S := by
  simp [queryTimes]

/-- Reindexing by the actual fresh query times is exact, for any function that
vanishes at zero. Positions never queried contribute zero. -/
theorem sum_wagerAt_comp_eq (π : ScanRule) (w : List Bool → ℝ)
    (S : Finset ℕ) (X : Cantor) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ a ∈ S, f (wagerAt π w a X)) =
      ∑ t ∈ queryTimes π S X, f |w (π.transcript X t)| := by
  classical
  let q : ℕ → ℕ := fun t => π.query (π.transcript X t)
  have hsub : (queryTimes π S X).image q ⊆ S := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
    exact (mem_queryTimes π S X t).mp ht
  calc
    _ = ∑ a ∈ (queryTimes π S X).image q, f (wagerAt π w a X) := by
      symm
      apply Finset.sum_subset hsub
      intro a ha hnot
      have hn : ∀ t, q t ≠ a := by
        intro t ht
        exact hnot (Finset.mem_image.mpr ⟨t,
          (mem_queryTimes π S X t).mpr (by change q t ∈ S; rw [ht]; exact ha), ht⟩)
      rw [wagerAt_eq_zero_of_not_queried π w a X hn, hf]
    _ = ∑ t ∈ queryTimes π S X, f (wagerAt π w (q t) X) := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact π.query_injective X hij
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [show q t = π.query (π.transcript X t) from rfl, wagerAt_eq_of_query]

/-- The finite-position definition agrees with the paper's all-time sum over
queries into the support. -/
theorem supportWager_eq_tsum (π : ScanRule) (w : List Bool → ℝ)
    (S : Finset ℕ) (X : Cantor) :
    supportWager π w S X =
      ∑' t : ℕ, if π.query (π.transcript X t) ∈ S then |w (π.transcript X t)| else 0 := by
  classical
  change (∑ a ∈ S, id (wagerAt π w a X)) = _
  rw [sum_wagerAt_comp_eq π w S X id rfl]
  rw [tsum_eq_sum (s := queryTimes π S X)]
  · apply Finset.sum_congr rfl
    intro t ht
    simp [(mem_queryTimes π S X t).mp ht]
  · intro t ht
    simp only [mem_queryTimes] at ht
    simp [ht]

/-- Finite query horizons contribute no more than the complete support wager. -/
theorem partial_supportWager_le (π : ScanRule) (w : List Bool → ℝ)
    (S : Finset ℕ) (X : Cantor) (N : ℕ) :
    (∑ t ∈ Finset.range N,
      if π.query (π.transcript X t) ∈ S then |w (π.transcript X t)| else 0) ≤
        supportWager π w S X := by
  classical
  have hs : Summable (fun t : ℕ =>
      if π.query (π.transcript X t) ∈ S then |w (π.transcript X t)| else 0) := by
    apply summable_of_ne_finset_zero (s := queryTimes π S X)
    intro t ht
    simp only [mem_queryTimes] at ht
    simp [ht]
  rw [supportWager_eq_tsum]
  exact hs.sum_le_tsum _ (fun t _ => by split_ifs <;> positivity)

/-- The actual early rank-drop wager total is dominated by the finite
support-wager sum through the same horizon. -/
theorem earlyWager_le_partial_supportWager (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (j : ℕ) (X : Cantor) :
    EarlyLateWagers.earlyWager B π w V j X ≤
      ∑ t ∈ Finset.range (V j),
        if π.query (π.transcript X t) ∈ (B j).support then |w (π.transcript X t)| else 0 := by
  classical
  unfold EarlyLateWagers.earlyWager
  apply Finset.sum_le_sum
  intro t ht
  by_cases h : DropEvents.atTime B π j X t
  · simp only [EarlyLateWagers.blockWager, h, ↓reduceIte, h.1, le_refl]
  · simp only [EarlyLateWagers.blockWager, h, ↓reduceIte]
    split_ifs <;> positivity

/-- The actual early rank-drop wager total is dominated by the all-time
wager total on the block's support. -/
theorem earlyWager_le_supportWager (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (j : ℕ) (X : Cantor) :
    EarlyLateWagers.earlyWager B π w V j X ≤ supportWager π w (B j).support X :=
  (earlyWager_le_partial_supportWager B π w V j X).trans
    (partial_supportWager_le π w (B j).support X (V j))

/-- The square budget of the wagers at pool positions is bounded by the
actual square budget over all query times. -/
theorem sum_wagerAt_sq_le (π : ScanRule) (w : List Bool → ℝ)
    (S : Finset ℕ) (X : Cantor)
    (hsum : Summable (fun t => (w (π.transcript X t)) ^ 2)) {C : ℝ}
    (hC : (∑' t, (w (π.transcript X t)) ^ 2) ≤ C) :
    (∑ a ∈ S, (wagerAt π w a X) ^ 2) ≤ C := by
  rw [sum_wagerAt_comp_eq π w S X (fun x => x ^ 2) (by norm_num)]
  simp_rw [sq_abs]
  exact (hsum.sum_le_tsum _ (fun _ _ => sq_nonneg _)).trans hC

/-- Cauchy--Schwarz for the actual all-time wagers on a finite support. -/
theorem supportWager_le_sqrt (π : ScanRule) (w : List Bool → ℝ)
    (S : Finset ℕ) (X : Cantor)
    (hsum : Summable (fun t => (w (π.transcript X t)) ^ 2)) {C : ℝ}
    (hC : (∑' t, (w (π.transcript X t)) ^ 2) ≤ C) :
    supportWager π w S X ≤ Real.sqrt ((S.card : ℝ) * C) := by
  classical
  have hs := sum_wagerAt_sq_le π w S X hsum hC
  have h := Sparse.sum_weights_le_sqrt (fun a : S => wagerAt π w a.val X) C
    (fun a => wagerAt_nonneg π w a.val X)
    (by rwa [Finset.sum_coe_sort S (fun a => (wagerAt π w a X) ^ 2)])
  rw [Finset.sum_coe_sort S (fun a => wagerAt π w a X)] at h
  simpa only [supportWager, Fintype.card_coe] using h

/-- Every finite-support total is integrable under every finite law, with a
uniform pathwise square budget. -/
theorem integrable_supportWager (μ : Measure Cantor) [IsFiniteMeasure μ]
    (π : ScanRule) (w : List Bool → ℝ) (S : Finset ℕ) {C : ℝ}
    (hsum : ∀ X, Summable (fun t => (w (π.transcript X t)) ^ 2))
    (hC : ∀ X, (∑' t, (w (π.transcript X t)) ^ 2) ≤ C) :
    Integrable (supportWager π w S) μ := by
  apply Integrable.of_bound (measurable_supportWager π w S).aestronglyMeasurable
    (Real.sqrt ((S.card : ℝ) * C))
  exact Filter.Eventually.of_forall fun X => by
    rw [Real.norm_eq_abs, abs_of_nonneg (supportWager_nonneg π w S X)]
    exact supportWager_le_sqrt π w S X (hsum X) (hC X)

/-- Injectively labeling a finite pool preserves the support sum exactly. -/
theorem supportWager_image {M : ℕ} (π : ScanRule) (w : List Bool → ℝ)
    (e : Fin M → ℕ) (he : Function.Injective e) (S : Finset (Fin M)) (X : Cantor) :
    supportWager π w (S.image e) X = ∑ i ∈ S, wagerAt π w (e i) X := by
  classical
  unfold supportWager
  rw [Finset.sum_image]
  exact fun i _ j _ h => he h

/-- The all-time position weights on any injectively labeled pool obey the
same square budget as the original time-indexed wagers. -/
theorem sum_wagerAt_sq_le_of_injective {M : ℕ} (π : ScanRule) (w : List Bool → ℝ)
    (e : Fin M → ℕ) (he : Function.Injective e) (X : Cantor)
    (hsum : Summable (fun t => (w (π.transcript X t)) ^ 2)) {C : ℝ}
    (hC : (∑' t, (w (π.transcript X t)) ^ 2) ≤ C) :
    (∑ i : Fin M, (wagerAt π w (e i) X) ^ 2) ≤ C := by
  classical
  have h := sum_wagerAt_sq_le π w (Finset.univ.image e) X hsum hC
  rwa [Finset.sum_image (fun i _ j _ h => he h)] at h

/-- The actual coded sparse-list incidence bound controls all-time support
wagers pathwise, before any probability law is chosen. -/
theorem average_supportWager_le {M m r J : ℕ} {τ θ : ℚ} {L : SparseListSearch.CodeList}
    (hL : SparseListSearch.Good M m r J τ θ L) (hJ : 0 < J)
    (π : ScanRule) (w : List Bool → ℝ) (e : Fin M → ℕ) (he : Function.Injective e)
    (X : Cantor) (hsum : Summable (fun t => (w (π.transcript X t)) ^ 2)) {C : ℝ}
    (hC : (∑' t, (w (π.transcript X t)) ^ 2) ≤ C) :
    (∑ j : Fin L.length,
      supportWager π w ((SparseListWeights.support M (L.get j)).image e) X) / J ≤
      (2 * ((m : ℝ) / M)) * Real.sqrt ((M : ℝ) * C) := by
  have h := SparseListWeights.average_supportWeight_le hL hJ
    (fun i => wagerAt π w (e i) X) C (fun i => wagerAt_nonneg π w (e i) X)
    (sum_wagerAt_sq_le_of_injective π w e he X hsum hC)
  simpa only [supportWager_image π w e he, SparseListWeights.supportWeight] using h

/-- Average expected all-time wager on the actual candidate supports, under
an arbitrary probability law such as the current finite-stage law. -/
theorem average_integral_supportWager_le (μ : Measure Cantor) [IsProbabilityMeasure μ]
    {M m r J : ℕ} {τ θ : ℚ} {L : SparseListSearch.CodeList}
    (hL : SparseListSearch.Good M m r J τ θ L) (hJ : 0 < J)
    (π : ScanRule) (w : List Bool → ℝ) (e : Fin M → ℕ) (he : Function.Injective e)
    {C : ℝ} (hsum : ∀ X, Summable (fun t => (w (π.transcript X t)) ^ 2))
    (hC : ∀ X, (∑' t, (w (π.transcript X t)) ^ 2) ≤ C) :
    (∑ j : Fin L.length,
      ∫ X, supportWager π w ((SparseListWeights.support M (L.get j)).image e) X ∂μ) / J ≤
      (2 * ((m : ℝ) / M)) * Real.sqrt ((M : ℝ) * C) := by
  let f (j : Fin L.length) := supportWager π w ((SparseListWeights.support M (L.get j)).image e)
  have hf (j : Fin L.length) : Integrable (f j) μ :=
    integrable_supportWager μ π w _ hsum hC
  calc
    _ = ∫ X, (∑ j : Fin L.length, f j X) / J ∂μ := by
      rw [integral_div, integral_finsetSum _ (fun j _ => hf j)]
    _ ≤ ∫ _X : Cantor,
        (2 * ((m : ℝ) / M)) * Real.sqrt ((M : ℝ) * C) ∂μ := by
      apply integral_mono ((integrable_finsetSum _ (fun j _ => hf j)).div_const _)
        (integrable_const _)
      intro X
      exact average_supportWager_le hL hJ π w e he X (hsum X) (hC X)
    _ = _ := by simp

/-- The averaging estimate sums over any finite protected family of scans.
It selects the same candidate family for all of them. -/
theorem average_integral_family_supportWager_le {ι : Type*} [Fintype ι]
    (μ : Measure Cantor) [IsProbabilityMeasure μ]
    {M m r J : ℕ} {τ θ : ℚ} {L : SparseListSearch.CodeList}
    (hL : SparseListSearch.Good M m r J τ θ L) (hJ : 0 < J)
    (π : ι → ScanRule) (w : ι → List Bool → ℝ)
    (e : Fin M → ℕ) (he : Function.Injective e) {C : ℝ}
    (hsum : ∀ i X, Summable (fun t => (w i ((π i).transcript X t)) ^ 2))
    (hC : ∀ i X, (∑' t, (w i ((π i).transcript X t)) ^ 2) ≤ C) :
    (∑ j : Fin L.length, ∑ i : ι,
      ∫ X, supportWager (π i) (w i) ((SparseListWeights.support M (L.get j)).image e) X ∂μ) / J ≤
      (Fintype.card ι : ℝ) * ((2 * ((m : ℝ) / M)) * Real.sqrt ((M : ℝ) * C)) := by
  rw [Finset.sum_comm, Finset.sum_div]
  calc
    _ ≤ ∑ _i : ι, (2 * ((m : ℝ) / M)) * Real.sqrt ((M : ℝ) * C) :=
      Finset.sum_le_sum fun i _ =>
        average_integral_supportWager_le μ hL hJ (π i) (w i) e he (hsum i) (hC i)
    _ = _ := by simp

/-- The actual normalized strategies discharge the pathwise square-budget
hypotheses of the simultaneous expectation estimate. -/
theorem average_integral_normalized_supportWager_le {ι : Type*} [Fintype ι]
    (μ : Measure Cantor) [IsProbabilityMeasure μ]
    {M m r J : ℕ} {τ θ : ℚ} {L : SparseListSearch.CodeList}
    (hL : SparseListSearch.Good M m r J τ θ L) (hJ : 0 < J)
    (s : ι → BettingStrategy) (e : Fin M → ℕ) (he : Function.Injective e) :
    (∑ j : Fin L.length, ∑ i : ι,
      ∫ X, supportWager (s i).normalize.scan (s i).normalize.capital.wager
        ((SparseListWeights.support M (L.get j)).image e) X ∂μ) / J ≤
      (Fintype.card ι : ℝ) * ((2 * ((m : ℝ) / M)) * Real.sqrt ((M : ℝ) / 2)) := by
  simpa only [mul_one_div] using average_integral_family_supportWager_le μ hL hJ
    (fun i => (s i).normalize.scan) (fun i => (s i).normalize.capital.wager) e he
    (fun i X => (s i).normalize_wagers_summable X)
    (fun i X => (s i).normalize_wagers_tsum_le_half X)

/-- The paper's polynomial choices give the exact inverse-square bound. -/
theorem polynomial_supportWager_bound_eq (r : ℕ) :
    (2 * ((SparseParameters.supportSize r : ℝ) / SparseParameters.blockSize r)) *
      Real.sqrt ((SparseParameters.blockSize r : ℝ) / 2) =
        Real.sqrt 2 / (r : ℝ) ^ 2 := by
  simp only [SparseParameters.supportSize, SparseParameters.blockSize, Nat.cast_pow]
  rw [Real.sqrt_div (by positivity),
    show (r : ℝ) ^ 8 = ((r : ℝ) ^ 4) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]
  by_cases hr : r = 0
  · simp [hr]
  · have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hs2 : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
      apply (div_eq_iff hs).mpr
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ = (2 / Real.sqrt 2) * (1 / (r : ℝ) ^ 2) := by field_simp
      _ = _ := by rw [hs2]; ring

/-- The checked executable construction has the paper's simultaneous
inverse-square expected-wager estimate for every protected finite family. -/
theorem average_integral_normalized_supportWager_le_of_construct
    {ι : Type*} [Fintype ι] (μ : Measure Cantor) [IsProbabilityMeasure μ]
    {τ θ : ℚ} {r : ℕ} {L : SparseListSearch.CodeList}
    (hL : L ∈ SparseListConstruction.construct τ θ r) (hr : 0 < r)
    (s : ι → BettingStrategy) (e : Fin (SparseParameters.blockSize r) → ℕ)
    (he : Function.Injective e) :
    (∑ j : Fin L.length, ∑ i : ι,
      ∫ X, supportWager (s i).normalize.scan (s i).normalize.capital.wager
        ((SparseListWeights.support (SparseParameters.blockSize r) (L.get j)).image e) X ∂μ) /
          SparseParameters.listSize r ≤
      (Fintype.card ι : ℝ) * (Real.sqrt 2 / (r : ℝ) ^ 2) := by
  have hJ : 0 < SparseParameters.listSize r := by
    unfold SparseParameters.listSize SparseParameters.blockSize
    positivity
  simpa only [polynomial_supportWager_bound_eq] using
    average_integral_normalized_supportWager_le μ
      (SparseListConstruction.construct_spec hL) hJ s e he

/-- The simultaneous support-wager allowance can be made smaller than any
positive stage error by increasing the trial rank. -/
theorem eventually_family_supportWager_bound_lt (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in Filter.atTop,
      (n : ℝ) * (Real.sqrt 2 / (r : ℝ) ^ 2) < ε := by
  have h : Filter.Tendsto (fun r : ℕ => (n : ℝ) * (Real.sqrt 2 / (r : ℝ) ^ 2))
      Filter.atTop (nhds 0) := by
    have ht := (SparseParameters.tendsto_nat_power 2 (by decide)).inv_tendsto_atTop
    simpa [div_eq_mul_inv, Nat.cast_pow] using
      (ht.const_mul (Real.sqrt 2)).const_mul (n : ℝ)
  exact h.eventually_lt_const hε

end Klr.StageWeights
