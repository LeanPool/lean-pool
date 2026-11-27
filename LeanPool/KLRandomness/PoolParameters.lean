/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolAdviceTables
public import LeanPool.KLRandomness.PoolSoundness
public import LeanPool.KLRandomness.PoolWeighted
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Choosing the finite pool advice before the input size

The Borel query partition is fixed first. For a finite protected prefix,
an error tolerance, and a position cutoff, this file chooses a rational low
margin, a rational error tolerance and threshold, a finite number of scans,
and concrete finite prefix tables. None of these choices depends on the
requested pool size M.
-/

@[expose] public section

namespace Klr.PoolAdvice

open Filter MeasureTheory
open scoped BigOperators Topology symmDiff

/-- All finite data and their analytic guarantees, chosen before the pool size. -/
structure FixedParameters {π : ℕ → ScanRule} {a : ℕ → ℕ}
    (Q : Pool.QueryPartition π a) (ℓ : ℕ) (η : ℝ) (z : ℕ) where
  /-- The positive separation margin for the partition estimates. -/
  margin : ℚ
  /-- The number of protected scans fixed before the search. -/
  scanCount : ℕ
  /-- The finite rational and clopen data given to the pool program. -/
  advice : Advice
  margin_pos : 0 < margin
  margin_lt_quarter : margin < 1 / 4
  protected_eq : advice.protectedCount = ℓ
  protected_le : ℓ ≤ scanCount
  position_ge : z ≤ advice.positionBound
  error_pos : 0 < advice.error
  high_budget : 4 * (advice.error : ℝ) < η
  low_budget : η / 3 + 8 * (advice.error : ℝ) / (margin : ℝ) < η
  near_one : ∀ i < ℓ, fairCoin.real
    {Z | Z ∈ Q.low i ∧ 1 - 2 * (margin : ℝ) ≤ Q.representative i Z} < η / 3
  high_approx : ∀ i < ℓ,
    fairCoin.real (Q.high i ∆ highSet advice i) < (advice.error : ℝ)
  function_approx : ∀ i < ℓ,
    (∫ Z, |approx advice i Z - Q.representative i Z| ∂fairCoin) < (advice.error : ℝ)
  approx_bounds : ∀ i < ℓ, ∀ Z, 0 ≤ approx advice i Z ∧ approx advice i Z ≤ 1
  threshold_lower : Pool.weightedQueryLimsup π -
    3 * (protectedWeight advice * (advice.error : ℝ)) < (advice.threshold : ℝ)
  threshold_upper : (advice.threshold : ℝ) < Pool.weightedQueryLimsup π -
    2 * (protectedWeight advice * (advice.error : ℝ))
  tail_lt : (1 / 2 : ℝ) ^ scanCount <
    (protectedWeight advice * (advice.error : ℝ)) / 4
  position_upper : ∀ b ≥ advice.positionBound,
    Pool.weightedQueryProbability π b < Pool.weightedQueryLimsup π +
      protectedWeight advice * (advice.error : ℝ)

/-- All scalar parameters and all finite prefix tables can be chosen jointly,
with the complete finite advice fixed before a later input M. -/
theorem exists_fixedParameters {π : ℕ → ScanRule} {a : ℕ → ℕ}
    (Q : Pool.QueryPartition π a) (ℓ : ℕ) {η : ℝ} (hη : 0 < η) (z : ℕ) :
    Nonempty (FixedParameters Q ℓ η z) := by
  obtain ⟨τ, hτ0, hτ1, hmargin⟩ := Q.exists_rational_margin ℓ (show 0 < η / 3 by positivity)
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτ0
  obtain ⟨δ, hδ0, hδsmall⟩ := exists_rat_btwn
    (show (0 : ℝ) < min (η / 4) (η * (τ : ℝ) / 24) by positivity)
  have hδq : (0 : ℚ) < δ := by exact_mod_cast hδ0
  have hδsmall₁ : (δ : ℝ) < η / 4 := hδsmall.trans_le (min_le_left _ _)
  have hδsmall₂ : (δ : ℝ) < η * (τ : ℝ) / 24 := hδsmall.trans_le (min_le_right _ _)
  have hhigh : 4 * (δ : ℝ) < η := by linarith
  have hlow : η / 3 + 8 * (δ : ℝ) / (τ : ℝ) < η := by
    have hdiv : 8 * (δ : ℝ) / (τ : ℝ) < η / 3 := by
      apply (div_lt_iff₀ hτr).mpr
      nlinarith
    linarith
  let s : ℝ := (1 / 2 : ℝ) ^ ℓ * (δ : ℝ)
  have hs : 0 < s := mul_pos (pow_pos (by norm_num) _) hδ0
  obtain ⟨γ, hγlow, hγhigh⟩ := exists_rat_btwn
    (show Pool.weightedQueryLimsup π - 3 * s < Pool.weightedQueryLimsup π - 2 * s by linarith)
  have htail : ∀ᶠ k : ℕ in atTop, (1 / 2 : ℝ) ^ k < s / 4 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).eventually (gt_mem_nhds (by positivity))
  obtain ⟨D, hD, hDtail⟩ := ((eventually_ge_atTop ℓ).and htail).exists
  obtain ⟨z₀, hz₀⟩ := Pool.exists_weighted_query_upper_cutoff π hs
  obtain ⟨A, hAz, hAℓ, hAδ, hAγ, hAtables⟩ := exists_approximating_advice ℓ
    (max z z₀) ℓ δ γ hδq (fun i => Q.high i.val) (fun i => Q.measurableSet_high i.val)
    (fun i => Q.representative i.val) (fun i => Q.measurable_representative i.val)
    (fun i Z => (Q.representative_bounds i.val Z).1)
    (fun i Z => (Q.representative_bounds i.val Z).2)
  have hsA : protectedWeight A * (A.error : ℝ) = s := by
    simp only [protectedWeight, hAℓ, hAδ, s]
  refine ⟨{
    margin := τ
    scanCount := D
    advice := A
    margin_pos := hτ0
    margin_lt_quarter := hτ1
    protected_eq := hAℓ
    protected_le := hD
    position_ge := ?_
    error_pos := ?_
    high_budget := ?_
    low_budget := ?_
    near_one := hmargin
    high_approx := ?_
    function_approx := ?_
    approx_bounds := ?_
    threshold_lower := ?_
    threshold_upper := ?_
    tail_lt := ?_
    position_upper := ?_ }⟩
  · rw [hAz]
    exact Nat.le_max_left _ _
  · rwa [hAδ]
  · rwa [hAδ]
  · rwa [hAδ]
  · intro i hi
    rw [hAδ, symmDiff_comm]
    exact (hAtables ⟨i, hi⟩).1
  · intro i hi
    rw [hAδ]
    exact (hAtables ⟨i, hi⟩).2.2
  · intro i hi Z
    exact (hAtables ⟨i, hi⟩).2.1 Z
  · rwa [hsA, hAγ]
  · rwa [hsA, hAγ]
  · rwa [hsA]
  · intro b hb
    rw [hsA]
    exact hz₀ b ((Nat.le_max_right z z₀).trans (by rwa [hAz] at hb))

namespace FixedParameters

variable {π : ℕ → ScanRule} {a : ℕ → ℕ} {Q : Pool.QueryPartition π a}
  {ℓ : ℕ} {η : ℝ} {z : ℕ} (P : FixedParameters Q ℓ η z)

/-- The fixed finite family of actual total computable scans compiled by the search. -/
def rules : List ScanRule := List.ofFn (fun i : Fin P.scanCount => π i.val)

@[simp] theorem length_rules : P.rules.length = P.scanCount := List.length_ofFn

theorem getElem?_rules {i : ℕ} (hi : i < P.scanCount) : P.rules[i]? = some (π i) := by
  simp [rules, hi]

theorem protected_le_length : P.advice.protectedCount ≤ P.rules.length := by
  rw [P.protected_eq, P.length_rules]
  exact P.protected_le

theorem error_real_pos : (0 : ℝ) < P.advice.error := by exact_mod_cast P.error_pos

theorem margin_real_pos : (0 : ℝ) < P.margin := by exact_mod_cast P.margin_pos

theorem slack_pos : 0 < protectedWeight P.advice * (P.advice.error : ℝ) :=
  mul_pos (protectedWeight_pos P.advice) P.error_real_pos

/-- The chosen threshold leaves less than the permitted later-increase budget. -/
theorem weighted_gap : Pool.weightedQueryLimsup π +
    protectedWeight P.advice * (P.advice.error : ℝ) - (P.advice.threshold : ℝ) <
      4 * protectedWeight P.advice * (P.advice.error : ℝ) := by
  have h := P.threshold_lower
  nlinarith

/-- The geometric tail is small enough for the finite weighted limit to be
strictly above the acceptance threshold. -/
theorem threshold_add_tail_lt :
    (P.advice.threshold : ℝ) + (1 / 2 : ℝ) ^ P.scanCount < Pool.weightedQueryLimsup π := by
  have h₁ := P.threshold_upper
  have h₂ := P.tail_lt
  have h₃ := P.slack_pos
  linarith

/-- The rational and real weight conventions coincide. -/
theorem cast_weight_eq (i : ℕ) : (PoolAdvice.weight i : ℝ) = Pool.weight i := by
  simp [PoolAdvice.weight, Pool.weight]

/-- The strict near-one strip used in the L1 argument is bounded by the
fixed low-set strip used to choose the margin. -/
theorem near_one_strict {i : ℕ} (hi : i < ℓ) :
    fairCoin.real {Z | 1 - 2 * (P.margin : ℝ) < Q.representative i Z ∧
      Q.representative i Z < 1} < η / 3 := by
  apply lt_of_le_of_lt (measureReal_mono (μ := fairCoin) ?_) (P.near_one i hi)
  intro Z hZ
  refine ⟨?_, hZ.1.le⟩
  change Q.representative i Z ≠ 1
  exact ne_of_lt hZ.2

/-- Fixed representatives are integrable on the probability space. -/
theorem integrable_representative (i : ℕ) : Integrable (Q.representative i) fairCoin :=
  (Pool.integrable_L2 (Q.limit i)).congr (Q.representative_ae_eq i).symm

/-- The cutoff controls final weighted coverage for every finite pool beyond
it, including the empty pool. This is the global bound used for soundness. -/
theorem final_weighted_bound (G : Finset ℕ)
    (hG : ∀ b ∈ G, P.advice.positionBound ≤ b) :
    (∑ i ∈ Finset.range P.scanCount,
      (PoolAdvice.weight i : ℝ) * ∫ Z, PoolQuery.readFraction (π i) G Z ∂fairCoin) ≤
      Pool.weightedQueryLimsup π + protectedWeight P.advice * (P.advice.error : ℝ) := by
  have hInt (i : ℕ) : (∫ Z, PoolQuery.readFraction (π i) G Z ∂fairCoin) =
      (∑ b ∈ G, Pool.queryProbability (π i) b) / G.card := by
    unfold PoolQuery.readFraction Pool.queryProbability
    rw [integral_div,
      integral_finsetSum _ (fun b _ => PoolQuery.integrable_indicator (π i) b)]
  simp_rw [hInt, cast_weight_eq, ← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  by_cases hcard : G.card = 0
  · simp only [hcard, Nat.cast_zero, div_zero]
    exact add_nonneg (Pool.weightedQueryLimsup_bounds π).1 P.slack_pos.le
  · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hcard)).mpr
    calc
      _ ≤ ∑ _b ∈ G, (Pool.weightedQueryLimsup π +
          protectedWeight P.advice * (P.advice.error : ℝ)) := by
        apply Finset.sum_le_sum
        intro b hb
        exact (sub_nonneg.mp (Pool.weighted_query_truncation π b P.scanCount).1).trans
          (P.position_upper b (hG b hb)).le
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Every accepted pair satisfies both final measure estimates on the fixed
Borel partition. The finite tables are used only inside the computation. -/
theorem accepted_measure_bounds {M : ℕ} {C : Candidate}
    (h : Accepted P.rules P.advice M C) :
    ∀ i < ℓ,
      fairCoin.real {Z | Z ∈ Q.high i ∧ PoolQuery.readFraction (π i) C.1.toFinset Z < 1} < η ∧
      fairCoin.real {Z | Z ∈ Q.low i ∧
        1 - (P.margin : ℝ) < PoolQuery.readFraction (π i) C.1.toFinset Z} < η := by
  have hπ : ∀ i < P.rules.length, P.rules[i]? = some (π i) := by
    intro i hi
    exact P.getElem?_rules (by simpa only [P.length_rules] using hi)
  have hbound : (∑ i ∈ Finset.range P.rules.length,
      (PoolAdvice.weight i : ℝ) *
        ∫ Z, PoolQuery.readFraction (π i) C.1.toFinset Z ∂fairCoin) ≤
      Pool.weightedQueryLimsup π + protectedWeight P.advice * (P.advice.error : ℝ) := by
    rw [P.length_rules]
    exact P.final_weighted_bound _ (fun b hb => h.2.2.1 b (List.mem_toFinset.mp hb))
  intro i hi
  have hi' : i < P.advice.protectedCount := by rwa [P.protected_eq]
  refine ⟨?_, ?_⟩
  · exact (h.high_failure_lt π hπ P.protected_le_length hi' (P.high_approx i hi)).trans
      P.high_budget
  · have hlow := h.low_near_full_lt π hπ P.protected_le_length hbound P.weighted_gap hi'
      (integrable_representative (Q := Q) i) (P.function_approx i hi) P.margin_real_pos
      (P.near_one_strict hi)
    apply lt_of_le_of_lt (measureReal_mono (μ := fairCoin) ?_) (hlow.trans P.low_budget)
    intro Z hZ
    exact ⟨Q.representative_lt_one_on_low i hZ.1, hZ.2⟩

/-- The chosen finite scan prefix eventually has sufficient weighted mass
along the fixed position subsequence. -/
theorem eventually_weighted_above
    (hp : Tendsto (Pool.weightedQueryProbability π ∘ Q.position) atTop
      (𝓝 (Pool.weightedQueryLimsup π))) :
    ∀ᶠ n : ℕ in atTop, (P.advice.threshold : ℝ) <
      ∑ i ∈ Finset.range P.rules.length,
        Pool.weight i * Pool.queryProbability (π i) (Q.position n) := by
  obtain ⟨ε, hε, hev⟩ := Q.eventually_finite_weighted_above hp P.scanCount
    P.threshold_add_tail_lt
  filter_upwards [hev] with n hn
  rw [P.length_rules]
  linarith

end FixedParameters

end Klr.PoolAdvice
