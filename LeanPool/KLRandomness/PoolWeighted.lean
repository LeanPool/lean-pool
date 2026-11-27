/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolPartitionQuery
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Weighted query probabilities and the limsup subsequence

The paper numbers scans starting at one.  Our zero-based index therefore has
`weight i = 2⁻(i+1)`, using exactly the paper's weights, whose sum is one.

The weighted query probability is an actual convergent series with a uniform
geometric tail bound.  We extract positions tending to infinity along which
this probability tends to its limsup, and prove the eventual upper bound used
in the finite pool construction.  The common weak-limit extraction preserves
this scalar limit.  Dominated convergence for series identifies the limsup
with the weighted integrals of the weak limits.
-/

@[expose] public section

noncomputable section

namespace Klr.Pool

open Filter MeasureTheory Set Topology
open scoped ENNReal BigOperators

/-- Normalized geometric weights on the countable family of scans. -/
def weight (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ (i + 1)

theorem weight_pos (i : ℕ) : 0 < weight i := by
  unfold weight
  positivity

theorem weight_nonneg (i : ℕ) : 0 ≤ weight i := (weight_pos i).le

theorem summable_weight : Summable weight := by
  change Summable (fun i => (1 / 2 : ℝ) ^ (i + 1))
  simpa only [pow_succ] using summable_geometric_two.mul_right (1 / 2)

theorem tsum_weight : ∑' i, weight i = 1 := by
  simp only [weight, pow_succ, tsum_mul_right, tsum_geometric_two]
  norm_num

theorem tsum_weight_tail (D : ℕ) : ∑' i, weight (i + D) = (1 / 2 : ℝ) ^ D := by
  calc
    ∑' i, weight (i + D) = ∑' i, weight i * (1 / 2 : ℝ) ^ D := by
      apply tsum_congr
      intro i
      simp only [weight, ← pow_add]
      congr 1
      omega
    _ = (∑' i, weight i) * (1 / 2 : ℝ) ^ D := tsum_mul_right
    _ = (1 / 2 : ℝ) ^ D := by rw [tsum_weight, one_mul]

/-- The probability that the scan eventually queries the stated position. -/
def queryProbability (π : ScanRule) (a : ℕ) : ℝ :=
  ∫ Z, PoolQuery.indicator π a Z ∂fairCoin

theorem queryProbability_nonneg (π : ScanRule) (a : ℕ) : 0 ≤ queryProbability π a :=
  integral_nonneg fun Z => (PoolQuery.indicator_bounds π a Z).1

theorem queryProbability_le_one (π : ScanRule) (a : ℕ) : queryProbability π a ≤ 1 := by
  calc
    queryProbability π a ≤ ∫ _Z : Cantor, (1 : ℝ) ∂fairCoin :=
      integral_mono (PoolQuery.integrable_indicator π a) (integrable_const 1)
        fun Z => (PoolQuery.indicator_bounds π a Z).2
    _ = 1 := by simp

theorem queryProbability_eq_measureReal (π : ScanRule) (a : ℕ) :
    queryProbability π a = fairCoin.real {Z | PoolQuery.Reads π a Z} := by
  unfold queryProbability PoolQuery.indicator
  rw [integral_indicator_const 1 (PoolQuery.measurableSet_reads π a)]
  simp

theorem integral_queryL2 (π : ScanRule) (a : ℕ) :
    ∫ Z, queryL2 π a Z ∂fairCoin = queryProbability π a :=
  integral_congr_ae (queryL2_coeFn π a)

/-- The normalized weighted eventual-query probability of a position. -/
def weightedQueryProbability (π : ℕ → ScanRule) (a : ℕ) : ℝ :=
  ∑' i, weight i * queryProbability (π i) a

theorem weighted_term_nonneg (π : ℕ → ScanRule) (a i : ℕ) :
    0 ≤ weight i * queryProbability (π i) a :=
  mul_nonneg (weight_nonneg i) (queryProbability_nonneg _ _)

theorem weighted_term_le_weight (π : ℕ → ScanRule) (a i : ℕ) :
    weight i * queryProbability (π i) a ≤ weight i :=
  mul_le_of_le_one_right (weight_nonneg i) (queryProbability_le_one _ _)

theorem summable_weighted_query (π : ℕ → ScanRule) (a : ℕ) :
    Summable (fun i => weight i * queryProbability (π i) a) :=
  Summable.of_nonneg_of_le (weighted_term_nonneg π a) (weighted_term_le_weight π a)
    summable_weight

theorem weightedQueryProbability_nonneg (π : ℕ → ScanRule) (a : ℕ) :
    0 ≤ weightedQueryProbability π a :=
  tsum_nonneg (weighted_term_nonneg π a)

theorem weightedQueryProbability_le_one (π : ℕ → ScanRule) (a : ℕ) :
    weightedQueryProbability π a ≤ 1 := by
  calc
    weightedQueryProbability π a ≤ ∑' i, weight i :=
      (summable_weighted_query π a).tsum_le_tsum (weighted_term_le_weight π a) summable_weight
    _ = 1 := tsum_weight

/-- The omitted scans contribute at most the geometric tail, uniformly in the
position. -/
theorem weighted_query_tail_le (π : ℕ → ScanRule) (a D : ℕ) :
    (∑' i, weight (i + D) * queryProbability (π (i + D)) a) ≤ (1 / 2 : ℝ) ^ D := by
  have hleft := (summable_weighted_query π a).comp_injective
    (fun i j (h : i + D = j + D) => Nat.add_right_cancel h)
  have hright := summable_weight.comp_injective
    (fun i j (h : i + D = j + D) => Nat.add_right_cancel h)
  calc
    (∑' i, weight (i + D) * queryProbability (π (i + D)) a) ≤ ∑' i, weight (i + D) :=
      hleft.tsum_le_tsum (fun i => weighted_term_le_weight π a (i + D)) hright
    _ = (1 / 2 : ℝ) ^ D := tsum_weight_tail D

theorem weighted_query_truncation (π : ℕ → ScanRule) (a D : ℕ) :
    0 ≤ weightedQueryProbability π a -
      ∑ i ∈ Finset.range D, weight i * queryProbability (π i) a ∧
    weightedQueryProbability π a -
      ∑ i ∈ Finset.range D, weight i * queryProbability (π i) a ≤ (1 / 2 : ℝ) ^ D := by
  have hsplit := (summable_weighted_query π a).sum_add_tsum_nat_add D
  have htail0 : 0 ≤ ∑' i, weight (i + D) * queryProbability (π (i + D)) a :=
    tsum_nonneg fun i => weighted_term_nonneg π a (i + D)
  have htail1 := weighted_query_tail_le π a D
  change _ = weightedQueryProbability π a at hsplit
  constructor <;> linarith

/-- The weighted-probability limsup at positions tending to infinity. -/
def weightedQueryLimsup (π : ℕ → ScanRule) : ℝ :=
  limsup (weightedQueryProbability π) atTop

theorem weighted_query_isBounded (π : ℕ → ScanRule) :
    IsBoundedUnder (· ≤ ·) atTop (weightedQueryProbability π) :=
  isBoundedUnder_of ⟨1, weightedQueryProbability_le_one π⟩

theorem weighted_query_isCobounded (π : ℕ → ScanRule) :
    IsCoboundedUnder (· ≤ ·) atTop (weightedQueryProbability π) :=
  isCoboundedUnder_le_of_le atTop (weightedQueryProbability_nonneg π)

/-- Positions tend to infinity while their weighted query probabilities tend
to the actual limsup. -/
theorem exists_weighted_limsup_sequence (π : ℕ → ScanRule) :
    ∃ a : ℕ → ℕ, Tendsto a atTop atTop ∧
      Tendsto (weightedQueryProbability π ∘ a) atTop (𝓝 (weightedQueryLimsup π)) := by
  obtain ⟨a, hp, ha⟩ := exists_seq_tendsto_limsup
    (weighted_query_isCobounded π) (weighted_query_isBounded π)
  exact ⟨a, ha, hp⟩

theorem weightedQueryLimsup_bounds (π : ℕ → ScanRule) :
    0 ≤ weightedQueryLimsup π ∧ weightedQueryLimsup π ≤ 1 := by
  obtain ⟨a, _, hp⟩ := exists_weighted_limsup_sequence π
  exact ⟨ge_of_tendsto' hp (fun n => weightedQueryProbability_nonneg π (a n)),
    le_of_tendsto' hp (fun n => weightedQueryProbability_le_one π (a n))⟩

/-- After a sufficiently large position, every weighted query probability is
below the limsup plus any prescribed positive error. -/
theorem eventually_weighted_query_lt (π : ℕ → ScanRule) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℕ in atTop, weightedQueryProbability π a < weightedQueryLimsup π + ε :=
  eventually_lt_of_limsup_lt (lt_add_of_pos_right _ hε) (weighted_query_isBounded π)

theorem exists_weighted_query_upper_cutoff (π : ℕ → ScanRule) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℕ, ∀ a ≥ z, weightedQueryProbability π a < weightedQueryLimsup π + ε :=
  eventually_atTop.mp (eventually_weighted_query_lt π hε)

namespace QueryPartition

variable {π : ℕ → ScanRule} {a : ℕ → ℕ} (D : QueryPartition π a)

theorem integral_representative (i : ℕ) :
    ∫ Z, D.representative i Z ∂fairCoin = ∫ Z, D.limit i Z ∂fairCoin :=
  integral_congr_ae (D.representative_ae_eq i)

theorem integral_limit_nonneg (i : ℕ) : 0 ≤ ∫ Z, D.limit i Z ∂fairCoin :=
  integral_nonneg_of_ae (D.limit_nonneg i)

theorem integral_limit_le_one (i : ℕ) : (∫ Z, D.limit i Z ∂fairCoin) ≤ 1 := by
  calc
    (∫ Z, D.limit i Z ∂fairCoin) ≤ ∫ _Z : Cantor, (1 : ℝ) ∂fairCoin :=
      integral_mono_ae (integrable_L2 (D.limit i)) (integrable_const 1) (D.limit_le_one i)
    _ = 1 := by simp

theorem queryProbability_tendsto (i : ℕ) :
    Tendsto (fun n => queryProbability (π i) (D.position n)) atTop
      (𝓝 (∫ Z, D.limit i Z ∂fairCoin)) := by
  simpa only [Measure.restrict_univ, integral_queryL2, position] using
    (D.weak i).setIntegral MeasurableSet.univ

theorem finite_weighted_tendsto (k : ℕ) :
    Tendsto (fun n => ∑ i ∈ Finset.range k, weight i * queryProbability (π i) (D.position n))
      atTop (𝓝 (∑ i ∈ Finset.range k, weight i * ∫ Z, D.limit i Z ∂fairCoin)) :=
  tendsto_finsetSum (Finset.range k)
    (fun i _ => (D.queryProbability_tendsto i).const_mul (weight i))

/-- Weighted means commute with the common weak limit, because the normalized
geometric weights dominate all query probabilities. -/
theorem weighted_tendsto :
    Tendsto (weightedQueryProbability π ∘ D.position) atTop
      (𝓝 (∑' i, weight i * ∫ Z, D.limit i Z ∂fairCoin)) := by
  have h := tendsto_tsum_of_dominated_convergence summable_weight
    (fun i => (D.queryProbability_tendsto i).const_mul (weight i))
    (Filter.Eventually.of_forall fun n i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (weighted_term_nonneg π (D.position n) i)]
      exact weighted_term_le_weight π (D.position n) i)
  exact h

theorem weighted_limit_eq_limsup
    (hp : Tendsto (weightedQueryProbability π ∘ a) atTop (𝓝 (weightedQueryLimsup π))) :
    (∑' i, weight i * ∫ Z, D.limit i Z ∂fairCoin) = weightedQueryLimsup π :=
  tendsto_nhds_unique D.weighted_tendsto (D.scalar_tendsto hp)

/-- Finite truncation of the limiting weighted integrals has the same uniform
geometric error bound as the original query probabilities. -/
theorem weighted_limit_truncation {pstar : ℝ}
    (hp : Tendsto (weightedQueryProbability π ∘ D.position) atTop (𝓝 pstar)) (k : ℕ) :
    0 ≤ pstar - ∑ i ∈ Finset.range k, weight i * ∫ Z, D.limit i Z ∂fairCoin ∧
    pstar - ∑ i ∈ Finset.range k, weight i * ∫ Z, D.limit i Z ∂fairCoin ≤
      (1 / 2 : ℝ) ^ k := by
  have hdiff := hp.sub (D.finite_weighted_tendsto k)
  exact ⟨ge_of_tendsto' hdiff (fun n => (weighted_query_truncation π (D.position n) k).1),
    le_of_tendsto' hdiff (fun n => (weighted_query_truncation π (D.position n) k).2)⟩

/-- A rational or real threshold below the limiting finite-prefix mass has a
fixed positive slack, eventually along the query subsequence. -/
theorem eventually_finite_weighted_above {pstar γ : ℝ}
    (hp : Tendsto (weightedQueryProbability π ∘ D.position) atTop (𝓝 pstar)) (k : ℕ)
    (hγ : γ + (1 / 2 : ℝ) ^ k < pstar) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
      γ + ε < ∑ i ∈ Finset.range k, weight i * queryProbability (π i) (D.position n) := by
  let S : ℝ := ∑ i ∈ Finset.range k, weight i * ∫ Z, D.limit i Z ∂fairCoin
  have hS : γ < S := by
    have ht := (D.weighted_limit_truncation hp k).2
    dsimp [S]
    linarith
  refine ⟨(S - γ) / 2, by linarith, ?_⟩
  have hmid : γ + (S - γ) / 2 < S := by linarith
  exact (D.finite_weighted_tendsto k).eventually (lt_mem_nhds hmid)

end QueryPartition

/-- The fixed Borel partition data can be chosen along positions tending to
infinity and preserving the weighted limsup. -/
theorem exists_weighted_queryPartition (π : ℕ → ScanRule) :
    ∃ (a : ℕ → ℕ) (D : QueryPartition π a), Tendsto D.position atTop atTop ∧
      Tendsto (weightedQueryProbability π ∘ D.position) atTop (𝓝 (weightedQueryLimsup π)) ∧
      (∑' i, weight i * ∫ Z, D.limit i Z ∂fairCoin) = weightedQueryLimsup π := by
  obtain ⟨a, ha, hp⟩ := exists_weighted_limsup_sequence π
  obtain ⟨D⟩ := exists_queryPartition π a
  exact ⟨a, D, D.positions_tendsto ha, D.scalar_tendsto hp, D.weighted_limit_eq_limsup hp⟩

end Klr.Pool
