/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolPartitionRepresentative
public import LeanPool.KLRandomness.PoolQuery

/-!
# Fixed Borel partitions for the actual query indicators

This file applies the Hilbert-space compactness theorem to the actual events
`PoolQuery.Reads`.  The resulting partitions depend only on the countable scan
family and the initial sequence of positions.  In particular, their choice
precedes the finite prefix of scans, the error tolerance, and the pool size.

The same extraction preserves convergence of any scalar statistic previously
arranged along the initial sequence, including the weighted query probability.
-/

@[expose] public section

noncomputable section

namespace Klr.Pool

open Filter MeasureTheory Set Topology
open scoped ENNReal

/-- The actual eventual-query indicator as an `L²` vector. -/
def queryL2 (π : ScanRule) (a : ℕ) : Lp ℝ 2 fairCoin :=
  indicatorConstLp 2 (PoolQuery.measurableSet_reads π a)
    (measure_ne_top fairCoin _) (1 : ℝ)

theorem queryL2_coeFn (π : ScanRule) (a : ℕ) :
    queryL2 π a =ᵐ[fairCoin] PoolQuery.indicator π a :=
  indicatorConstLp_coeFn

theorem queryL2_nonneg (π : ScanRule) (a : ℕ) :
    ∀ᵐ Z ∂fairCoin, 0 ≤ queryL2 π a Z := by
  filter_upwards [queryL2_coeFn π a] with Z hZ
  rw [hZ]
  exact (PoolQuery.indicator_bounds π a Z).1

theorem queryL2_le_one (π : ScanRule) (a : ℕ) :
    ∀ᵐ Z ∂fairCoin, queryL2 π a Z ≤ 1 := by
  filter_upwards [queryL2_coeFn π a] with Z hZ
  rw [hZ]
  exact (PoolQuery.indicator_bounds π a Z).2

theorem norm_queryL2_le_one (π : ScanRule) (a : ℕ) : ‖queryL2 π a‖ ≤ 1 :=
  norm_le_one_of_ae_unitInterval (queryL2_nonneg π a) (queryL2_le_one π a)

/-- The common weak limits and their subsequence, obtained from the actual
query indicators.  `exists_queryPartition` proves this structure inhabited. -/
structure QueryPartition (π : ℕ → ScanRule) (a : ℕ → ℕ) where
  /-- The common subsequence of query positions used for weak convergence. -/
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  /-- Weak limit in the fair-coin Hilbert space for each scan. -/
  limit : ℕ → Lp ℝ 2 fairCoin
  weak : ∀ i, WeaklyConverges (fun n => queryL2 (π i) (a (subseq n))) (limit i)
  limit_nonneg : ∀ i, ∀ᵐ Z ∂fairCoin, 0 ≤ limit i Z
  limit_le_one : ∀ i, ∀ᵐ Z ∂fairCoin, limit i Z ≤ 1

/-- Genuine existence of the common weak limits, using only Mathlib's
Banach--Alaoglu and Riesz theorems and the actual query events. -/
theorem exists_queryPartition (π : ℕ → ScanRule) (a : ℕ → ℕ) :
    Nonempty (QueryPartition π a) := by
  obtain ⟨φ, g, hφ, hweak, hg0, hg1⟩ :=
    exists_unitInterval_weak_limits (fun i n => queryL2 (π i) (a n))
      (fun i n => queryL2_nonneg (π i) (a n))
      (fun i n => queryL2_le_one (π i) (a n))
  exact ⟨⟨φ, hφ, g, hweak, hg0, hg1⟩⟩

namespace QueryPartition

variable {π : ℕ → ScanRule} {a : ℕ → ℕ} (D : QueryPartition π a)

/-- The common sequence of positions after weak-limit extraction. -/
def position (n : ℕ) : ℕ := a (D.subseq n)

/-- The Borel representative used in the fixed partition. -/
def representative (i : ℕ) : Cantor → ℝ := clippedRepresentative (D.limit i)

/-- The fixed Borel high set. -/
def high (i : ℕ) : Set Cantor := clippedHighSet (D.limit i)

/-- The complementary fixed Borel low set. -/
def low (i : ℕ) : Set Cantor := clippedLowSet (D.limit i)

theorem measurable_representative (i : ℕ) : Measurable (D.representative i) :=
  measurable_clippedRepresentative _

theorem representative_bounds (i : ℕ) (Z : Cantor) :
    0 ≤ D.representative i Z ∧ D.representative i Z ≤ 1 :=
  clippedRepresentative_bounds _ _

theorem representative_ae_eq (i : ℕ) :
    D.representative i =ᵐ[fairCoin] D.limit i :=
  clippedRepresentative_ae_eq _ (D.limit_nonneg i) (D.limit_le_one i)

theorem measurableSet_high (i : ℕ) : MeasurableSet (D.high i) :=
  measurableSet_clippedHighSet _

theorem measurableSet_low (i : ℕ) : MeasurableSet (D.low i) :=
  measurableSet_clippedLowSet _

theorem disjoint_high_low (i : ℕ) : Disjoint (D.high i) (D.low i) :=
  disjoint_clippedHighSet_clippedLowSet _

theorem high_union_low (i : ℕ) : D.high i ∪ D.low i = univ :=
  clippedHighSet_union_clippedLowSet _

theorem representative_eq_one_on_high (i : ℕ) {Z : Cantor} (hZ : Z ∈ D.high i) :
    D.representative i Z = 1 := hZ

theorem representative_lt_one_on_low (i : ℕ) {Z : Cantor} (hZ : Z ∈ D.low i) :
    D.representative i Z < 1 := clippedRepresentative_lt_one_on_low _ hZ

theorem low_eq_lt_one (i : ℕ) : D.low i = {Z | D.representative i Z < 1} := by
  ext Z
  constructor
  · exact D.representative_lt_one_on_low i
  · exact fun hZ => ne_of_lt hZ

theorem positions_strictMono (ha : StrictMono a) : StrictMono D.position :=
  ha.comp D.subseq_strictMono

theorem positions_tendsto (ha : Tendsto a atTop atTop) :
    Tendsto D.position atTop atTop := ha.comp D.subseq_strictMono.tendsto_atTop

/-- Any scalar convergence arranged along the starting positions survives the
one common weak-limit extraction. -/
theorem scalar_tendsto {p : ℕ → ℝ} {pstar : ℝ}
    (hp : Tendsto (p ∘ a) atTop (𝓝 pstar)) :
    Tendsto (p ∘ D.position) atTop (𝓝 pstar) :=
  hp.comp D.subseq_strictMono.tendsto_atTop

/-- On each fixed high set, the probability of missing the current position
tends to zero along the actual query subsequence. -/
theorem high_miss_tendsto_zero (i : ℕ) :
    Tendsto (fun n => fairCoin.real (D.high i \ {Z | PoolQuery.Reads (π i) (D.position n) Z}))
      atTop (𝓝 0) :=
  clipped_high_miss_tendsto_zero
    (fun n => {Z | PoolQuery.Reads (π i) (D.position n) Z})
    (fun n => PoolQuery.measurableSet_reads (π i) (D.position n))
    (D.weak i) (D.limit_nonneg i) (D.limit_le_one i)

/-- One positive rational margin works for a finite prefix of the fixed low
sets, independently of the subsequently chosen pool size. -/
theorem exists_rational_margin (ℓ : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ τ : ℚ, 0 < τ ∧ τ < 1 / 4 ∧
      ∀ i < ℓ, fairCoin.real
        {Z | Z ∈ D.low i ∧ 1 - 2 * (τ : ℝ) ≤ D.representative i Z} < η :=
  exists_rational_clipped_low_margin D.limit D.limit_nonneg D.limit_le_one ℓ hη

end QueryPartition

end Klr.Pool
