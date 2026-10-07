/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import LeanPool.FormalizingGMT.Densities.HausdorffUpperDensityInsideLemmas

/-!
# Density bounds for Hausdorff measure restricted to a set for points in the set

Let `X` be a metric space, `s ≥ 0`, and let `E ⊆ X` with
`H^s(E) < ∞`, where `H^s` is the `s`-dimensional Hausdorff measure.

* **Part I**. For `H^s`-almost every `x ∈ E`,

    `limsup_{r ↘ 0} H^s_∞(E ∩ B(x,r)) / (2r)^s ≥ 1 / 2^s`

  (`hausdorffContentInfty_upperDensity_ge_ae_mem`), and consequently the same holds with
  `H^s` in place of `H^s_∞` (`hausdorffMeasure_upperDensity_ge_ae_mem`).
* **Part II** (`X` locally compact and second countable, and `E` measurable with respect to the
  `s`-dimensional Hausdorff outer measure in the sense of Carathéodory). For `H^s`-almost
  every `x ∈ E`,

    `limsup_{r ↘ 0} H^s(E ∩ B(x,r)) / (2r)^s ≤ 1`

  (`hausdorffMeasure_upperDensity_le_one_ae_mem`).

All balls occurring here are *closed* metric balls. The technical lemmas are in
`FormalizingGMT/Densities/HausdorffUpperDensityInsideLemmas.lean`.
-/

@[expose] public section

open scoped BigOperators Real Nat Pointwise ENNReal NNReal
open MeasureTheory MeasureTheory.OuterMeasure Set Filter Topology

/-! ## Part I: the lower density bound -/

section Main

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Theorem 0.3.** Let `X` be a metric space (with its Borel σ-algebra), `s ≥ 0`, and let
`E ⊆ X` be any set with `H^s(E) < ∞`.  Then for `H^s`-almost every `x ∈ E`,
`limsup_{r ↘ 0} H^s_∞(E ∩ B(x,r)) / (2r)^s ≥ 1 / 2^s`;
equivalently, the set of `x ∈ E` where the upper density is `< 1/2^s` is `H^s`-null.

Neither σ-compactness of `X` nor Carathéodory measurability of `E` is assumed: the proof only
uses the finiteness `H^s(E) < ∞`. -/
theorem hausdorffContentInfty_upperDensity_ge_ae_mem {s : ℝ} (hs : 0 ≤ s)
    (E : Set X) (hE : μH[s] E ≠ ⊤) :
    μH[s] {x ∈ E | dimensionalUpperDensity
        (OuterMeasure.restrict E (hausdorffContentInftyOuter s)) s x
        < ENNReal.ofReal (1 / 2 ^ s)} = 0 := by
  rcases eq_or_lt_of_le hs with h0 | hspos
  · -- `s = 0`: the exceptional set is empty, since `H^0_∞(B(x,r) ∩ E) ≥ 1` for `x ∈ E`.
    have hset : {x ∈ E | dimensionalUpperDensity
        (OuterMeasure.restrict E (hausdorffContentInftyOuter s)) s x
        < ENNReal.ofReal (1 / 2 ^ s)} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
      intro hxE
      have hone : ENNReal.ofReal (1 / 2 ^ s) = 1 := by
        rw [← h0]; norm_num
      rw [hone, dimensionalUpperDensity]
      refine Filter.le_limsup_of_frequently_le (Filter.Eventually.frequently ?_)
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [dimensional_density_ratio_contentInfty _ _ _ (le_of_lt hr), ← h0]
      simp only [Real.rpow_zero, ENNReal.ofReal_one, div_one]
      exact one_le_hausdorffContentInfty_zero
        ⟨x, Metric.mem_closedBall_self (le_of_lt hr), hxE⟩
    rw [hset]
    exact measure_empty
  · exact measure_mono_null
      (fun x hx => mem_iUnion_cover_set_of_upper_density_lt hspos E x hx.1 hx.2)
      (hausdorffMeasure_iUnion_cover_set_eq_zero hspos E hE)

/-- **Corollary 0.1.** Under the same hypotheses (a metric space `X`, `s ≥ 0`, and any
`E ⊆ X` with `H^s(E) < ∞`; no σ-compactness or measurability of `E` is assumed), for
`H^s`-almost every `x ∈ E`,
`limsup_{r ↘ 0} H^s(E ∩ B(x,r)) / (2r)^s ≥ 1 / 2^s`, the density being taken with respect to the
restriction of the `s`-dimensional Hausdorff measure to `E`.

This follows from Theorem 0.3, because `H^s_∞ ≤ H^s_1 ≤ H^s`, so the exceptional set of the
corollary is contained in the exceptional set of the theorem. -/
theorem hausdorffMeasure_upperDensity_ge_ae_mem {s : ℝ} (hs : 0 ≤ s)
    (E : Set X) (hE : μH[s] E ≠ ⊤) :
    μH[s] {x ∈ E | dimensionalUpperDensity ((μH[s]).restrict E).toOuterMeasure s x
        < ENNReal.ofReal (1 / 2 ^ s)} = 0 := by
  refine measure_mono_null ?_ (hausdorffContentInfty_upperDensity_ge_ae_mem hs E hE)
  rintro x ⟨hxE, hlt⟩
  refine ⟨hxE, lt_of_le_of_lt ?_ hlt⟩
  refine Filter.limsup_le_limsup ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
  rw [dimensional_density_ratio_contentInfty _ _ _ hr0, density_ratio_apply _ _ _ hr0]
  gcongr
  exact le_trans (hausdorffContentInfty_le_hausdorffContent s 1 _)
    (hausdorffContent_le_hausdorffMeasure one_pos _)

end Main

/-! ## Part II: the upper density bound -/

section PartII

open Metric HausdorffDensity

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- **Theorem 0.4 (Theorem 2.7, upper bound).** Let `X` be a locally compact, second countable
metric space, `s ≥ 0`,
and let `E ⊆ X` be measurable with respect to the `s`-dimensional Hausdorff outer measure
(in the sense of Carathéodory), with `H^s(E) < ∞`. Then for `H^s`-almost every `x ∈ E`,

  `limsup_{r ↘ 0} H^s(E ∩ B(x,r)) / (2r)^s ≤ 1`,

that is, the set of points of `E` where the upper `s`-density of `H^s ⌞ E` exceeds `1` is
`H^s`-null. -/
theorem hausdorffMeasure_upperDensity_le_one_ae_mem {s : ℝ} (hs : 0 ≤ s) (E : Set X)
    (hEmeas : MeasurableSet[(OuterMeasure.mkMetric (X := X) (fun r => r ^ s)).caratheodory] E)
    (hEfin : μH[s] E ≠ ⊤) :
    μH[s] {x ∈ E | 1 < dimensionalUpperDensity ((μH[s]).restrict E).toOuterMeasure s x} = 0 := by
  -- **(m)** Each `B_{1 + 1/(n+1)}` is null, hence so is their union.
  have hnull : ∀ n : ℕ, μH[s] (superlevelSet s E (1 + ((n : ℝ≥0∞) + 1)⁻¹)) = 0 := by
    intro n
    refine superlevelSet_null hs hEmeas hEfin ?_ ?_
    · exact ENNReal.lt_add_right ENNReal.one_ne_top (ENNReal.inv_ne_zero.mpr (by simp))
    · exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.mpr (by positivity)⟩
  -- **(n)** The exceptional set is contained in that union.
  refine measure_mono_null ?_ (measure_iUnion_null hnull)
  rintro x ⟨hxE, hx⟩
  obtain ⟨n, hn⟩ := exists_nat_one_add_inv_lt hx
  exact Set.mem_iUnion.mpr ⟨n, hxE, hn⟩

end PartII
