/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Tactic

/-!
# Dimensional densities

This file defines dimensional density ratios and their upper and lower limits, then proves their
basic order-theoretic properties.
-/

@[expose] public section

open scoped BigOperators Real Nat Pointwise
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

variable {X : Type*} [PseudoEMetricSpace X] {μ : OuterMeasure X}

-- Section 1: Definitions

/-- The s-density ratio of an outer measure μ at point x with radius r:
    `μ(B̄(x, r)) / (2r) ^ s`.

The closed ball is taken in the extended-distance sense, `Metric.closedEBall x (ofReal r)`,
so that the definition makes sense in a `PseudoEMetricSpace`.  For `0 ≤ r` in a (pseudo)
metric space this is the usual closed ball `Metric.closedBall x r`, by
`Metric.closedEBall_ofReal`. -/
noncomputable def dimensionalDensityRatio
    (μ : OuterMeasure X) (s : ℝ) (x : X) (r : ℝ) : ℝ≥0∞ :=
  μ (Metric.closedEBall x (ENNReal.ofReal r)) / ENNReal.ofReal ((2 * r) ^ s)

/-- Upper s-density of μ at x:
    `limsup_{r → 0⁺} μ(B̄(x, r)) / (2r) ^ s`. -/
noncomputable def dimensionalUpperDensity
    (μ : OuterMeasure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.limsup (dimensionalDensityRatio μ s x) (𝓝[>] 0)

/-- Lower s-density of μ at x:
    `liminf_{r → 0⁺} μ(B̄(x, r)) / (2r) ^ s`. -/
noncomputable def dimensionalLowerDensity
    (μ : OuterMeasure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.liminf (dimensionalDensityRatio μ s x) (𝓝[>] 0)

/-- The s-dimensional density of μ at x exists if the density ratio converges as r → 0⁺. -/
class HasDensity (μ : OuterMeasure X) (s : ℝ) (x : X) : Prop where
  exists_tendsto : ∃ y, Tendsto (dimensionalDensityRatio μ s x) (𝓝[>] 0) (𝓝 y)

/-- The s-dimensional density of μ at x (Definition 1.5).

When the limit exists (`HasDensity μ s x`), this equals
`lim_{r → 0⁺} μ(B̄(x, r)) / (2r) ^ s`.
When the limit does not exist, this returns a junk value. -/
noncomputable def dimensionalDensity
    (μ : OuterMeasure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  sInf {y | Tendsto (dimensionalDensityRatio μ s x) (𝓝[>] 0) (𝓝 y)}

-- Section 2: Basic facts

/-- Comparison between lower and upper density: Θ_*^s(μ, x) ≤ Θ^{*s}(μ, x). -/
lemma lower_le_upper_density (s : ℝ) (x : X) :
    dimensionalLowerDensity μ s x ≤ dimensionalUpperDensity μ s x :=
  Filter.liminf_le_limsup
    (⟨⊤, by simp⟩)
    (⟨0, Filter.eventually_map.2 <| Filter.eventually_of_mem self_mem_nhdsWithin
      fun _ _ => bot_le⟩)

/-- Non-negativity of lower density: 0 ≤ Θ_*^s(μ, x). -/
lemma lower_density_nonneg (s : ℝ) (x : X) :
    0 ≤ dimensionalLowerDensity μ s x :=
  bot_le

/-- Non-negativity of upper density: 0 ≤ Θ^{*s}(μ, x). -/
lemma upper_density_nonneg (s : ℝ) (x : X) :
    0 ≤ dimensionalUpperDensity μ s x :=
  bot_le

/-- If the lower and upper densities are equal, then the density limit exists.

Uses `tendsto_of_liminf_eq_limsup` from Mathlib, which directly gives convergence
when `liminf = limsup` in a conditionally complete linear order with order topology
(which `ℝ≥0∞` satisfies). -/
lemma density_exists_of_lower_eq_upper (s : ℝ) (x : X)
    (h : dimensionalLowerDensity μ s x = dimensionalUpperDensity μ s x) :
    HasDensity μ s x :=
  ⟨_, tendsto_of_liminf_eq_limsup rfl h.symm⟩

/-- Lemma 2.4: If Θ_*^s(μ, x) ≥ α, then Θ^{*s}(μ, x) ≥ α. -/
lemma upper_density_ge_of_lower_density_ge (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : α ≤ dimensionalLowerDensity μ s x) :
    α ≤ dimensionalUpperDensity μ s x :=
  h.trans (lower_le_upper_density s x)

/-- Lemma 2.5: If Θ^{*s}(μ, x) ≤ α, then Θ_*^s(μ, x) ≤ α. -/
lemma lower_density_le_of_upper_density_le (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : dimensionalUpperDensity μ s x ≤ α) :
    dimensionalLowerDensity μ s x ≤ α :=
  (lower_le_upper_density s x).trans h

/-- Lemma 2.6: If Θ_*^s(μ, x) > α, then eventually (for small enough r > 0)
    the density ratio is > α. -/
lemma eventually_gt_of_lower_density_gt (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : α < dimensionalLowerDensity μ s x) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), α < dimensionalDensityRatio μ s x r :=
  Filter.eventually_lt_of_lt_liminf h

/-- Lemma 2.7: If Θ^{*s}(μ, x) < α, then eventually (for small enough r > 0)
    the density ratio is < α. -/
lemma eventually_lt_of_upper_density_lt (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : dimensionalUpperDensity μ s x < α) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), dimensionalDensityRatio μ s x r < α :=
  Filter.eventually_lt_of_limsup_lt h

/-- Lemma 2.8: If Θ_*^s(μ, x) < α, then frequently (along r → 0⁺)
    the density ratio is < α. -/
lemma frequently_lt_of_lower_density_lt (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : dimensionalLowerDensity μ s x < α) :
    ∃ᶠ r in 𝓝[>] (0 : ℝ), dimensionalDensityRatio μ s x r < α :=
  Filter.frequently_lt_of_liminf_lt ⟨⊤, fun _ _ => le_top⟩ h

/-- Lemma 2.9: If Θ^{*s}(μ, x) > α, then frequently (along r → 0⁺)
    the density ratio is > α. -/
lemma frequently_gt_of_upper_density_gt (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : α < dimensionalUpperDensity μ s x) :
    ∃ᶠ r in 𝓝[>] (0 : ℝ), α < dimensionalDensityRatio μ s x r :=
  Filter.frequently_lt_of_lt_limsup ⟨0, fun _ _ => bot_le⟩ h

-- Section 3: Comparison with the metric closed ball

section PseudoMetric

variable {Y : Type*} [PseudoMetricSpace Y]

/-- In a (pseudo) metric space, and for a nonnegative radius, the density ratio is computed
with the usual closed ball. -/
lemma dimensional_density_ratio_closedBall (ν : OuterMeasure Y) (s : ℝ) (x : Y) {r : ℝ}
    (hr : 0 ≤ r) :
    dimensionalDensityRatio ν s x r
      = ν (Metric.closedBall x r) / ENNReal.ofReal ((2 * r) ^ s) := by
  rw [dimensionalDensityRatio, Metric.closedEBall_ofReal hr]

end PseudoMetric
