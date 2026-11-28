/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The law of a finite weight vector

`Measure.ofWeights s p` is the measure `∑ i ∈ s, p i • δ_i` with the weights `p i` on the finite
set `s`: the single adaptor between the library's `Finset`-indexed weight vectors (probabilities,
state prices, spectral weights) and Mathlib's measures. For non-negative weights its integral is
the weighted sum, `∫ f ∂ofWeights s p = ∑ i ∈ s, p i * f i`, so a statement about weighted sums is
a statement about an integral, and a finite measure on a finite space is the law of its own
point masses (`ofWeights_univ_real_singleton`). It lives in `MeasureTheory.Measure` as an upstream
candidate (cf. `PMF.toMeasure`, which needs weights summing to one).

## Main definitions

* `MeasureTheory.Measure.ofWeights`: the measure `∑ i ∈ s, ofReal (p i) • dirac i`.

## Main results

* `MeasureTheory.Measure.integral_ofWeights`: `∫ f ∂ofWeights s p = ∑ i ∈ s, p i * f i` for
  non-negative weights.
* `MeasureTheory.Measure.isProbabilityMeasure_ofWeights`: weights summing to one give a
  probability measure.
* `MeasureTheory.Measure.ofWeights_univ_real_singleton`: a finite measure on a finite type with
  measurable singletons is `ofWeights univ (fun i ↦ μ.real {i})`.

## References

* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §1.1

## Tags

finite law, point masses, discrete probability, weights, Dirac measure, MSC 28A25
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {ι : Type*} [MeasurableSpace ι]

/-- **The measure with weights `p i` on the points `i ∈ s`**: `∑ i ∈ s, p i • δ_i`, with negative
weights read as `0`. -/
noncomputable def ofWeights (s : Finset ι) (p : ι → ℝ) : Measure ι :=
  ∑ i ∈ s, ENNReal.ofReal (p i) • Measure.dirac i

/-- Weights that are non-negative and sum to one give a probability measure. -/
theorem isProbabilityMeasure_ofWeights {s : Finset ι} {p : ι → ℝ} (hp0 : ∀ i ∈ s, 0 ≤ p i)
    (hp1 : ∑ i ∈ s, p i = 1) : IsProbabilityMeasure (ofWeights s p) :=
  ⟨by simp [ofWeights, ← ENNReal.ofReal_sum_of_nonneg hp0, hp1]⟩

/-- **The integral against finite weights is the weighted sum**:
`∫ f ∂(∑ i ∈ s, p i • δ_i) = ∑ i ∈ s, p i * f i` for non-negative weights. -/
theorem integral_ofWeights [MeasurableSingletonClass ι] (s : Finset ι) {p : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (f : ι → ℝ) :
    ∫ i, f i ∂ofWeights s p = ∑ i ∈ s, p i * f i := by
  have hint : ∀ i ∈ s, Integrable f (ENNReal.ofReal (p i) • Measure.dirac i) := fun i _ ↦
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [ofWeights, integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp i hi), smul_eq_mul]

/-- **A finite measure on a finite type is the law of its point masses**:
`μ = ∑ i, μ {i} • δ_i`. -/
theorem ofWeights_univ_real_singleton [Fintype ι] [MeasurableSingletonClass ι] (μ : Measure ι)
    [IsFiniteMeasure μ] : ofWeights Finset.univ (fun i ↦ μ.real {i}) = μ := by
  refine Eq.trans ?_ (Measure.sum_smul_dirac μ)
  rw [ofWeights, Measure.sum_fintype]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]

end MeasureTheory.Measure
