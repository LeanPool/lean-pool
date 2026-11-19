/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralExponentialApproximation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralHorizon
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoDriftRiemann
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoConvergenceInMeasure

/-!
# Ginibre Brownian integral exponential approximation

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianVectorTimeEnergyUniformSum_tendstoInMeasure`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The quadratic energy `∫ s in 0..T, ∑ i, (F i s ω) ^ 2` of the vector integrand `F`. -/
def brownianVectorTimeEnergy {Ω ι : Type*} [Fintype ι]
    (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(T : ℝ), ∑ i, (F i (Real.toNNReal s) ω)^2

/-- The Riemann sum of `∑ i, (F i · ω) ^ 2` over the `n + 1` uniform grid times
`ginibreUniformBrownianTime T n k`, each weighted by `T / (n + 1)`. -/
def brownianVectorTimeEnergyUniformSum {Ω ι : Type*} [Fintype ι]
    (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k : Fin (n+1), (∑ i, (F i (ginibreUniformBrownianTime T n k) ω)^2)*
    ((T : ℝ)/((n : ℝ)+1))

/-- Actual vector energy Riemann sums converge almost surely to the time integral. -/
theorem brownianVectorTimeEnergyUniformSum_tendsto_ae {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Icc 0 T)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => brownianVectorTimeEnergyUniformSum F T n ω)
      atTop (𝓝 (brownianVectorTimeEnergy F T ω)) := by
  have hall : ∀ᵐ ω ∂P, ∀ i, ContinuousOn (fun s => F i s ω) (Icc 0 T) := ae_all_iff.mpr hc
  filter_upwards [hall] with ω hω
  have hfi (i : ι) : ContinuousOn (fun s : ℝ => F i (Real.toNNReal s) ω) (Icc 0 (T : ℝ)) :=
    (hω i).comp continuous_real_toNNReal.continuousOn (by
      intro s hs
      constructor
      · positivity
      · simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hs.2)
  have he : ContinuousOn (fun s : ℝ => ∑ i, (F i (Real.toNNReal s) ω)^2) (Icc 0 (T : ℝ)) :=
    continuousOn_finsetSum Finset.univ fun i _ => (hfi i).pow 2
  have ht := itoContinuousScalarRiemann_fin_tendsto
    (fun s : ℝ => ∑ i, (F i (Real.toNNReal s) ω)^2) T he
  simpa only [Real.toNNReal_coe, brownianVectorTimeEnergyUniformSum, brownianVectorTimeEnergy] using
      ht

theorem brownianVectorTimeEnergyUniformSum_measurable {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hm : ∀ i t, Measurable (F i t)) (n : ℕ) :
    Measurable (brownianVectorTimeEnergyUniformSum F T n) := by
  classical
  unfold brownianVectorTimeEnergyUniformSum
  apply Finset.measurable_sum
  intro k hk
  apply Measurable.mul_const
  apply Finset.measurable_sum
  intro i hi
  exact (hm i _).pow_const 2

/-- Energy convergence in probability is derived from actual path continuity. -/
theorem brownianVectorTimeEnergyUniformSum_tendstoInMeasure {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsFiniteMeasure P]
    (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hm : ∀ i t, Measurable (F i t))
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Icc 0 T)) :
    TendstoInMeasure P (brownianVectorTimeEnergyUniformSum F T) atTop
      (brownianVectorTimeEnergy F T) :=
  tendstoInMeasure_of_tendsto_ae
    (fun n => (brownianVectorTimeEnergyUniformSum_measurable F T hm n).aestronglyMeasurable)
    (brownianVectorTimeEnergyUniformSum_tendsto_ae P F T hc)

end
end GinibrePoincare
