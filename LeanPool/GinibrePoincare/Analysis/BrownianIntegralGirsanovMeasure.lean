/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGirsanovMeasure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovVectorDensityLimit

/-!
# Brownian integral Girsanov measure

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `gaussianDensity_isProbabilityMeasure_of_integral_one`,
`brownianPredictableVectorGaussianDensity_isProbabilityMeasure`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

theorem gaussianDensity_isProbabilityMeasure_of_lintegral_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → ℝ)
    (hD : (∫⁻ ω, ENNReal.ofReal (D ω) ∂P) = 1) :
    IsProbabilityMeasure (P.withDensity (fun ω => ENNReal.ofReal (D ω))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hD

theorem gaussianDensity_isProbabilityMeasure_of_integral_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → ℝ)
    (hDi : Integrable D P) (hDp : 0 ≤ᵐ[P] D) (hD : (∫ ω, D ω ∂P) = 1) :
    IsProbabilityMeasure (P.withDensity (fun ω => ENNReal.ofReal (D ω))) := by
  apply gaussianDensity_isProbabilityMeasure_of_lintegral_one
  rw [← ofReal_integral_eq_lintegral_ofReal hDi hDp, hD, ENNReal.ofReal_one]

/-- The original predictable vector RN density defines an actual probability
measure at every finite chronological grid. -/
theorem brownianPredictableVectorGaussianDensity_isProbabilityMeasure
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω (ι → ℝ) (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (N : ℕ) : IsProbabilityMeasure (P.withDensity
      (fun ω => ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω))) :=
  gaussianDensity_isProbabilityMeasure_of_lintegral_one P _
    (brownianPredictableVectorGaussianDensity_lintegral B P hB hind h τ hτ hh N)

end
end GinibrePoincare
