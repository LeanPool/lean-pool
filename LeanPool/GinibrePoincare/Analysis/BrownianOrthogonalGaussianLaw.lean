/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalGaussianLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianPredictableMeasureTransform
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Brownian orthogonal Gaussian law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `independent_past_orthogonal_gaussian_transform`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The centered Gaussian measure with covariance `v` times the identity: the image of
`stdGaussian E` under scaling by `√v`. -/
def scaledStandardGaussian (v : ℝ≥0) : Measure E :=
  (stdGaussian E).map (fun x => Real.sqrt (v : ℝ) • x)

instance scaledStandardGaussian_isProbability (v : ℝ≥0) :
    IsProbabilityMeasure (scaledStandardGaussian E v) := by
  unfold scaledStandardGaussian
  infer_instance

theorem scaledStandardGaussian_measurePreserving (v : ℝ≥0) (U : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving U (scaledStandardGaussian E v) (scaledStandardGaussian E v) := by
  refine ⟨U.continuous.measurable, ?_⟩
  unfold scaledStandardGaussian
  rw [Measure.map_map U.continuous.measurable (by fun_prop)]
  have he : (fun x => U (Real.sqrt (v : ℝ) • x)) =
      (fun x => Real.sqrt (v : ℝ) • U x) := by funext x; exact U.map_smul _ _
  change (stdGaussian E).map (fun x => U (Real.sqrt (v : ℝ) • x)) = _
  rw [he]
  change (stdGaussian E).map ((fun x => Real.sqrt (v : ℝ) • x) ∘ U) = _
  rw [← Measure.map_map (by fun_prop) U.continuous.measurable, stdGaussian_map U]

theorem independent_past_orthogonal_gaussian_transform {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    (v : ℝ≥0) (Y : Ω → A) (X : Ω → E) (hY : HasLaw Y ν P)
    (hX : HasLaw X (scaledStandardGaussian E v) P) (hi : IndepFun Y X P)
    (U : A → E ≃ₗᵢ[ℝ] E) (hU : Measurable (fun p : A × E => U p.1 p.2)) :
    HasLaw (fun ω => U (Y ω) (X ω)) (scaledStandardGaussian E v) P ∧
      IndepFun Y (fun ω => U (Y ω) (X ω)) P := by
  exact independent_past_measure_transform P ν (scaledStandardGaussian E v) Y X hY hX hi
    (fun a x => U a x) hU (fun a => scaledStandardGaussian_measurePreserving E v (U a))

end
end GinibrePoincare
