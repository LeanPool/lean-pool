/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalEquilibriumInputs.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalIndependentProduct
public import LeanPool.GinibrePoincare.Analysis.EquilibriumProbability

/-!
# Brownian orthogonal equilibrium inputs

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibre_equilibrium_center_relative_inputs_independent`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous complex paths `C(ℝ, ℂ)`. -/
local instance instBorelBrownianOrthogonalEquilibriumInputs56 : MeasurableSpace C(ℝ, ℂ) := borel _
local instance : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩

/-- The actual Ginibre initial center and its Brownian noise are independent of
 the actual initial relative configuration and its entire relative noise path. -/
theorem ginibre_equilibrium_center_relative_inputs_independent {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) :
    IndepFun
      (fun p => (coordinateSum p.1,
        ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α p.2)))
      (fun p => (recenteredConfiguration n p.1,
        ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α p.2)))
      ((ginibreMeasure n).prod P) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hN := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  apply independent_pairs_on_product_measure (ginibreMeasure n) P
    (coordinateSum : Configuration n → ℂ) (recenteredConfiguration n)
    (fun ω => ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω))
    (fun ω => ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α ω))
  · convert (coordinateSumCLM n).continuous.measurable using 1
    funext z
    exact (coordinateSumCLM_apply n z).symm
  · convert (recenteredCLM n).continuous.measurable using 1
    funext z
    exact (recenteredCLM_apply n z).symm
  · exact (ginibreContinuousNoiseCenter_continuous n).measurable.comp hN
  · exact (ginibreContinuousNoiseRecenter_continuous n).measurable.comp hN
  · exact coordinateSum_recentered_indepFun n hn
  · exact brownianFamily_actual_continuous_center_recenter_noise_independent hn B P hB hind α

end
end GinibrePoincare
