/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralPuncturedAggregate.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedPartialContinuous
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitution
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticUnitFieldPartialMeanSquare
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionNatural

/-!
# Ginibre Brownian integral punctured aggregate

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianAggregateUniformSum_punctured_meanSquare_of_horizon_limit`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem brownianAggregateUniformSum_punctured_meanSquare_of_horizon_limit
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (F : ι → ℝ≥0 → Ω → ℝ)
    (hF : ∀ i r, @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) r) _ (F i r))
    (T : ℝ≥0) (hT : 0 < T) (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun r => F i r ω) (Set.Ioi 0))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ i r ω, ‖F i r ω‖ ≤ C)
    (J : Ω → ℝ)
    (hlim : TendstoInMeasure P (fun k ω => ∑ i, brownianUniformLeftSum (B i) (F i) T (k + 1) ω)
      atTop J) :
    MemLp J 2 P ∧ Tendsto (fun k => ∫ ω,
      ((∑ i, brownianUniformLeftSum (B i) (F i) T (k+1) ω)-J ω)^2 ∂P) atTop (𝓝 0) := by
  classical
  have hex (i : ι) := brownianPuncturedPartialIntegral_exists B P hB hind i (F i) (hF i)
    (hc i) C hC (hb i) T hT
  choose M hM hMC hML hM0 hMS using hex
  exact brownianAggregateUniformSum_meanSquare_of_coordinate_limits B P hB hind F hF C hb T
    (fun i => M i T) (fun i => hML i T)
    (fun i => by simpa only [brownianUniformPartialSum_terminal] using hMS i T le_rfl) J hlim

end
end GinibrePoincare
