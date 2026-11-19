/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralPuncturedSubstitution.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedAggregate
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticPuncturedUnitFieldPartialMeanSquare

/-!
# Ginibre Brownian integral punctured substitution

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianPuncturedUnitIntegral_bounded_substitution_of_horizon_limits`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Genuine stochastic substitution under natural bounded continuous
unit-field assumptions, with integral values specified only by actual horizon
limits in probability. Mean-square limits and refinement control are derived. -/
theorem brownianPuncturedUnitIntegral_bounded_substitution_of_horizon_limits
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ r, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) r) _ (u r))
    (hunit : ∀ r ω, ‖u r ω‖ = 1) (huc : ∀ᵐ ω ∂P, ContinuousOn (fun r => u r ω) (Set.Ioi 0))
    (A : ℝ≥0 → Ω → ℝ)
    (hA : ∀ r, @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) r) _ (A r))
    (C : ℝ) (hC : 0 ≤ C) (hAb : ∀ r ω, ‖A r ω‖ ≤ C)
    (T : ℝ≥0) (hT : 0 < T) (hc : ∀ᵐ ω ∂P, Continuous (fun r => A r ω))
    (β : ℝ≥0 → Ω → ℝ)
    (hβM : Martingale β (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) P) (hβ : ∀ r, MemLp (β r) 2 P)
    (hβlim : ∀ r, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω => u s ω i) r (k + 1) ω) atTop (β r))
    (J : Ω → ℝ)
    (hJlim : TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun r ω => A r ω * u r ω i) T (k + 1) ω) atTop J) :
    Tendsto (fun k => ∫ ω, (brownianUniformLeftSum β A T (k+1) ω-J ω)^2 ∂P)
      atTop (𝓝 0) := by
  classical
  have hum (i : ι) (r : ℝ≥0) : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) r) _
      (fun ω => u r ω i) := (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).measurable.comp (hu r)
  have hub (i : ι) (r : ℝ≥0) (ω : Ω) : ‖u r ω i‖≤1 := by
    simpa only [hunit r ω] using PiLp.norm_apply_le (u r ω) i
  have hProd := brownianAggregateUniformSum_punctured_meanSquare_of_horizon_limit B P hB hind
    (fun i r ω => A r ω*u r ω i) (fun i r => (hA r).mul (hum i r)) T hT
    (fun i => by
      filter_upwards [hc, huc] with ω hω hωu
      exact hω.continuousOn.mul ((PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).comp_continuousOn
          hωu))
    C hC (fun i r ω => by
      rw [norm_mul]
      calc
        ‖A r ω‖*‖u r ω i‖ ≤ C*‖u r ω i‖ :=
          mul_le_mul_of_nonneg_right (hAb r ω) (norm_nonneg _)
        _ ≤ C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hub i r ω) hC) J hJlim
  exact brownianIntegral_bounded_substitution_meanSquare B P
    (fun i => (hB i).toIsPreBrownianReal) hind A (fun i r ω => u r ω i) hA hum
    C 1 hC (by norm_num) hAb hub T (hc.mono fun ω hω => hω.continuousOn) β hβ
    (fun r hr => ginibrePuncturedUnitField_partial_meanSquare_of_horizon_limits
      B P hB hind u hu hunit huc β hβM hβlim T r hT hr) J hProd.1 hProd.2

end
end GinibrePoincare
