/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticUnitFieldBrownian.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticPuncturedUnitFieldBrownian

/-! # Brownian integral of a continuous adapted unit field

Integrate the coordinates of the Euclidean unit field `u` against the
independent Brownian family. A continuous field is continuous at every positive
time, so this is the special case of `ginibrePuncturedUnitField_Brownian_exists`:
the integral `β` is a Brownian motion and a continuous martingale, square
integrable and started at zero, and its increments are independent of every
measurable variable in the completed original past. The conclusion retains
the uniform-sum limits on ordinary and shifted intervals so that downstream
driver-independence arguments can work with the original Brownian sums. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreUnitField_Brownian_exists
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ t, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (u t))
    (hunit : ∀ t ω, ‖u t ω‖ = 1)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => u t ω)) (i₀ : ι) :
    ∃ β : ℝ≥0 → Ω → ℝ,
      IsBrownianReal β P ∧
      Martingale β (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ t, MemLp (β t) 2 P) ∧ β 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t, TendstoInMeasure P (fun k ω =>
        ∑ i, brownianUniformLeftSum (B i) (fun s ω => u s ω i) t (k+1) ω) atTop (β t)) ∧
      (∀ s t, TendstoInMeasure P (fun k => brownianUnitShiftedUniformSum B u s t (k+1))
        atTop (fun ω => β (s+t) ω-β s ω)) ∧
      (∀ s t (Y : Ω → ℝ),
        @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P (fun i => (hB
            i).toIsPreBrownianReal) s) _ Y →
        IndepFun Y (fun ω => β (s+t) ω-β s ω) P) := by
  exact ginibrePuncturedUnitField_Brownian_exists B P hB hind u hu hunit
    (hc.mono fun ω hω => hω.continuousOn) i₀
end
end GinibrePoincare
