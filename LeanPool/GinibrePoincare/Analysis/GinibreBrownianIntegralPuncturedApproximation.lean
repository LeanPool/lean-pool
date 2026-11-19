/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralPuncturedApproximation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedPartialApproximation

/-! Genuine continuous stochastic integral approximants for a bounded adapted
integrand continuous at every positive time. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem brownianPuncturedIntegral_continuous_approximants {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal) t) _ (F t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => F t ω) (Set.Ioi 0))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ω, ‖F t ω‖ ≤ C)
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ M : ℕ → ℝ≥0 → Ω → ℝ,
      (∀ n, Martingale (M n) (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P) ∧
      (∀ n ω, Continuous (fun t => M n t ω)) ∧
      (∀ n t, MemLp (M n t) 2 P) ∧
      (∀ n, M n 0 =ᵐ[P] (fun _ => 0)) ∧
      (∀ (n : ℕ) (t : ℝ≥0), t ≤ T → Tendsto (fun k => ∫ ω,
        (brownianUniformLeftSum (B j) (brownianInitialTimeCutoff F (1/((n : ℝ)+1)))
          t (k+1) ω-M n t ω)^2 ∂P) atTop (𝓝 0)) ∧
      Tendsto (fun q : ℕ × ℕ => ∫ ω, (M q.1 T ω-M q.2 T ω)^2 ∂P) atTop (𝓝 0) := by
  obtain ⟨M, hM, hMC, hML, hM0, hleft, -, hterm⟩ :=
    brownianPuncturedIntegral_partial_approximants B P hB hind j F hF hc C hC hb T hT
  exact ⟨M, hM, hMC, hML, hM0, hleft, hterm⟩

end
end GinibrePoincare
