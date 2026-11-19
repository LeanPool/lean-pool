/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralLimitTransfer.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralL2Completion
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticMeanSquareInProbability

/-!
# Ginibre Brownian integral limit transfer

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `actualMeanSquareLimit_transfer`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- A vanishing actual mean-square comparison transfers an actual L² limit. -/
theorem actualMeanSquareLimit_transfer {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S R : ℕ → Ω → ℝ) (I : Ω → ℝ)
    (hS : ∀ n, MemLp (S n) 2 P) (hR : ∀ n, MemLp (R n) 2 P)
    (hI : MemLp I 2 P)
    (hcomp : Tendsto (fun n => ∫ ω, (S n ω - R n ω) ^ 2 ∂P) atTop (𝓝 0))
    (hlim : Tendsto (fun n => ∫ ω, (S n ω - I ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (R n ω-I ω)^2 ∂P) atTop (𝓝 0) := by
  have hle (n : ℕ) : (∫ ω, (R n ω-I ω)^2 ∂P) ≤
      2*(∫ ω, (S n ω-R n ω)^2 ∂P)+2*(∫ ω, (S n ω-I ω)^2 ∂P) := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add]
    · apply integral_mono ((hR n).sub hI).integrable_sq
        ((((hS n).sub (hR n)).integrable_sq.const_mul 2).add
          (((hS n).sub hI).integrable_sq.const_mul 2))
      intro ω
      dsimp only [Pi.add_apply, Pi.sub_apply]
      nlinarith [sq_nonneg (S n ω-R n ω + (S n ω-I ω))]
    · exact (((hS n).sub (hR n)).integrable_sq.const_mul 2)
    · exact (((hS n).sub hI).integrable_sq.const_mul 2)
  apply squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) hle
  simpa using (hcomp.const_mul 2).add (hlim.const_mul 2)

end
end GinibrePoincare
