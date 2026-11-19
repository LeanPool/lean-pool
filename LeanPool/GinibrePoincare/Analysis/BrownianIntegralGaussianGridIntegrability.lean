/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianGridIntegrability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianGridComparison
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralFrozenStep

/-!
# Brownian integral Gaussian grid integrability

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianActualLeftGridSum_memLp_two`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem brownianActualLeftGridSum_memLp_two
    {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (a : ℕ → ℝ≥0) (ha : Monotone a) (N : ℕ) :
    MemLp (brownianActualLeftGridSum (B j) F a N) 2 P := by
  have := Fintype.ofFinite ι
  apply memLp_finsetSum
  intro k hk
  have hh := brownianFrozenStep_memLp_two B P hB hind j (F (a k)) (a k)
    (a (k+1)) (a (k+1)) (hF _) (hFi _)
  have he : brownianFrozenStep (B j) (F (a k)) (a k) (a (k+1)) (a (k+1)) =
      (fun ω => F (a k) ω*(B j (a (k+1)) ω-B j (a k) ω)) := by
    funext ω
    simp [brownianFrozenStep, max_eq_right (ha (Nat.le_succ k))]
  rw [he] at hh
  exact hh

end
end GinibrePoincare
