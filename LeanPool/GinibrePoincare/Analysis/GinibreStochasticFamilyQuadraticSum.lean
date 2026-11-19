/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticFamilyQuadraticSum.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticAugmentedWeightedHessian
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticProbabilityOperations

/-! Actual finite Brownian-family scalar quadratic sums converge in probability. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The total quadratic sum `∑ᵢ ∑ₗ (B i tₗ₊₁ - B i tₗ)²` of a finite family of processes over the
uniform partition of `[0, T]` into `n + 1` steps. -/
def ginibreBrownianFamilyQuadraticSum {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i, ∑ l : Fin (n+1),
    (B i (ginibreUniformBrownianTime T n (l.val+1)) ω-
      B i (ginibreUniformBrownianTime T n l) ω)^2

theorem ginibreBrownianFamilyQuadraticSum_tendstoInProbability {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (T : ℝ≥0) :
    TendstoInMeasure P (ginibreBrownianFamilyQuadraticSum B T) atTop
      (fun _ => (Fintype.card ι : ℝ)*(T : ℝ)) := by
  classical
  let A : ι → ι → ℝ≥0 → Ω → ℝ := fun i j _ _ => if i=j then 1 else 0
  have h := ginibreBrownianAugmentedWeightedHessian_tendstoInProbability B P hB hind T A
    (fun i j t => stronglyMeasurable_const)
    (fun i j => Filter.Eventually.of_forall (fun ω => continuous_const))
    1 (by intro i j s ω; simp [A]; split_ifs <;> norm_num)
  convert! h using 1
  · funext n ω
    simp only [ginibreBrownianFamilyQuadraticSum, ginibreBrownianAugmentedWeightedHessian,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    simp [A, pow_two]
  · funext ω
    simp [A]
end
end GinibrePoincare
