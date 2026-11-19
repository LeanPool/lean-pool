/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticBrownianQuadraticSums.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticGaussianSquareMoments
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianSums

/-! # Exact moments of actual Brownian quadratic-increment sums -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace GinibrePoincare
noncomputable section

/-- The quadratic sum `∑ (B τᵢ₊₁ - B τᵢ)²` of a process `B` along the times
`τ 0, …, τ n`. -/
def ginibreBrownianQuadraticSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Fin (n + 1) → ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin n, (B (τ i.succ) ω-B (τ i.castSucc) ω)^2

theorem ginibreBrownianQuadraticSum_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (n : ℕ) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) :
    MemLp (ginibreBrownianQuadraticSum B n τ) 2 P := by
  apply memLp_finsetSum
  intro i hi
  exact ginibreGaussian_hasLaw_square_memLp_two P _ _
    (ginibreBrownian_increment_hasLaw B P hB _ _ (hτ i.castSucc_lt_succ.le))

theorem ginibreBrownianQuadraticSum_mean {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (n : ℕ) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) :
    (∫ ω, ginibreBrownianQuadraticSum B n τ ω ∂P) =
      ∑ i : Fin n, ((τ i.succ-τ i.castSucc : ℝ≥0) : ℝ) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  unfold ginibreBrownianQuadraticSum
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact ginibreGaussian_hasLaw_square_mean P _ _
      (ginibreBrownian_increment_hasLaw B P hB _ _ (hτ i.castSucc_lt_succ.le))
  · intro i hi
    exact (ginibreGaussian_hasLaw_square_memLp_two P _ _
      (ginibreBrownian_increment_hasLaw B P hB _ _ (hτ i.castSucc_lt_succ.le))).integrable (by
          norm_num)

theorem ginibreBrownianQuadraticSum_variance {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (n : ℕ) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) :
    variance (ginibreBrownianQuadraticSum B n τ) P =
      2*∑ i : Fin n, (((τ i.succ-τ i.castSucc : ℝ≥0) : ℝ))^2 := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let W := fun i : Fin n => fun ω => (B (τ i.succ) ω-B (τ i.castSucc) ω)^2
  have hmem (i : Fin n) : MemLp (W i) 2 P := ginibreGaussian_hasLaw_square_memLp_two P _ _
    (ginibreBrownian_increment_hasLaw B P hB _ _ (hτ i.castSucc_lt_succ.le))
  have hind := (hB.hasIndepIncrements n τ hτ).comp (fun _ => fun x : ℝ => x^2) (fun _ => by
      fun_prop)
  have hvar := IndepFun.variance_sum (s := Finset.univ) (X := W)
    (fun i _ => hmem i) (fun i _ j _ hij => hind.indepFun hij)
  have he : (∑ i : Fin n, W i) = ginibreBrownianQuadraticSum B n τ := by
    funext ω
    simp only [Finset.sum_apply, ginibreBrownianQuadraticSum, W]
  rw [he] at hvar
  rw [hvar, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact ginibreGaussian_hasLaw_square_variance P _ _
    (ginibreBrownian_increment_hasLaw B P hB _ _ (hτ i.castSucc_lt_succ.le))

end
end GinibrePoincare
