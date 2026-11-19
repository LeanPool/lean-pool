/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralIsometry.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralLinear

/-! Exact discrete Itô isometry for the actual augmented joint Brownian filtration. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_augmented_linear_sum_isometry {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (n : ℕ) (s t : Fin n → ℝ≥0)
    (hchron : ∀ i k, i < k → s i + t i ≤ s k) (F : Fin n → Ω → ℝ)
    (hF : ∀ i, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (s i)) _ (F i))
    (hFi : ∀ i, MemLp (F i) 2 P) :
    (∫ ω, (∑ i, F i ω*(B j (s i+t i) ω-B j (s i) ω))^2 ∂P) =
      ∑ i, (t i : ℝ)*(∫ ω, (F i ω)^2 ∂P) := by
  have := Fintype.ofFinite ι
  let X := fun i ω => F i ω*(B j (s i+t i) ω-B j (s i) ω)
  have hX (i : Fin n) : MemLp (X i) 2 P :=
    ginibreBrownian_augmented_linear_memLp_two B P hB hind (s i) (t i) j (F i) (hF i) (hFi i)
  have hcross (i k : Fin n) (hne : i ≠ k) : (∫ ω, X i ω*X k ω ∂P) = 0 := by
    rcases lt_or_gt_of_ne hne with hik | hki
    · exact ginibreBrownian_augmented_linear_disjoint_orthogonal B P hB hind
        (s i) (t i) (s k) (t k) (hchron i k hik) j j (F i) (F k) (hF i) (hF k)
    · simpa only [X, mul_comm] using ginibreBrownian_augmented_linear_disjoint_orthogonal B P hB
        hind
        (s k) (t k) (s i) (t i) (hchron k i hki) j j (F k) (F i) (hF k) (hF i)
  change (∫ ω, (∑ i, X i ω)^2 ∂P) = _
  rw [ginibre_integral_square_sum_of_cross_zero P X hX hcross]
  apply Finset.sum_congr rfl
  intro i hi
  exact ginibreBrownian_augmented_linear_secondMoment B P hB hind (s i) (t i) j (F i) (hF i)

theorem ginibreBrownian_augmented_linear_sum_memLp_two {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (n : ℕ) (s t : Fin n → ℝ≥0) (F : Fin n → Ω → ℝ)
    (hF : ∀ i, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (s i)) _ (F i))
    (hFi : ∀ i, MemLp (F i) 2 P) :
    MemLp (fun ω => ∑ i, F i ω*(B j (s i+t i) ω-B j (s i) ω)) 2 P := by
  have := Fintype.ofFinite ι
  convert! memLp_finsetSum Finset.univ (fun i _ =>
    ginibreBrownian_augmented_linear_memLp_two B P hB hind (s i) (t i) j (F i) (hF i) (hFi i)) using
        1

end
end GinibrePoincare
