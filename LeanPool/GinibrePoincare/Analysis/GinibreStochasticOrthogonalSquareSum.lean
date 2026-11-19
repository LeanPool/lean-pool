/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOrthogonalSquareSum.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianQuadraticOrthogonality
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianWeightedQuadratic

/-! Finite square-moment expansion for genuinely orthogonal random errors. -/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem ginibre_integral_square_sum_of_cross_zero {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 P)
    (hcross : ∀ i j, i ≠ j → (∫ ω, X i ω * X j ω ∂P) = 0) :
    (∫ ω, (∑ i, X i ω)^2 ∂P) = ∑ i, ∫ ω, (X i ω)^2 ∂P := by
  classical
  have hprod (i j : ι) : Integrable (fun ω => X i ω * X j ω) P :=
    (hX i).integrable_mul (hX j)
  have hsum (i : ι) : Integrable (fun ω => ∑ j, X i ω * X j ω) P :=
    integrable_finsetSum Finset.univ (fun j _ => hprod i j)
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hsum i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Finset.univ (fun j _ => hprod i j)]
  rw [Finset.sum_eq_single i]
  · intro j hj hji
    exact hcross i j (Ne.symm hji)
  · simp

end
end GinibrePoincare
