/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoIntervalRefinementBrownian.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoIntervalRefinement
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPartialGeometry

/-!
# Finite dimensional Ito interval refinement Brownian

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianUniformPartialSum_difference_horizon_refinement`.
-/

@[expose] public section

open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Literal two-grid intersection identity between a fixed-horizon partial
Brownian sum and the actual horizon-t left sum. -/
theorem brownianUniformPartialSum_difference_horizon_refinement {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F G : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t ≤ T)
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (ω : Ω) :
    brownianUniformPartialSum B F T N t ω - brownianUniformLeftSum B G t M ω =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
        (F (itoUniformNNTime T N i) ω-G (itoUniformNNTime t M j) ω)*
        (B (max (max (min t (itoUniformNNTime T N i)) (itoUniformNNTime t M j))
          (min (min t (itoUniformNNTime T N (i+1))) (itoUniformNNTime t M (j+1)))) ω -
          B (max (min t (itoUniformNNTime T N i)) (itoUniformNNTime t M j)) ω) := by
  rw [brownianUniformPartialSum_eq_stopped_leftsum]
  unfold brownianUniformLeftSum
  exact itoWeightedIntervalSums_difference_intersections (fun s => B s ω) t
    (fun i => min t (itoUniformNNTime T N i)) (itoUniformNNTime t M) N M
    (monotone_const.min (itoUniformNNTime_mono T N)) (itoUniformNNTime_mono t M)
    (by simp [itoUniformNNTime, itoUniformTime])
    (by rw [itoUniformNNTime_end T N hN, min_eq_left ht])
    (by simp [itoUniformNNTime, itoUniformTime]) (itoUniformNNTime_end t M hM)
    (fun i => F (itoUniformNNTime T N i) ω) (fun j => G (itoUniformNNTime t M j) ω)

end
end GinibrePoincare
