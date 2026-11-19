/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCIRFullNoiseSums.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCIRCoefficientProcess

/-! # Radius sums use the full-process radial direction before stopping

The existing radius gradient identity expresses each finite Brownian sum
through the CIR amplitude and the stopped process's radial direction.
Every left endpoint in a partition of `[0, t]` is at most `t`. If `t` is
before the Hamiltonian stop, the stopped and maximal configurations agree
at all those endpoints, so the direction can be replaced by that of the
full process term by term.

This finite-sum identity connects the stopped Itô formula to the global
scalar radial Brownian driver in `GinibreStochasticCIRDrivenLocal`. It is
pathwise and requires no limiting or probabilistic argument. -/

@[expose] public section
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreConfigurationBrownianGradientSum_radius_full_direction
    {Ω : Type*} {n : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (t : ℝ≥0) (k : ℕ) (ω : Ω)
    (ht : t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω) :
    let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
    ginibreConfigurationBrownianGradientSum n B α X pairwiseRadius t k ω =
      ∑ i, brownianUniformLeftSum (B i)
        (fun s ω => Real.sqrt ((8*α/(n : ℝ))*pairwiseRadius (X s ω))*
          ginibreRecenteredRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k+1) ω := by
  classical
  dsimp only
  rw [ginibreConfigurationBrownianGradientSum_radius hn B α hα _
    (fun s ω => (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B R hR T s ω).1)
        e]
  apply Finset.sum_congr rfl
  intro i hi
  unfold brownianUniformLeftSum
  apply Finset.sum_congr rfl
  intro j hj
  have he := ginibreBrownianHamiltonianStoppedProcess_grid_eq_maximal α z B R T t k j hj ω ht
  dsimp only
  rw [he]

end
end GinibrePoincare
