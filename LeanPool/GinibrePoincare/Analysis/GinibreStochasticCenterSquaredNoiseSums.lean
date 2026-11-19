/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterSquaredNoiseSums.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterCIRNoiseCoefficient
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactGradientIntegral

/-! The actual finite configuration-noise sums already have the precise CIR
amplitude and actual radial-unit innovation, before any stochastic limit. -/

@[expose] public section
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreCenterCIR_noise_coordinate_all {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n × Fin 2) :
    Real.sqrt (2*α/(n : ℝ)^2)*fderiv ℝ (ginibreCenterSquared n) z (ginibreCoordinateDirection i) =
      Real.sqrt ((8*α/(n : ℝ))*ginibreCenterSquared n z)*ginibreCenterRadialDirection n e z i := by
  by_cases hz : ginibreCenterSquared n z=0
  · have hs : coordinateSum z=0 := Complex.normSq_eq_zero.mp hz
    simp [hz, ginibre_fderiv_centerSquared, hs]
  · exact ginibreCenterCIR_noise_coordinate hn α hα z hz e i

theorem ginibreConfigurationBrownianGradientSum_centerSquared {Ω : Type*} {n : ℕ}
    (hn : 2 ≤ n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (α : ℝ) (hα : 0 ≤ α) (X : ℝ≥0 → Ω → Configuration n)
    (_ : ∀ s ω, CollisionFree (X s ω)) (e : EuclideanSpace ℝ (Fin n × Fin 2))
    (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    ginibreConfigurationBrownianGradientSum n B α X (ginibreCenterSquared n) T k ω =
      ∑ i, brownianUniformLeftSum (B i)
        (fun s ω => Real.sqrt ((8*α/(n : ℝ))*(ginibreCenterSquared n) (X s ω))*
          ginibreCenterRadialDirection n e (X s ω) i) T (k+1) ω := by
  classical
  rw [ginibreConfigurationBrownianGradientSum_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold brownianUniformLeftSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_assoc, ginibreCenterCIR_noise_coordinate_all (by omega) α hα _ e i]

end
end GinibrePoincare
