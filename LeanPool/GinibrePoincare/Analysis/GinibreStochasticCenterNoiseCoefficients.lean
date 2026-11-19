/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterNoiseCoefficients.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterDirection

/-! Actual normalization of the repeated center in original coordinate noise. -/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

theorem ginibreRepeatedCenterEuclidean_norm_sq (n : ℕ) (z : Configuration n) :
    ‖configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z)‖^2 =
      (n : ℝ)*ginibreCenterSquared n z := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, configurationEuclideanEquiv_apply_zero,
    configurationEuclideanEquiv_apply_one, ginibreRepeatedCenterCLM,
    ContinuousLinearMap.pi_apply, coordinateSumCLM_apply]
  simp [ginibreCenterSquared, Complex.normSq_apply]
  ring

theorem ginibreRepeatedCenterEuclidean_norm (n : ℕ) (z : Configuration n) :
    ‖configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z)‖ =
      Real.sqrt ((n : ℝ)*ginibreCenterSquared n z) := by
  rw [← ginibreRepeatedCenterEuclidean_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem ginibreCenterRadialDirection_apply {n : ℕ} (hn : 0 < n)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (z : Configuration n)
    (hz : ginibreCenterSquared n z ≠ 0) (i : Fin n) :
    ginibreCenterRadialDirection n e z (i, 0) =
      (Real.sqrt ((n : ℝ)*ginibreCenterSquared n z))⁻¹*(coordinateSum z).re ∧
    ginibreCenterRadialDirection n e z (i, 1) =
      (Real.sqrt ((n : ℝ)*ginibreCenterSquared n z))⁻¹*(coordinateSum z).im := by
  have hne : configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z) ≠ 0 := by
    intro h
    have hh := ginibreRepeatedCenterEuclidean_norm_sq n z
    rw [h, norm_zero, zero_pow (by norm_num)] at hh
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    exact hz ((mul_eq_zero.mp hh.symm).resolve_left hnR)
  unfold ginibreCenterRadialDirection brownianRadialUnitVector
  rw [ite_eq_right hne, ginibreRepeatedCenterEuclidean_norm]
  simp only [PiLp.smul_apply, smul_eq_mul, configurationEuclideanEquiv_apply_zero,
    configurationEuclideanEquiv_apply_one, ginibreRepeatedCenterCLM,
    ContinuousLinearMap.pi_apply, coordinateSumCLM_apply]
  exact ⟨trivial, trivial⟩

end
end GinibrePoincare
