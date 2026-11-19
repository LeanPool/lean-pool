/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterCIRNoiseCoefficient.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterNoiseCoefficients

/-! Exact CIR diffusion amplitude of the original configuration Brownian noise. -/

@[expose] public section
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreCenterRadialDirection_scaled_coordinate {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : ginibreCenterSquared n z ≠ 0)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n × Fin 2) :
    ‖configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z)‖*
      ginibreCenterRadialDirection n e z i =
      configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z) i := by
  have hne : configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z) ≠ 0 := by
    intro h
    have hh := ginibreRepeatedCenterEuclidean_norm_sq n z
    rw [h, norm_zero, zero_pow (by norm_num)] at hh
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    exact hz ((mul_eq_zero.mp hh.symm).resolve_left hnR)
  simp only [ginibreCenterRadialDirection, brownianRadialUnitVector, ite_eq_right hne,
    PiLp.smul_apply, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hne), one_mul]

theorem ginibreCenterCIR_noise_amplitude_square {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n) :
    (2*Real.sqrt (2*α/(n : ℝ)^2)*
      ‖configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z)‖)^2 =
      (8*α/(n : ℝ))*ginibreCenterSquared n z := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : (Real.sqrt (2*α/(n : ℝ)^2))^2=2*α/(n : ℝ)^2 :=
    Real.sq_sqrt (div_nonneg (by positivity) (sq_nonneg _))
  rw [mul_pow, mul_pow, hs, ginibreRepeatedCenterEuclidean_norm_sq]
  field_simp
 ; ring

theorem ginibreCenterCIR_noise_amplitude {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n) :
    2*Real.sqrt (2*α/(n : ℝ)^2)*
      ‖configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z)‖ =
      Real.sqrt ((8*α/(n : ℝ))*ginibreCenterSquared n z) := by
  rw [← ginibreCenterCIR_noise_amplitude_square hn α hα z, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity)]

theorem ginibreCenterCIR_noise_coordinate {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n) (hz : ginibreCenterSquared n z ≠ 0)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n × Fin 2) :
    Real.sqrt (2*α/(n : ℝ)^2)*fderiv ℝ (ginibreCenterSquared n) z (ginibreCoordinateDirection i) =
      Real.sqrt ((8*α/(n : ℝ))*ginibreCenterSquared n z)*ginibreCenterRadialDirection n e z i := by
  rw [← ginibreCenterCIR_noise_amplitude hn α hα z]
  rw [mul_assoc (2*Real.sqrt (2*α/(n : ℝ)^2)),
    ginibreCenterRadialDirection_scaled_coordinate hn z hz e i]
  have hc : fderiv ℝ (ginibreCenterSquared n) z (ginibreCoordinateDirection i) =
      2*configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z) i := by
    obtain ⟨j, b⟩ := i
    fin_cases b <;> simp [ginibre_fderiv_centerSquared, ginibreCoordinateDirection,
      realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection,
      coordinateSum, ginibreRepeatedCenterCLM, coordinateSumCLM_apply]
  rw [hc]
  ring

end
end GinibrePoincare
