/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCIRNoiseCoefficient.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRadialGradient

/-! Exact CIR diffusion amplitude of the original configuration Brownian noise. -/

@[expose] public section
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreRecenteredRadialDirection_scaled_coordinate {n : ℕ} (hn : 2 ≤ n)
    (z : Configuration n) (hz : CollisionFree z)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n × Fin 2) :
    ‖configurationEuclideanEquiv n (recenteredConfiguration n z)‖*
      ginibreRecenteredRadialDirection n e z i =
      configurationEuclideanEquiv n (recenteredConfiguration n z) i := by
  have hne : configurationEuclideanEquiv n (recenteredConfiguration n z) ≠ 0 := by
    intro h
    exact recenteredConfiguration_ne_zero_of_collisionFree hn z hz
      ((configurationEuclideanEquiv n).injective (by simpa using h))
  simp only [ginibreRecenteredRadialDirection, brownianRadialUnitVector, ite_eq_right hne,
    PiLp.smul_apply, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hne), one_mul]

theorem ginibreCIR_noise_amplitude_square {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n) :
    (2*(n : ℝ)*Real.sqrt (2*α/(n : ℝ)^2)*
      ‖configurationEuclideanEquiv n (recenteredConfiguration n z)‖)^2 =
      (8*α/(n : ℝ))*pairwiseRadius z := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : (Real.sqrt (2*α/(n : ℝ)^2))^2=2*α/(n : ℝ)^2 :=
    Real.sq_sqrt (div_nonneg (by positivity) (sq_nonneg _))
  rw [mul_pow, mul_pow, mul_pow, hs, ginibre_configurationEuclidean_norm_sq,
    pairwiseRadius_eq_radialObservable]
  unfold radialObservable recenteredSqNorm
  field_simp
 ; ring

theorem ginibreCIR_noise_amplitude {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n) :
    2*(n : ℝ)*Real.sqrt (2*α/(n : ℝ)^2)*
      ‖configurationEuclideanEquiv n (recenteredConfiguration n z)‖ =
      Real.sqrt ((8*α/(n : ℝ))*pairwiseRadius z) := by
  rw [← ginibreCIR_noise_amplitude_square hn α hα z, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity)]

theorem ginibreCIR_noise_coordinate {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n) (hz : CollisionFree z)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n × Fin 2) :
    Real.sqrt (2*α/(n : ℝ)^2)*fderiv ℝ pairwiseRadius z (ginibreCoordinateDirection i) =
      Real.sqrt ((8*α/(n : ℝ))*pairwiseRadius z)*ginibreRecenteredRadialDirection n e z i := by
  rw [ginibre_fderiv_pairwiseRadius_coordinate (by omega),
    ← ginibreCIR_noise_amplitude (by omega) α hα z]
  rw [mul_assoc (2*(n : ℝ)*Real.sqrt (2*α/(n : ℝ)^2)),
    ginibreRecenteredRadialDirection_scaled_coordinate hn z hz e i]
  ring

end
end GinibrePoincare
