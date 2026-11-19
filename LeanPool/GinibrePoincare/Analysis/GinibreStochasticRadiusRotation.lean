/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticRadiusRotation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticPlanarGaussianRotation

/-! # Autonomous radial transition laws from genuine isotropic Gaussian noise -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The law of `|m + W|²` for `W` distributed as `ginibrePlanarGaussian v`. -/
def ginibreNoncentralRadiusLaw (v : ℝ≥0) (m : ℂ) : Measure ℝ :=
  (ginibrePlanarGaussian v).map (fun w => Complex.normSq (m+w))

theorem ginibreNoncentralRadiusLaw_rotation (v : ℝ≥0) (u m : ℂ) (hu : ‖u‖ = 1) :
    ginibreNoncentralRadiusLaw v (u*m) = ginibreNoncentralRadiusLaw v m := by
  unfold ginibreNoncentralRadiusLaw
  conv_lhs => rw [← ginibrePlanarGaussian_rotation v u hu]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext w
  dsimp
  rw [← mul_add, Complex.normSq_mul, Complex.normSq_eq_norm_sq u, hu]
  norm_num

theorem ginibreNoncentralRadiusLaw_norm (v : ℝ≥0) (m : ℂ) :
    ginibreNoncentralRadiusLaw v m = ginibreNoncentralRadiusLaw v (‖m‖ : ℂ) := by
  by_cases hm : m = 0
  · simp [hm]
  have hnorm : ‖m‖ ≠ 0 := norm_ne_zero_iff.mpr hm
  let u : ℂ := (starRingEnd ℂ) m / (‖m‖ : ℂ)
  have hu : ‖u‖ = 1 := by simp [u, hnorm]
  have hum : u*m = (‖m‖ : ℂ) := by
    dsimp [u]
    rw [div_mul_eq_mul_div, Complex.conj_mul']
    field_simp
  rw [← hum]
  exact (ginibreNoncentralRadiusLaw_rotation v u m hu).symm

theorem ginibreNoncentralRadiusLaw_eq_of_normSq_eq (v : ℝ≥0) (m q : ℂ)
    (h : Complex.normSq m = Complex.normSq q) :
    ginibreNoncentralRadiusLaw v m = ginibreNoncentralRadiusLaw v q := by
  rw [ginibreNoncentralRadiusLaw_norm v m, ginibreNoncentralRadiusLaw_norm v q]
  congr 2
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg m, norm_nonneg q]

end
end GinibrePoincare
