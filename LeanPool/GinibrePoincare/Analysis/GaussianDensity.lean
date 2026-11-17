/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianDensity.lean.
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

public import LeanPool.GinibrePoincare.Concrete.GaussianProbability

/-!
# Density of the real coordinates of the Ginibre Gaussian

This file begins the identification of the probability measure constructed in
`Concrete.GaussianProbability` with an explicit Lebesgue density.  The first
step is completely supplied by Mathlib's density theorem for a nondegenerate
real Gaussian; the only point specific to the Ginibre normalization is proving
that the variance `1 / (2n)` is nonzero when `n > 0`.
-/


@[expose] public section


open MeasureTheory

namespace GinibrePoincare

noncomputable section

/-- For a nonempty particle configuration, the variance `1 / (2n)` of each
real coordinate is nonzero. -/
theorem realCoordinateVariance_ne_zero {n : ℕ} (hn : 0 < n) :
    realCoordinateVariance n ≠ 0 := by
  unfold realCoordinateVariance
  exact inv_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hn.ne'))

/-- Coercing the real-coordinate variance to `ℝ` gives the expected
normalization. -/
theorem coe_realCoordinateVariance (n : ℕ) :
    (realCoordinateVariance n : ℝ) = ((2 : ℝ) * n)⁻¹ := by
  simp [realCoordinateVariance]

/-- The exponent in the centered one-dimensional Gaussian PDF simplifies to
`-n x²`. -/
theorem realCoordinateGaussian_exponent {n : ℕ} (hn : 0 < n) (x : ℝ) :
    -(x - 0) ^ 2 / (2 * (realCoordinateVariance n : ℝ)) =
      -(n : ℝ) * x ^ 2 := by
  rw [coe_realCoordinateVariance]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

/-- The real Gaussian PDF in the normalization used by the Ginibre model. -/
theorem realCoordinateGaussianPDFReal_formula {n : ℕ} (hn : 0 < n)
    (x : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 (realCoordinateVariance n) x =
      (Real.sqrt (Real.pi / n))⁻¹ * Real.exp (-(n : ℝ) * x ^ 2) := by
  rw [ProbabilityTheory.gaussianPDFReal]
  rw [realCoordinateGaussian_exponent hn]
  congr 2
  apply congrArg Real.sqrt
  rw [coe_realCoordinateVariance]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

/-- `ℝ≥0∞`-valued version of the explicit real-coordinate density. -/
theorem realCoordinateGaussianPDF_formula {n : ℕ} (hn : 0 < n)
    (x : ℝ) :
    ProbabilityTheory.gaussianPDF 0 (realCoordinateVariance n) x =
      ENNReal.ofReal
        ((Real.sqrt (Real.pi / n))⁻¹ * Real.exp (-(n : ℝ) * x ^ 2)) := by
  rw [ProbabilityTheory.gaussianPDF,
    realCoordinateGaussianPDFReal_formula hn]

/-- The ordinary measure underlying one real-coordinate Gaussian has
Mathlib's explicit Gaussian PDF with respect to Lebesgue measure. -/
theorem realCoordinateGaussianMeasure_eq_withDensity {n : ℕ} (hn : 0 < n) :
    (realCoordinateGaussianProbability n : Measure ℝ) =
      volume.withDensity
        (ProbabilityTheory.gaussianPDF 0 (realCoordinateVariance n)) := by
  unfold realCoordinateGaussianProbability
  exact ProbabilityTheory.gaussianReal_of_var_ne_zero 0
    (realCoordinateVariance_ne_zero hn)

/-- Setwise form of `realCoordinateGaussianMeasure_eq_withDensity`. -/
theorem realCoordinateGaussian_apply {n : ℕ} (hn : 0 < n)
    (s : Set ℝ) :
    (realCoordinateGaussianProbability n : Measure ℝ) s =
      ∫⁻ x in s, ProbabilityTheory.gaussianPDF 0
        (realCoordinateVariance n) x := by
  rw [realCoordinateGaussianMeasure_eq_withDensity hn]
  exact withDensity_apply' _ _

/-- The real-coordinate Gaussian is absolutely continuous with respect to
Lebesgue measure whenever the particle number is positive. -/
theorem realCoordinateGaussian_absolutelyContinuous {n : ℕ} (hn : 0 < n) :
    (realCoordinateGaussianProbability n : Measure ℝ) ≪ volume := by
  rw [realCoordinateGaussianMeasure_eq_withDensity hn]
  exact withDensity_absolutelyContinuous _ _

end

end GinibrePoincare
