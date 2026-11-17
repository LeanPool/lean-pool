/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/ComplexGaussianMoments.lean and
GinibrePoincare/Analysis/KostlanProductLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianPolynomialIntegrability
public import LeanPool.GinibrePoincare.Analysis.PolarGaussianMoments
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianDensity

/-! # Mixed moments of one complex Gaussian coordinate -/


@[expose] public section


open MeasureTheory Set
open scoped ComplexConjugate

namespace GinibrePoincare

noncomputable section

/-- Mixed complex monomials have the expected absolute value. -/
theorem norm_mixedComplexMonomial (a b : ℕ) (z : ℂ) :
    ‖z ^ a * (conj z) ^ b‖ = ‖z‖ ^ (a + b) := by
  simp [norm_pow, pow_add]

/-- Every mixed complex monomial is integrable under one complex Gaussian
coordinate law. -/
theorem integrable_mixedComplexMonomial (n a b : ℕ) :
    Integrable (fun z : ℂ ↦ z ^ a * (conj z) ^ b)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  apply Integrable.mono'
    (integrable_norm_pow_complexCoordinateGaussianProbability n (a + b))
  · fun_prop
  · filter_upwards with z
    exact le_of_eq (norm_mixedComplexMonomial a b z)

/-- The `(a,b)` mixed moment of one complex Gaussian coordinate. -/
noncomputable def complexGaussianMixedMoment (n a b : ℕ) : ℂ :=
  ∫ z : ℂ, z ^ a * (conj z) ^ b
    ∂(complexCoordinateGaussianProbability n : Measure ℂ)

/-- The zeroth mixed moment is one. -/
@[simp] theorem complexGaussianMixedMoment_zero_zero (n : ℕ) :
    complexGaussianMixedMoment n 0 0 = 1 := by
  simp [complexGaussianMixedMoment]

/-- Swapping the two exponents conjugates the mixed moment. -/
theorem complexGaussianMixedMoment_comm_conj (n a b : ℕ) :
    complexGaussianMixedMoment n b a =
      conj (complexGaussianMixedMoment n a b) := by
  unfold complexGaussianMixedMoment
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with z
  simp only [map_mul, map_pow]
  rw [show conj (conj z) = z by exact star_star z]
  ring

/-- The extended nonnegative density has the expected real value. -/
theorem complexCoordinateGaussianDensity_toReal (n : ℕ) (z : ℂ) :
    (complexCoordinateGaussianDensity n z).toReal =
      ((n : ℝ) / Real.pi) * Real.exp (-(n : ℝ) * Complex.normSq z) := by
  unfold complexCoordinateGaussianDensity
  rw [ENNReal.toReal_ofReal]
  positivity

/-- The mixed moment is the corresponding Jacobian-weighted polar integral. -/
theorem complexGaussianMixedMoment_eq_polar {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    complexGaussianMixedMoment n a b =
      ∫ p : ℝ × ℝ in Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ((((n : ℝ) : ℂ) / Real.pi) * (p.1 : ℂ) ^ (a + b + 1) *
          (Real.exp (-(n : ℝ) * p.1 ^ 2) : ℂ)) * angularMode a b p.2 := by
  unfold complexGaussianMixedMoment
  rw [complexCoordinateGaussianMeasure_eq_withDensity hn]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_complexCoordinateGaussianDensity n)
    (ae_of_all _ fun z ↦ ENNReal.ofReal_lt_top)]
  simp_rw [complexCoordinateGaussianDensity_toReal]
  rw [← Complex.integral_comp_polarCoord_symm]
  apply setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
  intro p hp
  change p.1 •
      (((n : ℝ) / Real.pi) *
        Real.exp (-(n : ℝ) * Complex.normSq (Complex.polarCoord.symm p))) •
        ((Complex.polarCoord.symm p) ^ a *
          conj (Complex.polarCoord.symm p) ^ b) = _
  rw [show Complex.normSq (Complex.polarCoord.symm p) = p.1 ^ 2 by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm, sq_abs]]
  rw [gaussianMixedIntegrand_polar]
  push_cast
  rw [pow_succ]
  ring

/-- Exact mixed moments of the centered complex Gaussian coordinate law. -/
theorem complexGaussianMixedMoment_formula {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    complexGaussianMixedMoment n a b =
      if a = b then (a.factorial : ℂ) / (n : ℂ) ^ a else 0 := by
  rw [complexGaussianMixedMoment_eq_polar hn]
  exact integral_gaussianMixedIntegrand_polar_eq n a b hn

theorem integrable_normSq_pow_coordinate (n k : ℕ) :
    Integrable (fun z : ℂ => Complex.normSq z ^ k)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  simpa only [Complex.normSq_eq_norm_sq, ← pow_mul] using
    integrable_norm_pow_complexCoordinateGaussianProbability n (2 * k)

theorem integral_normSq_pow_coordinate (n k : ℕ) (hn : 0 < n) :
    (∫ z : ℂ, Complex.normSq z ^ k ∂(complexCoordinateGaussianProbability n : Measure ℂ)) =
      (k.factorial : ℝ) / (n : ℝ) ^ k := by
  have h := complexGaussianMixedMoment_formula hn k k
  unfold complexGaussianMixedMoment at h
  have he : (fun z : ℂ => z ^ k * (starRingEnd ℂ) z ^ k) =
      fun z : ℂ => (Complex.normSq z ^ k : ℂ) := by
    funext z
    rw [← mul_pow, Complex.mul_conj]
  rw [he] at h
  simp only [← Complex.ofReal_pow, integral_complex_ofReal] at h
  have heq : (Complex.ofReal (∫ z : ℂ, Complex.normSq z ^ k
      ∂(complexCoordinateGaussianProbability n : Measure ℂ))) =
      Complex.ofReal ((k.factorial : ℝ) / (n : ℝ) ^ k) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, ite_true] using h
  exact Complex.ofReal_injective heq


end

end GinibrePoincare
