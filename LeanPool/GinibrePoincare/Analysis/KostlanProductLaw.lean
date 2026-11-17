/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/KostlanProductLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.KostlanRadialTransfer
public import LeanPool.GinibrePoincare.Analysis.ProductWeightedMeasure
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianMoments

/-!
# Kostlan Product Law
-/


@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
namespace GinibrePoincare
noncomputable section

/-- Normalized polynomial tilt of one complex Gaussian coordinate. -/
def kostlanCoordinateWeight (n k : ℕ) (z : ℂ) : ℝ :=
  (n : ℝ) ^ k / (k.factorial : ℝ) * Complex.normSq z ^ k

def kostlanCoordinateLaw (n k : ℕ) : Measure ℂ :=
  (complexCoordinateGaussianProbability n : Measure ℂ).withDensity
    (fun z => ENNReal.ofReal (kostlanCoordinateWeight n k z))

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

theorem kostlanCoordinateLaw_isProbabilityMeasure (n k : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (kostlanCoordinateLaw n k) := by
  constructor
  unfold kostlanCoordinateLaw kostlanCoordinateWeight
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((integrable_normSq_pow_coordinate n k).const_mul _)
      (ae_of_all _ (by intro z; exact mul_nonneg (by positivity) (pow_nonneg
        (Complex.normSq_nonneg _) _)))]
  rw [integral_const_mul, integral_normSq_pow_coordinate n k hn]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp
  simp

/-- The explicit reference law consists of independent normalized coordinate tilts. -/
theorem kostlanReference_eq_product (n : ℕ) (hn : 0 < n) :
    kostlanReference n = Measure.pi (fun i : Fin n => kostlanCoordinateLaw n i.val) := by
  let c : ℝ := ∏ i : Fin n, (n : ℝ) ^ i.val / (i.val.factorial : ℝ)
  let ν := (complexGaussianMeasure n).withDensity
    (fun z => ENNReal.ofReal (kostlanWeight n z))
  have hc : 0 ≤ c := Finset.prod_nonneg (fun i _ => by positivity)
  have hp : ∀ i : Fin n, IsProbabilityMeasure (kostlanCoordinateLaw n i.val) :=
    fun i => kostlanCoordinateLaw_isProbabilityMeasure n i.val hn
  let := hp
  have he : Measure.pi (fun i : Fin n => kostlanCoordinateLaw n i.val) =
      ENNReal.ofReal c • ν := by
    unfold kostlanCoordinateLaw
    rw [pi_withDensity_ofReal_eq]
    · dsimp [ν]
      unfold complexGaussianMeasure complexGaussianProbability
      simp only [ProbabilityMeasure.toMeasure_pi]
      rw [← withDensity_smul]
      · congr 1
        funext z
        simp only [kostlanCoordinateWeight, Finset.prod_mul_distrib, kostlanWeight,
          Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul hc, c]
      · unfold kostlanWeight; fun_prop
    · intro i; unfold kostlanCoordinateWeight; fun_prop
    · intro i
      exact (integrable_normSq_pow_coordinate n i.val).const_mul _
    · intro i z; unfold kostlanCoordinateWeight
      exact mul_nonneg (by positivity) (pow_nonneg (Complex.normSq_nonneg _) _)
  have hmass := congrArg (fun μ : Measure (Configuration n) => μ Set.univ) he
  have href := (kostlanReference_isProbabilityMeasure n hn).measure_univ
  unfold kostlanReference at href ⊢
  rw [he]
  rw [Measure.smul_apply, smul_eq_mul] at hmass href
  simp only [measure_univ] at hmass
  have hν : ν Set.univ ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hmass
    exact one_ne_zero hmass
  have hνtop : ν Set.univ ≠ ⊤ := by
    unfold ν
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hi : Integrable (kostlanWeight n) (complexGaussianMeasure n) := by
      unfold kostlanWeight complexGaussianMeasure complexGaussianProbability
      simp only [ProbabilityMeasure.toMeasure_pi]
      exact Integrable.fintype_prod (fun i : Fin n => integrable_normSq_pow_coordinate n i.val)
    exact hi.lintegral_lt_top.ne
  have hcEq := (ENNReal.mul_left_inj hν hνtop).mp (href.trans hmass)
  rw [hcEq]

end
end GinibrePoincare
