/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MultivariateHermiteIntegrability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.ComplexHermiteOrthogonality

/-!
# Integrability of multivariate complex Hermite functions

Finite complex-Hermite tensors have polynomial growth, hence belong to both
`L¹` and `L²` of the concrete product Gaussian measure.  Their inner products
factor coordinatewise by finite-dimensional Fubini.
-/


@[expose] public section


open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace GinibrePoincare
namespace ComplexHermite

noncomputable section

/-- The product of any two normalized one-coordinate Hermite functions is
integrable. -/
theorem integrable_normalizedEval_mul (n : ℕ) (hn : 0 < n)
    (p q r s : ℕ) :
    Integrable (fun z : ℂ =>
      normalizedEval n hn p q z * normalizedEval n hn r s z)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  rw [show (fun z : ℂ =>
      normalizedEval n hn p q z * normalizedEval n hn r s z) =
      fun z =>
        (((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ) *
          ∑ k ∈ Finset.range (min p q + 1),
            (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
                (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
              z ^ (p - k) * (conj z) ^ (q - k)) *
        (((oneDimNormalization n r * oneDimNormalization n s : ℝ) : ℂ) *
          ∑ l ∈ Finset.range (min r s + 1),
            (((-((n : ℝ)⁻¹ : ℂ)) ^ l) * (l.factorial : ℂ) *
                (Nat.choose r l : ℂ) * (Nat.choose s l : ℂ)) *
              z ^ (r - l) * (conj z) ^ (s - l)) by
    funext z
    rw [normalizedEval_eq_sum, normalizedEval_eq_sum]]
  rw [show (fun z : ℂ =>
      (((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ) *
        ∑ k ∈ Finset.range (min p q + 1),
          (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
              (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
            z ^ (p - k) * (conj z) ^ (q - k)) *
      (((oneDimNormalization n r * oneDimNormalization n s : ℝ) : ℂ) *
        ∑ l ∈ Finset.range (min r s + 1),
          (((-((n : ℝ)⁻¹ : ℂ)) ^ l) * (l.factorial : ℂ) *
              (Nat.choose r l : ℂ) * (Nat.choose s l : ℂ)) *
            z ^ (r - l) * (conj z) ^ (s - l))) =
      fun z => ∑ k ∈ Finset.range (min p q + 1),
        ∑ l ∈ Finset.range (min r s + 1),
          (((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ) *
            ((oneDimNormalization n r * oneDimNormalization n s : ℝ) : ℂ) *
            (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
              (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
            (((-((n : ℝ)⁻¹ : ℂ)) ^ l) * (l.factorial : ℂ) *
              (Nat.choose r l : ℂ) * (Nat.choose s l : ℂ))) *
            (z ^ ((p - k) + (r - l)) *
              (conj z) ^ ((q - k) + (s - l))) by
    funext z
    simp_rw [Finset.mul_sum, Finset.sum_mul, pow_add]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring]
  apply integrable_finsetSum
  intro k hk
  apply integrable_finsetSum
  intro l hl
  have hmono := integrable_complex_monomial_complexCoordinateGaussianProbability
    n ((p - k) + (r - l)) ((q - k) + (s - l))
  exact hmono.const_mul _

/-- A normalized one-coordinate Hermite function times the conjugate of
another is integrable. -/
theorem integrable_conj_normalizedEval_mul (n : ℕ) (hn : 0 < n)
    (p q r s : ℕ) :
    Integrable (fun z : ℂ =>
      conj (normalizedEval n hn p q z) * normalizedEval n hn r s z)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  apply Integrable.congr'_enorm
    (integrable_normalizedEval_mul n hn p q r s)
  · exact ((Complex.continuous_conj.comp
      (continuous_normalizedEval n hn p q)).mul
        (continuous_normalizedEval n hn r s)).aestronglyMeasurable
  · filter_upwards with z
    simp [enorm_eq_nnnorm]

/-- The squared norm of every normalized one-coordinate Hermite function is
integrable. -/
theorem integrable_normSq_normalizedEval (n : ℕ) (hn : 0 < n)
    (p q : ℕ) :
    Integrable (fun z : ℂ => Complex.normSq (normalizedEval n hn p q z))
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  apply Integrable.congr'_enorm
    (integrable_conj_normalizedEval_mul n hn p q p q)
  · exact (Complex.continuous_normSq.comp
      (continuous_normalizedEval n hn p q)).aestronglyMeasurable
  · filter_upwards with z
    rw [← Complex.sq_norm]
    simp [enorm_eq_nnnorm, pow_two]

/-- Every multivariate normalized Hermite tensor is in `L¹` of the concrete
Gaussian product measure. -/
theorem integrable_multivariateNormalized (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) :
    Integrable (multivariateNormalized n hn p q) (complexGaussianMeasure n) := by
  unfold multivariateNormalized complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  exact Integrable.fintype_prod fun i => integrable_normalizedEval n hn (p i) (q i)

/-- Pointwise squared norms of multivariate normalized Hermite tensors are
integrable. -/
theorem integrable_normSq_multivariateNormalized (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) :
    Integrable (fun z => Complex.normSq (multivariateNormalized n hn p q z))
      (complexGaussianMeasure n) := by
  rw [show (fun z => Complex.normSq (multivariateNormalized n hn p q z)) =
      fun z => ∏ i, Complex.normSq (normalizedEval n hn (p i) (q i) (z i)) by
    funext z
    simp [multivariateNormalized, Complex.normSq_apply, map_prod]]
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  exact Integrable.fintype_prod fun i =>
    integrable_normSq_normalizedEval n hn (p i) (q i)

/-- Every multivariate normalized Hermite tensor belongs to Gaussian `L²`. -/
theorem memLp_two_multivariateNormalized (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) :
    MemLp (multivariateNormalized n hn p q) 2 (complexGaussianMeasure n) := by
  rw [memLp_two_iff_integrable_sq_norm
    (continuous_multivariateNormalized n hn p q).aestronglyMeasurable]
  apply Integrable.congr (integrable_normSq_multivariateNormalized n hn p q)
  filter_upwards with z
  rw [Complex.sq_norm]

/-- The Gaussian inner product of two Hermite tensors factors as the product
of their one-coordinate inner products. -/
theorem integral_conj_multivariateNormalized_mul_eq_prod (n : ℕ) (hn : 0 < n)
    (p q r s : Fin n → ℕ) :
    ∫ z, conj (multivariateNormalized n hn p q z) *
        multivariateNormalized n hn r s z ∂complexGaussianMeasure n =
      ∏ i, ∫ z : ℂ, conj (normalizedEval n hn (p i) (q i) z) *
          normalizedEval n hn (r i) (s i) z
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
  unfold multivariateNormalized complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi, map_prod]
  rw [show (fun z : Fin n → ℂ =>
      (∏ x, conj (normalizedEval n hn (p x) (q x) (z x))) *
        ∏ x, normalizedEval n hn (r x) (s x) (z x)) =
      fun z => ∏ i, conj (normalizedEval n hn (p i) (q i) (z i)) *
        normalizedEval n hn (r i) (s i) (z i) by
    funext z
    rw [← Finset.prod_mul_distrib]]
  simpa using (integral_fintype_prod_eq_prod
    (𝕜 := ℂ)
    (E := fun _ : Fin n => ℂ)
    (μ := fun _ : Fin n =>
      (complexCoordinateGaussianProbability n : Measure ℂ))
    (fun i (z : ℂ) => conj (normalizedEval n hn (p i) (q i) z) *
      normalizedEval n hn (r i) (s i) z))

end
end ComplexHermite
end GinibrePoincare
