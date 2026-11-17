/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreMassFiniteness.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreMassPositivity

/-! # Finiteness of the Ginibre normalizing mass -/


@[expose] public section


open MeasureTheory
open scoped ENNReal BigOperators

namespace GinibrePoincare

noncomputable section

/-- A polynomial growth majorant for one coordinate is integrable under its
complex Gaussian law. -/
theorem integrable_one_add_norm_pow_complexCoordinateGaussianProbability
    (n k : ℕ) :
    Integrable (fun z : ℂ ↦ (1 + ‖z‖) ^ k)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  rw [show (fun z : ℂ ↦ (1 + ‖z‖) ^ k) =
      fun z ↦ ∑ m ∈ Finset.range (k + 1),
        ‖z‖ ^ (k - m) * (Nat.choose k m : ℝ) by
    funext z
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [one_pow, one_mul]]
  apply integrable_finsetSum
  intro m hm
  exact (integrable_norm_pow_complexCoordinateGaussianProbability n (k - m)).mul_const _

/-- Products of coordinatewise polynomial majorants are integrable under the
concrete product Gaussian law. -/
theorem integrable_prod_one_add_norm_pow_complexGaussianMeasure
    (n : ℕ) (k : Fin n → ℕ) :
    Integrable (fun z : Configuration n ↦ ∏ i, (1 + ‖z i‖) ^ k i)
      (complexGaussianMeasure n) := by
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  exact Integrable.fintype_prod fun i ↦
    integrable_one_add_norm_pow_complexCoordinateGaussianProbability n (k i)

/-- Constant-exponent form of
`integrable_prod_one_add_norm_pow_complexGaussianMeasure`. -/
theorem integrable_prod_one_add_norm_pow_const_complexGaussianMeasure
    (n k : ℕ) :
    Integrable (fun z : Configuration n ↦ ∏ i, (1 + ‖z i‖) ^ k)
      (complexGaussianMeasure n) :=
  integrable_prod_one_add_norm_pow_complexGaussianMeasure n (fun _ ↦ k)

/-- A deliberately generous separable polynomial bound for the Vandermonde
square. -/
theorem vandermondeWeight_le_prod_one_add_norm_pow (n : ℕ)
    (z : Configuration n) :
    vandermondeWeight z ≤ ∏ i, (1 + ‖z i‖) ^ (4 * n * n) := by
  let B : ℝ := ∏ i : Fin n, (1 + ‖z i‖)
  have hfac (i : Fin n) : 1 ≤ 1 + ‖z i‖ := by
    linarith [norm_nonneg (z i)]
  have hB : 1 ≤ B := by
    dsimp [B]
    exact Finset.one_le_prod₀ fun i _ ↦ hfac i
  have hiB (i : Fin n) : 1 + ‖z i‖ ≤ B := by
    have he : B = (1 + ‖z i‖) *
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (1 + ‖z j‖) := by
      dsimp [B]
      exact (Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
        (fun j ↦ 1 + ‖z j‖) (Finset.mem_univ i)).symm
    have ho : 1 ≤ ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        (1 + ‖z j‖) := Finset.one_le_prod₀ fun j _ ↦ hfac j
    rw [he]
    nlinarith [hfac i]
  have hdiff (i j : Fin n) : ‖z j - z i‖ ≤ B ^ 2 := by
    calc
      ‖z j - z i‖ ≤ ‖z j‖ + ‖z i‖ := norm_sub_le _ _
      _ ≤ (1 + ‖z j‖) * (1 + ‖z i‖) := by nlinarith [norm_nonneg (z i), norm_nonneg (z j)]
      _ ≤ B * B := mul_le_mul (hiB j) (hiB i) (by positivity) (by positivity)
      _ = B ^ 2 := by ring
  have hinner (i : Fin n) :
      ∏ j > i, ‖z j - z i‖ ≤ (B ^ 2) ^ n := by
    calc
      _ ≤ ∏ j > i, B ^ 2 := by
        apply Finset.prod_le_prod₀
        · intro j hj
          positivity
        · intro j hj
          exact hdiff i j
      _ ≤ (B ^ 2) ^ n := by
        rw [Finset.prod_const]
        apply pow_le_pow_right₀ (by nlinarith [hB])
        exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have hvnorm : ‖vandermonde z‖ ≤ (B ^ 2) ^ (n * n) := by
    rw [vandermonde_eq_product, norm_prod]
    simp_rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin n, (B ^ 2) ^ n :=
        Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦ hinner i
      _ = ((B ^ 2) ^ n) ^ n := by simp
      _ = (B ^ 2) ^ (n * n) := by rw [← pow_mul]
  unfold vandermondeWeight
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖vandermonde z‖ ^ 2 ≤ ((B ^ 2) ^ (n * n)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hvnorm 2
    _ = B ^ (4 * n * n) := by ring
    _ = ∏ i, (1 + ‖z i‖) ^ (4 * n * n) := by
      dsimp [B]
      rw [Finset.prod_pow]

/-- The Vandermonde square is integrable under the concrete Gaussian
reference probability measure. -/
theorem integrable_vandermondeWeight_complexGaussianMeasure (n : ℕ) :
    Integrable (vandermondeWeight : Configuration n → ℝ)
      (complexGaussianMeasure n) := by
  apply Integrable.mono'
    (integrable_prod_one_add_norm_pow_const_complexGaussianMeasure
      n (4 * n * n))
  · exact (Complex.continuous_normSq.comp continuous_vandermonde).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (vandermondeWeight_nonneg z)]
    exact vandermondeWeight_le_prod_one_add_norm_pow n z

/-- The actual normalizing mass of the raw Ginibre measure is finite. -/
theorem ginibreNormalizingMass_lt_top (n : ℕ) :
    ginibreNormalizingMass n < ⊤ := by
  unfold ginibreNormalizingMass rawGinibreMeasure
  rw [withDensity_apply' _ Set.univ, Measure.restrict_univ]
  exact (integrable_vandermondeWeight_complexGaussianMeasure n).lintegral_lt_top

/-- The concrete Ginibre normalizing mass is positive and finite at every
positive particle number. -/
theorem ginibreMassEvaluation : GinibreMassEvaluationStatement := by
  intro n hn
  exact ⟨ginibreNormalizingMass_pos hn, ginibreNormalizingMass_lt_top n⟩

/-- The normalized concrete Ginibre measure has total mass one. -/
theorem ginibreMeasureIsProbability : GinibreMeasureIsProbabilityStatement :=
  ginibreMeasureIsProbability_of_mass_evaluation ginibreMassEvaluation

/-- Typeclass-valued probability assertion for the concrete normalized law. -/
theorem ginibreMeasure_isProbabilityMeasure {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (ginibreMeasure n) :=
  ginibreMeasure_isProbabilityMeasure_of_mass_evaluation
    ginibreMassEvaluation n hn


end

end GinibrePoincare
