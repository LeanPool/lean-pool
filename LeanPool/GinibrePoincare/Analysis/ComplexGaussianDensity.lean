/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/ComplexGaussianDensity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianDensity
public import LeanPool.GinibrePoincare.Analysis.FinitePiDensity
public import LeanPool.GinibrePoincare.Analysis.MeasureTransport
public import LeanPool.GinibrePoincare.Concrete.MeasureModel

/-! # Explicit density of the complex Gaussian product law -/


@[expose] public section


open Fintype MeasureTheory
open scoped ENNReal BigOperators

namespace GinibrePoincare

noncomputable section

/-- Density of one complex coordinate in the Ginibre normalization. -/
def complexCoordinateGaussianDensity (n : ℕ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((n : ℝ) / Real.pi) *
    Real.exp (-(n : ℝ) * Complex.normSq z))

theorem measurable_complexCoordinateGaussianDensity (n : ℕ) :
    Measurable (complexCoordinateGaussianDensity n) := by
  unfold complexCoordinateGaussianDensity
  fun_prop

private theorem real_density_product_formula {n : ℕ} (hn : 0 < n)
    (x : Fin 2 → ℝ) :
    ∏ i, ProbabilityTheory.gaussianPDF 0 (realCoordinateVariance n) (x i) =
      complexCoordinateGaussianDensity n
        (Complex.measurableEquivPi.symm x) := by
  simp_rw [realCoordinateGaussianPDF_formula hn]
  simp only [Fin.prod_univ_two, complexCoordinateGaussianDensity,
    Complex.measurableEquivPi_symm_apply, Complex.normSq_apply]
  rw [← ENNReal.ofReal_mul]
  · congr 1
    have hnR : (0 : ℝ) < n := by positivity
    have hsqrt : Real.sqrt (Real.pi / n) ^ 2 = Real.pi / n := by
      rw [Real.sq_sqrt]
      positivity
    calc
      _ = (Real.sqrt (Real.pi / n))⁻¹ ^ 2 *
          (Real.exp (-(n : ℝ) * x 0 ^ 2) *
            Real.exp (-(n : ℝ) * x 1 ^ 2)) := by ring
      _ = (Real.sqrt (Real.pi / n))⁻¹ ^ 2 *
          Real.exp (-(n : ℝ) * x 0 ^ 2 + -(n : ℝ) * x 1 ^ 2) := by
            rw [Real.exp_add]
      _ = _ := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im, mul_one,
          sub_zero, add_zero, Complex.add_im, zero_add]
        have hc : (Real.sqrt (Real.pi / n))⁻¹ ^ 2 = (n : ℝ) / Real.pi := by
          rw [inv_pow, hsqrt]
          field_simp
        rw [hc]
        simp [hn.ne']
        ring
  · positivity

/-- One complex Gaussian coordinate has density
`(n / π) exp (-n |z|²)` with respect to complex Lebesgue measure. -/
theorem complexCoordinateGaussianMeasure_eq_withDensity {n : ℕ} (hn : 0 < n) :
    (complexCoordinateGaussianProbability n : Measure ℂ) =
      (volume : Measure ℂ).withDensity (complexCoordinateGaussianDensity n) := by
  unfold complexCoordinateGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi]
  rw [show Measure.pi (fun _ : Fin 2 ↦
        (realCoordinateGaussianProbability n : Measure ℝ)) =
      Measure.pi (fun _ : Fin 2 ↦
        (volume : Measure ℝ).withDensity
          (ProbabilityTheory.gaussianPDF 0 (realCoordinateVariance n))) by
      congr 1
      funext i
      exact realCoordinateGaussianMeasure_eq_withDensity hn]
  have hsf : ∀ i : Fin 2, SigmaFinite
      ((volume : Measure ℝ).withDensity
        (ProbabilityTheory.gaussianPDF 0 (realCoordinateVariance n))) :=
    fun i ↦ by
      rw [← realCoordinateGaussianMeasure_eq_withDensity hn]
      infer_instance
  have hpi := @Measure.pi_withDensity _ _ _ _
    (fun _ : Fin 2 ↦ (volume : Measure ℝ)) (by intro i; infer_instance)
    (fun _ : Fin 2 ↦ ProbabilityTheory.gaussianPDF 0 (realCoordinateVariance n))
    (fun _ ↦ ProbabilityTheory.measurable_gaussianPDF _ _) hsf
  rw [hpi]
  rw [← volume_pi]
  have hdensity :
      (fun x : Fin 2 → ℝ ↦
        ∏ i, ProbabilityTheory.gaussianPDF 0
          (realCoordinateVariance n) (x i)) =
        complexCoordinateGaussianDensity n ∘
          Complex.measurableEquivPi.symm := by
    funext x
    exact real_density_product_formula hn x
  rw [hdensity]
  exact MeasureTheory.map_complexPi_withDensity
    (measurable_complexCoordinateGaussianDensity n)

private theorem coordinate_density_product_formula {n : ℕ} (hn : 0 < n)
    (z : Configuration n) :
    ∏ i, complexCoordinateGaussianDensity n (z i) =
      complexGaussianDensity n z := by
  simp only [complexCoordinateGaussianDensity, complexGaussianDensity]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
    simp only [configurationNormSq, gaussianWeight]
    rw [← Finset.mul_sum]
    simp
  · intro i hi
    positivity

/-- The product construction of the Gaussian reference law agrees with its
explicit Lebesgue density. -/
theorem complexGaussianDensityIdentification :
    ComplexGaussianDensityIdentificationStatement := by
  intro n hn
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  rw [show Measure.pi (fun _ : Fin n ↦
        (complexCoordinateGaussianProbability n : Measure ℂ)) =
      Measure.pi (fun _ : Fin n ↦
        (volume : Measure ℂ).withDensity
          (complexCoordinateGaussianDensity n)) by
      congr 1
      funext i
      exact complexCoordinateGaussianMeasure_eq_withDensity hn]
  have hsf : ∀ i : Fin n, SigmaFinite
      ((volume : Measure ℂ).withDensity
        (complexCoordinateGaussianDensity n)) :=
    fun i ↦ by
      rw [← complexCoordinateGaussianMeasure_eq_withDensity hn]
      infer_instance
  have hpi := @Measure.pi_withDensity _ _ _ _
    (fun _ : Fin n ↦ (volume : Measure ℂ)) (by intro i; infer_instance)
    (fun _ : Fin n ↦ complexCoordinateGaussianDensity n)
    (fun _ ↦ measurable_complexCoordinateGaussianDensity n) hsf
  rw [hpi]
  · rw [← volume_pi]
    unfold complexGaussianDensityMeasure configurationVolume
    congr 1
    funext z
    exact coordinate_density_product_formula hn z

end

end GinibrePoincare
