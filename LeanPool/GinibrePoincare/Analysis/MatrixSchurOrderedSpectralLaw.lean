/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurOrderedSpectralLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurSymmetricObservable

/-!
# Matrix Schur ordered spectral law

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixGaussian_ordered_symmetric_spectral_integral`.
-/

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section

/-- Exact actual Gaussian matrix spectral integration on the ordered chamber.
The remaining scalar is normalized by the same diagonal density at test function one. -/
theorem matrixGaussian_ordered_symmetric_spectral_integral {n : ℕ} (hn : 0 < n) :
    ∃ d : ℝ≥0∞,
      (∀ F : (Fin n → ℂ) → ℝ≥0∞, Measurable F →
        (∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) →
        ∫⁻ A, F (matrixMeasurableEigenvalues n A) ∂matrixGaussianMeasure n =
          d * ∫⁻ z in matrixSchurOrderedConfigurations n, schurDiagonalSpectralDensity n z * F z) ∧
      1 = d * ∫⁻ z in matrixSchurOrderedConfigurations n, schurDiagonalSpectralDensity n z := by
  obtain ⟨c, hc, hnorm⟩ := matrixSchur_gaussian_global_integral hn
  have h : ∀ F : (Fin n → ℂ) → ℝ≥0∞, Measurable F →
      (∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) →
      ∫⁻ A, F (matrixMeasurableEigenvalues n A) ∂matrixGaussianMeasure n =
        (c * schurUpperGaussianDiagonalFactor n) *
          ∫⁻ z in matrixSchurOrderedConfigurations n, schurDiagonalSpectralDensity n z * F z := by
    intro F hF hsym
    have hg := matrixSimpleSymmetricObservable_measurable F hF
    have hi := hc (matrixSimpleSymmetricObservable n F) hg
      (fun U hU A => matrixSimpleSymmetricObservable_unitary F hsym U A hU)
    have ha := lintegral_congr_ae (matrixSimpleSymmetricObservable_ae F)
    rw [ha] at hi
    have hs : (∫⁻ y in matrixSchurSortedUpperDomain n,
        ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
          (matrixGaussianDensity n (schurUpperCombination y) *
            matrixSimpleSymmetricObservable n F (schurUpperCombination y))) =
        ∫⁻ y in matrixSchurSortedUpperDomain n,
          ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
            (matrixGaussianDensity n (schurUpperCombination y) * F (fun i => schurUpperCombination y
                i i)) := by
      apply setLIntegral_congr_fun (measurableSet_matrixSchurSortedUpperDomain n)
      intro y hy
      exact congrArg (fun v : ℝ≥0∞ =>
        ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
          (matrixGaussianDensity n (schurUpperCombination y) * v))
        (matrixSimpleSymmetricObservable_schurUpper F hsym y hy)
    rw [hs, matrixSchur_sortedUpper_diagonal_integral hn F hF, ← mul_assoc] at hi
    exact hi
  refine ⟨c * schurUpperGaussianDiagonalFactor n, h, ?_⟩
  have h1 := h (fun _ => 1) measurable_const (by intros; rfl)
  simpa only [mul_one, lintegral_const, measure_univ, one_mul] using h1

end
end GinibrePoincare
