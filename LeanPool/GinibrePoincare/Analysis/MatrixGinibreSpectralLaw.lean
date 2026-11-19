/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixGinibreSpectralLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurChamberIntegration
public import LeanPool.GinibrePoincare.Analysis.GinibreMassFiniteness

/-! # Identifying Gaussian matrix spectral expectations with Ginibre expectations

Write the Ginibre measure as its normalized Vandermonde-weighted Gaussian
density. Symmetry partitions its integral into permutation chambers, producing
the same ordered diagonal integral that comes from Schur integration of Gaussian
matrices. Both measures have mass one; this proves the common chamber integral
is nonzero and finite, allowing cancellation of the two normalizing constants.
Consequently all measurable symmetric nonnegative spectral tests have identical
expectations. No spectral density identification is supplied as a hypothesis.
-/

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibre_lintegral_diagonal_density {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂ginibreMeasure n =
      ((ginibreNormalizingMass n)⁻¹ * ENNReal.ofReal (((n : ℝ)/Real.pi)^n)) *
        ∫⁻ z, schurDiagonalSpectralDensity n z * F z := by
  have hv : Measurable (vandermondeDensity : (Fin n → ℂ) → ℝ≥0∞) := by
    exact ENNReal.measurable_ofReal.comp
      (Complex.continuous_normSq.measurable.comp continuous_vandermonde.measurable)
  rw [ginibreMeasure, lintegral_smul_measure, rawGinibreMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hv hF,
    complexGaussianDensityIdentification n hn]
  unfold complexGaussianDensityMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_complexGaussianDensity n) (hv.mul hF)]
  have he : (fun z : Fin n → ℂ => complexGaussianDensity n z * (vandermondeDensity z * F z)) =
      (fun z => ENNReal.ofReal (((n : ℝ)/Real.pi)^n) * (schurDiagonalSpectralDensity n z * F z)) :=
          by
    funext z
    unfold complexGaussianDensity gaussianWeight configurationNormSq vandermondeDensity
        schurDiagonalSpectralDensity
    rw [ENNReal.ofReal_mul (pow_nonneg (div_nonneg (Nat.cast_nonneg n) Real.pi_pos.le) _)]
    ac_rfl
  simp only [Pi.mul_apply]
  rw [he]
  change (ginibreNormalizingMass n)⁻¹ *
    (∫⁻ z, ENNReal.ofReal (((n : ℝ)/Real.pi)^n) * (schurDiagonalSpectralDensity n z * F z)) = _
  rw [lintegral_const_mul (f := fun z => schurDiagonalSpectralDensity n z * F z) _
    ((measurable_schurDiagonalSpectralDensity n).mul hF), ← mul_assoc]

/-- Normalized Ginibre integration over the genuine lexicographic ordered chamber. -/
theorem ginibre_ordered_symmetric_integral {n : ℕ} (hn : 0 < n) :
    ∃ q : ℝ≥0∞,
      (∀ F : (Fin n → ℂ) → ℝ≥0∞, Measurable F →
        (∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) →
        ∫⁻ z, F z ∂ginibreMeasure n = q *
          ∫⁻ z in matrixSchurOrderedConfigurations n, schurDiagonalSpectralDensity n z * F z) ∧
      1 = q * ∫⁻ z in matrixSchurOrderedConfigurations n, schurDiagonalSpectralDensity n z := by
  let := ginibreMeasure_isProbabilityMeasure hn
  let q := ((ginibreNormalizingMass n)⁻¹ * ENNReal.ofReal (((n : ℝ)/Real.pi)^n)) *
    (Fintype.card (Fin n ≃ Fin n) : ℝ≥0∞)
  have h : ∀ F : (Fin n → ℂ) → ℝ≥0∞, Measurable F →
      (∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) →
      ∫⁻ z, F z ∂ginibreMeasure n = q *
        ∫⁻ z in matrixSchurOrderedConfigurations n, schurDiagonalSpectralDensity n z * F z := by
    intro F hF hsym
    rw [ginibre_lintegral_diagonal_density hn F hF,
      matrixSchur_ordered_density_integral F hF hsym, ← mul_assoc]
  refine ⟨q, h, ?_⟩
  have h1 := h (fun _ => 1) measurable_const (by intros; rfl)
  simpa only [mul_one, lintegral_const, measure_univ, one_mul] using h1

/-- The actual Gaussian matrix spectrum has precisely Ginibre expectations for
all measurable symmetric tests. This follows from the global Schur Jacobian and
probability normalization, with no density-identification hypothesis. -/
theorem matrixGaussian_symmetric_spectral_lintegral {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ≥0∞) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    ∫⁻ A, F (matrixMeasurableEigenvalues n A) ∂matrixGaussianMeasure n =
      ∫⁻ z, F z ∂ginibreMeasure n := by
  obtain ⟨d, hd, hd1⟩ := matrixGaussian_ordered_symmetric_spectral_integral hn
  obtain ⟨q, hq, hq1⟩ := ginibre_ordered_symmetric_integral hn
  let K := ∫⁻ z in matrixSchurOrderedConfigurations n, schurDiagonalSpectralDensity n z
  have hchamberMass_ne_zero : K ≠ 0 := by
    intro hz
    change 1 = d * K at hd1
    rw [hz, mul_zero] at hd1
    exact one_ne_zero hd1
  have hmatrixConstant_ne_zero : d ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hd1
    exact one_ne_zero hd1
  have hp : d * K ≠ ∞ := by
    rw [← hd1]
    exact ENNReal.one_ne_top
  have hchamberMass_ne_top : K ≠ ∞ := ne_of_lt (ENNReal.lt_top_of_mul_ne_top_right hp
      hmatrixConstant_ne_zero)
  have he : d = q := (ENNReal.mul_left_inj hchamberMass_ne_zero hchamberMass_ne_top).mp
      (hd1.symm.trans hq1)
  rw [hd F hF hsym, hq F hF hsym, he]

end
end GinibrePoincare
