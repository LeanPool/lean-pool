/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralIntegralTransport.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixGinibreSpectralLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreEntropy

/-!
# Matrix spectral integral transport

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSpectralLift_squareEntropy`, `matrixSpectralLift_squareLog_integrable_iff`,
`matrixSpectralLift_memLp_two_iff`.
-/

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section

theorem matrixSpectralLift_integrable_iff {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    Integrable (fun A : Matrix (Fin n) (Fin n) ℂ => F (matrixMeasurableEigenvalues n A))
        (matrixGaussianMeasure n) ↔
      Integrable F (ginibreMeasure n) := by
  have hM : Measurable (fun A : Matrix (Fin n) (Fin n) ℂ => F (matrixMeasurableEigenvalues n A)) :=
    hF.comp (matrixMeasurableEigenvalues_measurable n)
  have he := matrixGaussian_symmetric_spectral_lintegral hn
    (fun z => ENNReal.ofReal ‖F z‖) (ENNReal.measurable_ofReal.comp hF.norm)
    (by intro e z; rw [hsym])
  constructor
  · intro h
    refine ⟨hF.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    rw [← he]
    exact (hasFiniteIntegral_iff_norm _).mp h.hasFiniteIntegral
  · intro h
    refine ⟨hM.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact he.symm ▸ (hasFiniteIntegral_iff_norm _).mp h.hasFiniteIntegral

theorem matrixSpectralLift_integral {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    ∫ A, F (matrixMeasurableEigenvalues n A) ∂matrixGaussianMeasure n =
      ∫ z, F z ∂ginibreMeasure n := by
  by_cases hi : Integrable F (ginibreMeasure n)
  · have hMi := (matrixSpectralLift_integrable_iff hn F hF hsym).mpr hi
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hMi,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi]
    congr 1
    · exact congrArg ENNReal.toReal (matrixGaussian_symmetric_spectral_lintegral hn
        (fun z => ENNReal.ofReal (F z)) (ENNReal.measurable_ofReal.comp hF)
        (by intro e z; rw [hsym]))
    · exact congrArg ENNReal.toReal (matrixGaussian_symmetric_spectral_lintegral hn
        (fun z => ENNReal.ofReal (-F z)) (ENNReal.measurable_ofReal.comp hF.neg)
        (by intro e z; rw [hsym]))
  · have hMi := mt (matrixSpectralLift_integrable_iff hn F hF hsym).mp hi
    rw [integral_undef hMi, integral_undef hi]

theorem matrixSpectralLift_square_integral {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    ∫ A, F (matrixMeasurableEigenvalues n A) ^ 2 ∂matrixGaussianMeasure n =
      ∫ z, F z ^ 2 ∂ginibreMeasure n :=
  matrixSpectralLift_integral hn (fun z => F z ^ 2) (hF.pow_const 2)
    (by intro e z; rw [hsym])

theorem matrixSpectralLift_squareEntropy {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    squareEntropy (matrixGaussianMeasure n) (fun A => F (matrixMeasurableEigenvalues n A)) =
      squareEntropy (ginibreMeasure n) F := by
  have hs := matrixSpectralLift_square_integral hn F hF hsym
  have hl := matrixSpectralLift_integral hn (fun z => F z ^ 2 * Real.log (F z ^ 2))
    ((hF.pow_const 2).mul (hF.pow_const 2).log) (by intro e z; rw [hsym])
  unfold squareEntropy
  exact congrArg₂ (fun a b : ℝ => a - b * Real.log b) hl hs

theorem matrixSpectralLift_squareLog_integrable_iff {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    Integrable (fun A : Matrix (Fin n) (Fin n) ℂ =>
      F (matrixMeasurableEigenvalues n A) ^ 2 * Real.log (F (matrixMeasurableEigenvalues n A) ^ 2))
      (matrixGaussianMeasure n) ↔
      Integrable (fun z => F z ^ 2 * Real.log (F z ^ 2)) (ginibreMeasure n) :=
  matrixSpectralLift_integrable_iff hn (fun z => F z ^ 2 * Real.log (F z ^ 2))
    ((hF.pow_const 2).mul (hF.pow_const 2).log) (by intro e z; rw [hsym])

theorem matrixSpectralLift_memLp_two_iff {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    MemLp (fun A : Matrix (Fin n) (Fin n) ℂ => F (matrixMeasurableEigenvalues n A)) 2
      (matrixGaussianMeasure n) ↔ MemLp F 2 (ginibreMeasure n) := by
  have hM : Measurable (fun A : Matrix (Fin n) (Fin n) ℂ => F (matrixMeasurableEigenvalues n A)) :=
    hF.comp (matrixMeasurableEigenvalues_measurable n)
  exact (memLp_two_iff_integrable_sq hM.aestronglyMeasurable).trans
    ((matrixSpectralLift_integrable_iff hn (fun z => F z ^ 2) (hF.pow_const 2)
      (by intro e z; rw [hsym])).trans (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).symm)

end
end GinibrePoincare
