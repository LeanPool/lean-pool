/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralLiftLSITransport.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralIntegralTransport
public import LeanPool.GinibrePoincare.Analysis.MatrixGaussianH1Closure
public import LeanPool.GinibrePoincare.Analysis.MatrixSymmetricLift

/-!
# Matrix spectral lift LSI transport

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSpectralLift_H1_overlap_integrable`, `matrixSpectralLift_H1_lsi`.
-/

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section

/-- The actual closed matrix gradient graph has exactly the spectral overlap energy
for intrinsic differentiable symmetric spectral observables. -/
theorem matrixSpectralLift_H1_energy {n : ℕ}
    (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (p : MatrixGaussianSobolevPair n)
    (hd : ∀ i, (p.2 i : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n]
      (fun A => fderiv ℝ (matrixSymmetricLift n F) A (matrixRealCoordinates n (Pi.single i 1)))) :
    matrixGaussianSobolevEnergy n p =
      4 * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  have he : matrixGaussianSobolevEnergy n p =
      ∫ A, matrixRealGradientEnergy n (matrixSymmetricLift n F) A ∂matrixGaussianMeasure n := by
    unfold matrixGaussianSobolevEnergy matrixRealGradientEnergy directionalEnergy
    simp_rw [← integral_square_eq_L2_norm_sq]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      apply integral_congr_ae
      filter_upwards [hd i] with A hA
      exact congrArg (fun v : ℝ => v ^ 2) hA
    · intro i hi
      exact ((Lp.memLp (p.2 i)).ae_eq (hd i)).integrable_sq
  rw [he]
  erw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [matrixGaussian_charpoly_separable_ae n] with A hA
  exact matrixSymmetricLift_energy n A hA F hF hsym

/-- Genuine finite closed-gradient representatives give integrable overlap energy. -/
theorem matrixSpectralLift_H1_overlap_integrable {n : ℕ}
    (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (p : MatrixGaussianSobolevPair n)
    (hd : ∀ i, (p.2 i : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n]
      (fun A => fderiv ℝ (matrixSymmetricLift n F) A (matrixRealCoordinates n (Pi.single i 1)))) :
    Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n) := by
  have hg : Integrable (matrixRealGradientEnergy n (matrixSymmetricLift n F))
      (matrixGaussianMeasure n) := by
    unfold matrixRealGradientEnergy directionalEnergy
    apply integrable_finsetSum
    intro i hi
    exact ((Lp.memLp (p.2 i)).ae_eq (hd i)).integrable_sq
  have he : Integrable (fun A => (4 : ℝ) * matrixSpectralOverlapEnergy n F A)
      (matrixGaussianMeasure n) := by
    apply hg.congr
    filter_upwards [matrixGaussian_charpoly_separable_ae n] with A hA
    exact matrixSymmetricLift_energy n A hA F hF hsym
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (by norm_num : (4 : ℝ) ≠ 0)) _).mp he

/-- Once the ordinary weak derivative pair has been placed in the actual matrix
H1 domain, the proved Ginibre spectral law transports the sharp Gaussian LSI and
entropy integrability to the exact matrix-overlap inequality. -/
theorem matrixSpectralLift_H1_lsi {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (p : MatrixGaussianSobolevPair n) (hp : p ∈ matrixGaussianH1Completion n)
    (hv : (p.1 : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n] matrixSymmetricLift n F)
    (hd : ∀ i, (p.2 i : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n]
      (fun A => fderiv ℝ (matrixSymmetricLift n F) A (matrixRealCoordinates n (Pi.single i 1)))) :
    Integrable (fun z => F z ^ 2 * Real.log (F z ^ 2)) (ginibreMeasure n) ∧
      squareEntropy (ginibreMeasure n) F ≤
        (4 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  obtain ⟨hlog, hlsi⟩ := matrixGaussianH1Completion_lsi n hn p hp
  have hlogLift : Integrable (fun A : Matrix (Fin n) (Fin n) ℂ =>
      F (matrixMeasurableEigenvalues n A) ^ 2 * Real.log (F (matrixMeasurableEigenvalues n A) ^ 2))
      (matrixGaussianMeasure n) := by
    apply hlog.congr
    filter_upwards [hv] with A hA
    exact congrArg (fun v : ℝ => v^2 * Real.log (v^2)) hA
  refine ⟨(matrixSpectralLift_squareLog_integrable_iff hn F hF.continuous.measurable hsym).mp
      hlogLift, ?_⟩
  have hent : squareEntropy (matrixGaussianMeasure n) p.1 = squareEntropy (ginibreMeasure n) F :=
    (squareEntropy_congr_ae _ hv).trans
      (matrixSpectralLift_squareEntropy hn F hF.continuous.measurable hsym)
  rw [hent, matrixSpectralLift_H1_energy F hF hsym p hd] at hlsi
  convert hlsi using 1; ring

end
end GinibrePoincare
