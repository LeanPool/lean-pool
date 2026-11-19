/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurGaussianGlobal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurGlobalIntegration

/-! # Inserting the Gaussian density into global Schur integration

The matrix Gaussian density depends only on the Hilbert–Schmidt squared norm,
which is invariant under unitary conjugation. Multiply a unitary-invariant test
by that density and apply the global volume integration formula. Testing with
the constant one gives the mass equation that determines the common angular
constant in subsequent spectral-law comparisons.
-/

@[expose] public section

open Matrix NormedSpace MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
namespace GinibrePoincare
noncomputable section

theorem matrixGaussianDensity_unitary_invariant (n : ℕ)
    (U A : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    matrixGaussianDensity n (U * A * Uᴴ) = matrixGaussianDensity n A := by
  unfold matrixGaussianDensity
  rw [matrixHSNormSq_unitary_conjugation n A U hU]

/-- The genuine Gaussian matrix integral is a single angular constant times the
sorted triangular Vandermonde integral, and its total mass fixes that constant. -/
theorem matrixSchur_gaussian_global_integral {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ≥0∞,
      (∀ g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞, Measurable g →
        (∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, g (U * A * Uᴴ) = g A) →
        ∫⁻ A, g A ∂matrixGaussianMeasure n = c *
          ∫⁻ y in matrixSchurSortedUpperDomain n,
            ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
              (matrixGaussianDensity n (schurUpperCombination y) * g (schurUpperCombination y))) ∧
      1 = c * ∫⁻ y in matrixSchurSortedUpperDomain n,
        ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
          matrixGaussianDensity n (schurUpperCombination y) := by
  obtain ⟨c, hc⟩ := matrixSchur_global_integral n
  have h : ∀ g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞, Measurable g →
      (∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, g (U * A * Uᴴ) = g A) →
      ∫⁻ A, g A ∂matrixGaussianMeasure n = c *
        ∫⁻ y in matrixSchurSortedUpperDomain n,
          ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
            (matrixGaussianDensity n (schurUpperCombination y) * g (schurUpperCombination y)) := by
    intro g hg hInv
    rw [matrixGaussianMeasure_eq_withDensity hn,
      lintegral_withDensity_eq_lintegral_mul volume (measurable_matrixGaussianDensity n) hg]
    apply hc
    · exact (measurable_matrixGaussianDensity n).mul hg
    · intro U hU A
      simp only [Pi.mul_apply]
      rw [matrixGaussianDensity_unitary_invariant n U A hU, hInv U hU A]
  refine ⟨c, h, ?_⟩
  have h1 := h (fun _ => 1) measurable_const (by intros; rfl)
  simpa only [mul_one, lintegral_const, measure_univ, one_mul] using h1

end
end GinibrePoincare
