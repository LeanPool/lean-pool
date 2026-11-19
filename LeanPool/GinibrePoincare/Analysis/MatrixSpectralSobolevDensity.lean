/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevDensity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixGaussianMeasure

/-! # Actual strictly positive bounded Gaussian matrix density -/

@[expose] public section
open MeasureTheory Matrix
open scoped ENNReal
namespace GinibrePoincare
noncomputable section

/-- The real-valued Ginibre matrix density `(n / π)^(n²) exp (-n ‖A‖²_HS)`. -/
def matrixGaussianDensityReal (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (((n : ℝ) / Real.pi) ^ (n * n)) * Real.exp (-(n : ℝ) * matrixHSNormSq A)

theorem matrixGaussianDensityReal_pos (n : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) : 0 < matrixGaussianDensityReal n A := by
  unfold matrixGaussianDensityReal
  positivity

theorem matrixGaussianDensity_le_const (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    matrixGaussianDensity n A ≤ ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n * n)) := by
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp (-(n : ℝ) * matrixHSNormSq A) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n))
      (matrixHSNormSq_nonneg A)
  change (((n : ℝ) / Real.pi) ^ (n * n)) * Real.exp (-(n : ℝ) * matrixHSNormSq A) ≤ _
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)

theorem matrixGaussianMeasure_le_finite_smul_volume (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧
      matrixGaussianMeasure n ≤ c • (volume : Measure (Matrix (Fin n) (Fin n) ℂ)) := by
  refine ⟨ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n * n)), ENNReal.ofReal_ne_top, ?_⟩
  rw [matrixGaussianMeasure_eq_withDensity hn, ← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall (matrixGaussianDensity_le_const n))

end
end GinibrePoincare
