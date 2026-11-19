/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurDensity.lean.
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
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Matrix Schur density

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixGaussianDensity_unitary_schur`.
-/

@[expose] public section

open Matrix
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

theorem matrixHSNormSq_unitary_conjugation (n : ℕ) (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    matrixHSNormSq (U * A * Uᴴ) = matrixHSNormSq A := by
  have h2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hp : (U * A * Uᴴ) * (U * A * Uᴴ)ᴴ = U * (A * Aᴴ) * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = U * A * (Uᴴ * U) * Aᴴ * Uᴴ := by noncomm_ring
      _ = U * (A * Aᴴ) * Uᴴ := by rw [h2]; simp [Matrix.mul_assoc]
  unfold matrixHSNormSq
  rw [hp, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem matrixHSNormSq_diag_remainder (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    matrixHSNormSq A = (∑ i, Complex.normSq (A i i)) +
      matrixHSNormSq (A - Matrix.diagonal fun i => A i i) := by
  classical
  simp_rw [matrixHSNormSq_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : Complex.normSq (A i i) =
      ∑ j : Fin n, if i = j then Complex.normSq (A i j) else 0 := by simp
  rw [hd, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]

/-- The Gaussian matrix density in unitary Schur coordinates factors into a diagonal
Gaussian term and an independent off-diagonal Gaussian term. -/
theorem matrixGaussianDensity_unitary_schur (n : ℕ) (T U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    matrixGaussianDensity n (U * T * Uᴴ) =
      ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n * n) *
        Real.exp (-(n : ℝ) * ∑ i, Complex.normSq (T i i)) *
        Real.exp (-(n : ℝ) * matrixHSNormSq (T - Matrix.diagonal fun i => T i i))) := by
  rw [matrixGaussianDensity, matrixHSNormSq_unitary_conjugation n T U hU,
    matrixHSNormSq_diag_remainder]
  rw [mul_add, Real.exp_add]
  congr 1
  ring

end
end GinibrePoincare
