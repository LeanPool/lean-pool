/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixDeterminantDerivative.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixLocalEigenvalue
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Jacobi's differential formula without an invertibility assumption -/

@[expose] public section
open scoped BigOperators Topology
open Matrix
namespace GinibrePoincare
noncomputable section

/-- The determinant as a continuous multilinear map of the rows of an `n × n` complex matrix. -/
def matrixDeterminantMultilinear (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin n → ℂ) ℂ where
  toMultilinearMap := (Matrix.detRowAlternating (n := Fin n) (R := ℂ)).toMultilinearMap
  cont := by
    change Continuous (fun G : GinibreMatrixCoordinates n => (Matrix.of G).det)
    simp only [Matrix.det_apply', Matrix.of_apply]
    fun_prop

theorem matrixDeterminantMultilinear_apply (n : ℕ) (G : GinibreMatrixCoordinates n) :
    matrixDeterminantMultilinear n G = (Matrix.of G).det := rfl

/-- The derivative of the determinant at the matrix `G`, as a continuous `ℂ`-linear map. -/
def matrixDeterminantDerivative (n : ℕ) (G : GinibreMatrixCoordinates n) :
    GinibreMatrixCoordinates n →L[ℂ] ℂ :=
  (matrixDeterminantMultilinear n).linearDeriv G

theorem matrixDeterminant_hasFDerivAt (n : ℕ) (G : GinibreMatrixCoordinates n) :
    HasFDerivAt (fun A : GinibreMatrixCoordinates n => (Matrix.of A).det)
      (matrixDeterminantDerivative n G) G :=
  (matrixDeterminantMultilinear n).hasFDerivAt G

theorem matrixDeterminantDerivative_apply (n : ℕ) (G H : GinibreMatrixCoordinates n) :
    matrixDeterminantDerivative n G H =
      Matrix.trace ((Matrix.of G).adjugate * Matrix.of H) := by
  rw [matrixDeterminantDerivative, ContinuousMultilinearMap.linearDeriv_apply]
  simp only [matrixDeterminantMultilinear_apply]
  have hrow (i : Fin n) : (Matrix.of (Function.update G i (H i))).det =
      ∑ j, (Matrix.of G).adjugate j i * H i j := by
    change ((Matrix.of G).updateRow i (H i)).det = _
    rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
      ← Matrix.adjugate_transpose]
    simp [Matrix.mulVec, dotProduct]
  simp_rw [hrow]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_comm]

end
end GinibrePoincare
