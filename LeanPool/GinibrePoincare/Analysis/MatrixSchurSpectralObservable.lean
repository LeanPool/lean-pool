/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurSpectralObservable.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSymmetricLift
public import LeanPool.GinibrePoincare.Analysis.MatrixSchurDensity

/-!
# Matrix Schur spectral observable

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSymmetricLift_unitary_schur`.
-/

@[expose] public section

open Matrix
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

theorem matrix_charpoly_unitary_conjugation {n : ℕ} (T U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (U * T * Uᴴ).charpoly = T.charpoly := by
  have hh : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hh]
  simp

theorem schur_diagonal_roots {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (i : Fin n) : T.charpoly.eval (T i i) = 0 := by
  classical
  rw [Matrix.charpoly_of_isUpperTriangular T hT, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

/-- A symmetric spectral observable is exactly the same function of the Schur diagonal,
independently of the unitary conjugating matrix and the strict upper entries. -/
theorem matrixSymmetricLift_unitary_schur {n : ℕ} (T U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hd : Function.Injective (fun i => T i i))
    (F : (Fin n → ℂ) → ℝ) (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    matrixSymmetricLift n F (U * T * Uᴴ) = F (fun i => T i i) := by
  have hr : ∀ i, (U * T * Uᴴ).charpoly.eval (T i i) = 0 := by
    intro i
    rw [matrix_charpoly_unitary_conjugation T U hU]
    exact schur_diagonal_roots T hT i
  have hs := matrix_injective_full_roots_separable n (U * T * Uᴴ) _ hd hr
  have hc := matrixMeasurableEigenvalues_spec n (U * T * Uᴴ) hs
  exact matrixSimpleSpectrum_symmetric_value n (U * T * Uᴴ) hs
    (matrixMeasurableEigenvalues n (U * T * Uᴴ)) (fun i => T i i)
    hc.1 hd hc.2 hr F hsym

end
end GinibrePoincare
