/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralProjector.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixEigenvalueProjector
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralBasis
public import Mathlib.LinearAlgebra.Trace

/-! # Identifying the canonical adjugate projector with biorthogonal eigenvectors -/

@[expose] public section
open Matrix
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

theorem matrixRankOneProjector_mulVec {n : ℕ} (r l x : Fin n → ℂ) :
    matrixRankOneProjector r l *ᵥ x = (star l ⬝ᵥ x) • r := by
  ext i
  simp only [Matrix.mulVec, dotProduct, matrixRankOneProjector, Pi.star_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem matrixBasis_twoSided_eigenmatrix {n : ℕ}
    (G T : Matrix (Fin n) (Fin n) ℂ) (eig : Fin n → ℂ)
    (b : Module.Basis (Fin n) ℂ (Fin n → ℂ)) (hinj : Function.Injective eig)
    (hG : ∀ i, G *ᵥ b i = eig i • b i) (j : Fin n)
    (hleft : G * T = eig j • T) (hright : T * G = eig j • T) :
    T = Matrix.trace T • matrixRankOneProjector (b j) (matrixBasisLeftVector b j) := by
  let e := Matrix.toLinAlgEquiv' |>.trans (LinearMap.toMatrixAlgEquiv b)
  have hdiag : e G = Matrix.diagonal eig := by
    ext i k
    simp only [e, AlgEquiv.trans_apply, LinearMap.toMatrixAlgEquiv_apply,
        Matrix.toLinAlgEquiv'_apply]
    rw [hG]
    by_cases h : i = k <;> simp [h]
  have hl : Matrix.diagonal eig * e T = eig j • e T := by
    rw [← hdiag, ← map_mul, hleft, map_smul]
  have hr : e T * Matrix.diagonal eig = eig j • e T := by
    rw [← hdiag, ← map_mul, hright, map_smul]
  have hrow (i k : Fin n) (hi : i ≠ j) : e T i k = 0 := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i k) hl
    simp only [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] at h
    have hz : (eig i - eig j) * e T i k = 0 := by linear_combination h
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (hinj.ne hi))
  have hcol (i k : Fin n) (hk : k ≠ j) : e T i k = 0 := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i k) hr
    simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] at h
    have hz : (eig k - eig j) * e T i k = 0 := by linear_combination h
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (hinj.ne hk))
  have ht : Matrix.trace (e T) = Matrix.trace T := by
    change Matrix.trace (LinearMap.toMatrix b b T.toLin') = _
    rw [← LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace_toLin'_eq]
  have hc : e T j j = Matrix.trace T := by
    rw [← ht]
    simp only [Matrix.trace, Matrix.diag_apply]
    symm
    apply Finset.sum_eq_single j
    · intro k _ hk
      exact hrow k k hk
    · simp
  have hP : e (matrixRankOneProjector (b j) (matrixBasisLeftVector b j)) =
      Matrix.single j j 1 := by
    ext i k
    simp only [e, AlgEquiv.trans_apply, LinearMap.toMatrixAlgEquiv_apply,
        Matrix.toLinAlgEquiv'_apply]
    rw [matrixRankOneProjector_mulVec, matrixBasisLeftVector_biorthogonal]
    by_cases hk : k = j
    · subst k
      simp [Matrix.single, Finsupp.single_apply]
    · simp [Ne.symm hk, Matrix.single]
  apply e.injective
  rw [map_smul, hP]
  ext i k
  by_cases hi : i = j
  · subst i
    by_cases hk : k = j
    · subst k; simp [hc, Matrix.single]
    · simp [hcol j k hk, Matrix.single, Ne.symm hk]
  · simp [hrow i k hi, Matrix.single, Ne.symm hi]

theorem matrixEigenvalueProjector_eigenmatrix (n : ℕ) (G : GinibreMatrixCoordinates n)
    (z : ℂ) (hz : (Matrix.of G).charpoly.eval z = 0) :
    Matrix.of G * matrixEigenvalueProjector n G z = z • matrixEigenvalueProjector n G z ∧
      matrixEigenvalueProjector n G z * Matrix.of G = z • matrixEigenvalueProjector n G z := by
  let Q := Matrix.scalar (Fin n) z - Matrix.of G
  have hdet : Q.det = 0 := by rw [← Matrix.eval_charpoly]; exact hz
  have hl : Matrix.of G * Q.adjugate = z • Q.adjugate := by
    have h := Matrix.mul_adjugate Q
    change (Matrix.scalar (Fin n) z - Matrix.of G) * Q.adjugate = Q.det • 1 at h
    rw [hdet, zero_smul, Matrix.sub_mul, matrixScalar_eq_smul_one,
      Matrix.smul_mul, Matrix.one_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hr : Q.adjugate * Matrix.of G = z • Q.adjugate := by
    have h := Matrix.adjugate_mul Q
    change Q.adjugate * (Matrix.scalar (Fin n) z - Matrix.of G) = Q.det • 1 at h
    rw [hdet, zero_smul, Matrix.mul_sub, matrixScalar_eq_smul_one,
      Matrix.mul_smul, Matrix.mul_one] at h
    exact (sub_eq_zero.mp h).symm
  constructor
  · simp only [matrixEigenvalueProjector, Matrix.mul_smul]
    rw [hl]
    simp [smul_smul, mul_comm, Q]
  · simp only [matrixEigenvalueProjector, Matrix.smul_mul]
    rw [hr]
    simp [smul_smul, mul_comm, Q]

/-- The differential's canonical adjugate projector is exactly `r ℓ*`
for the normalized dual eigenbasis. -/
theorem matrixEigenvalueProjector_eq_rankOne {n : ℕ}
    (G : GinibreMatrixCoordinates n) (eig : Fin n → ℂ)
    (b : Module.Basis (Fin n) ℂ (Fin n → ℂ)) (hs : (Matrix.of G).charpoly.Separable)
    (hinj : Function.Injective eig) (hG : ∀ i, Matrix.of G *ᵥ b i = eig i • b i)
    (j : Fin n) (hz : (Matrix.of G).charpoly.eval (eig j) = 0) :
    matrixEigenvalueProjector n G (eig j) =
      matrixRankOneProjector (b j) (matrixBasisLeftVector b j) := by
  obtain ⟨hl, hr⟩ := matrixEigenvalueProjector_eigenmatrix n G (eig j) hz
  have he := matrixBasis_twoSided_eigenmatrix (Matrix.of G)
    (matrixEigenvalueProjector n G (eig j)) eig b hinj hG j hl hr
  simpa only [matrixEigenvalueProjector_trace n G (eig j) hs hz, one_smul] using he

theorem matrixEigenvalueProjector_mul {n : ℕ}
    (G : GinibreMatrixCoordinates n) (eig : Fin n → ℂ)
    (b : Module.Basis (Fin n) ℂ (Fin n → ℂ)) (hs : (Matrix.of G).charpoly.Separable)
    (hinj : Function.Injective eig) (hG : ∀ i, Matrix.of G *ᵥ b i = eig i • b i)
    (hz : ∀ i, (Matrix.of G).charpoly.eval (eig i) = 0) (j k : Fin n) :
    matrixEigenvalueProjector n G (eig j) * matrixEigenvalueProjector n G (eig k) =
      if j = k then matrixEigenvalueProjector n G (eig j) else 0 := by
  simp_rw [matrixEigenvalueProjector_eq_rankOne G eig b hs hinj hG _ (hz _)]
  exact matrixRankOneProjector_biorthogonal b (matrixBasisLeftVector b)
    (matrixBasisLeftVector_biorthogonal b) j k

end
end GinibrePoincare
