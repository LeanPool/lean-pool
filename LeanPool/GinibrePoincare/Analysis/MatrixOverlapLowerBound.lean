/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixOverlapLowerBound.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurDiagonal
public import LeanPool.GinibrePoincare.Analysis.MatrixSchurDensity
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralProjector
public import LeanPool.GinibrePoincare.Analysis.MatrixSymmetricLift
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure

/-!
# Matrix overlap lower bound

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSpectralOverlapEnergy_ge_gradient`.
-/

@[expose] public section

open Matrix
open scoped BigOperators Matrix
namespace GinibrePoincare
noncomputable section

/-- Hilbert--Schmidt energy dominates the squared eigenvalues, even when
some eigenvalues coincide, provided an actual eigenbasis is given. -/
theorem matrixHSNormSq_ge_eigenbasis {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Module.Basis (Fin n) ℂ (Fin n → ℂ)) (a : Fin n → ℂ)
    (ha : ∀ i, A *ᵥ b i = a i • b i) :
    (∑ i, Complex.normSq (a i)) ≤ matrixHSNormSq A := by
  classical
  let e := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  let f := e.symm.toLinearMap.comp (A.toLin'.comp e.toLinearMap)
  let b' := b.map e.symm
  have hb' (i : Fin n) : f (b' i) = a i • b' i := by
    change e.symm (A *ᵥ e (e.symm (b i))) = a i • e.symm (b i)
    rw [e.apply_symm_apply, ha i, map_smul]
  let s := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨Q, T, hQ, hT, hdiag, he⟩ :=
    eigenbasis_exists_unitary_schur_with_diagonal n f b' a hb' s
  have hmat : LinearMap.toMatrix s.toBasis s.toBasis f = A := by
    ext i j
    simp [LinearMap.toMatrix_apply, s, f, e, EuclideanSpace.basisFun_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      Matrix.toLin'_apply]
  have hA : A = Q * T * Qᴴ := hmat ▸ he
  rw [hA, matrixHSNormSq_unitary_conjugation n T Q hQ, matrixHSNormSq_eq_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [← hdiag i]
  exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (T i j)) (Finset.mem_univ i)

/-- The overlap matrix of a normalized biorthogonal eigenbasis dominates
identity as a quadratic form, without a normality assumption. -/
theorem matrixOverlapEnergy_biorthogonal_ge {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (Fin n → ℂ)) (a : Fin n → ℂ) :
    (∑ i, Complex.normSq (a i)) ≤
      matrixOverlapEnergy (fun j => matrixRankOneProjector (b j)
        (matrixBasisLeftVector b j)) a := by
  classical
  rw [matrixOverlapEnergy_eq_HS]
  apply matrixHSNormSq_ge_eigenbasis _ b a
  intro i
  simp only [matrixProjectorCombination, Matrix.sum_mulVec, Matrix.smul_mulVec,
    matrixRankOneProjector_mulVec, matrixBasisLeftVector_biorthogonal]
  simp []

/-- Canonical projectors for every simple matrix obey the same lower bound. -/
theorem matrixEigenvalueProjector_overlap_ge {n : ℕ}
    (G : GinibreMatrixCoordinates n) (hs : (Matrix.of G).charpoly.Separable)
    (a : Fin n → ℂ) :
    (∑ i, Complex.normSq (a i)) ≤
      matrixOverlapEnergy (fun j => matrixEigenvalueProjector n G
        (matrixMeasurableEigenvalues n G j)) a := by
  classical
  obtain ⟨eig, b, hi, hb⟩ := matrixSimpleSpectrum_exists_eigenbasis n (Matrix.of G) hs
  obtain ⟨hl, hr⟩ := matrixMeasurableEigenvalues_spec n G hs
  obtain ⟨e, he⟩ := matrixSimpleSpectrum_labels_permutation n (Matrix.of G) hs eig
    (matrixMeasurableEigenvalues n G) hi hl
    (matrixEigenbasis_eigenvalue_isRoot (Matrix.of G) eig b hb) hr
  let b' := b.reindex e.symm
  have hb' (i : Fin n) : Matrix.of G *ᵥ b' i =
      matrixMeasurableEigenvalues n G i • b' i := by
    simp only [b', Module.Basis.reindex_apply, Equiv.symm_symm]
    rw [hb, he]
  have hp (i : Fin n) : matrixEigenvalueProjector n G
      (matrixMeasurableEigenvalues n G i) =
      matrixRankOneProjector (b' i) (matrixBasisLeftVector b' i) :=
    matrixEigenvalueProjector_eq_rankOne G _ b' hs hl hb' i (hr i)
  simp_rw [hp]
  exact matrixOverlapEnergy_biorthogonal_ge b' a

theorem realGradientNormSq_eq_wirtinger {n : ℕ}
    (F : Configuration n → ℝ) (z : Configuration n) :
    realGradientNormSq F z =
      4 * ∑ i, Complex.normSq (realDifferentialWirtinger (fderiv ℝ F z) i) := by
  classical
  rw [realGradientNormSq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hd (w : ℂ) : coordinateDirection i w = Pi.single i w := by
    ext j
    simp [coordinateDirection, Pi.single_apply]
  simp [realDifferentialWirtinger, Complex.normSq_apply,
    realCoordinateDirection, imaginaryCoordinateDirection, hd]
  ring

/-- Ordinary spectral gradient energy is bounded by four times actual
matrix overlap energy at every simple-spectrum matrix. -/
theorem matrixSpectralOverlapEnergy_ge_gradient {n : ℕ}
    (G : GinibreMatrixCoordinates n) (hs : (Matrix.of G).charpoly.Separable)
    (F : Configuration n → ℝ) :
    realGradientNormSq F (matrixMeasurableEigenvalues n G) ≤
      4 * matrixSpectralOverlapEnergy n F G := by
  rw [realGradientNormSq_eq_wirtinger]
  exact mul_le_mul_of_nonneg_left
    (matrixEigenvalueProjector_overlap_ge G hs
      (realDifferentialWirtinger (fderiv ℝ F (matrixMeasurableEigenvalues n G)))) (by norm_num)

end
end GinibrePoincare
