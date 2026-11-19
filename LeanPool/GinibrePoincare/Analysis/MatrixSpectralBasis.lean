/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralBasis.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSimpleSpectrum
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Eigenbases and simple-spectrum labels for complex matrices -/

@[expose] public section
open Matrix Polynomial
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- Every simple-spectrum complex matrix has an eigenbasis with exactly `n`
distinct labels. This finite algebraic selection is not yet a measurable one. -/
theorem matrixSimpleSpectrum_exists_eigenbasis (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ)
    (hs : G.charpoly.Separable) :
    ∃ eig : Fin n → ℂ, ∃ b : Module.Basis (Fin n) ℂ (Fin n → ℂ),
      Function.Injective eig ∧ ∀ i, G *ᵥ b i = eig i • b i := by
  let s := G.charpoly.roots.toFinset
  have hcard : s.card = n := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs),
        IsAlgClosed.card_roots_eq_natDegree,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : Fin n ≃ s := (Fintype.equivFinOfCardEq (show Fintype.card s = n by simpa using
                                                                               hcard)).symm
  let eig : Fin n → ℂ := fun i => e i
  have hinj : Function.Injective eig := Subtype.val_injective.comp e.injective
  have heigen (i : Fin n) : Module.End.HasEigenvalue G.toLin' (eig i) := by
    apply Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    rw [Matrix.spectrum_toLin', Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots G.charpoly_monic.ne_zero).mp
      (Multiset.mem_toFinset.mp (e i).property)
  choose r hr using fun i => (heigen i).exists_hasEigenvector
  have hli := Module.End.eigenvectors_linearIndependent' G.toLin' eig hinj r hr
  let b := basisOfLinearIndependentOfCardEqFinrank' r hli
    (by simp [Module.finrank_fintype_fun_eq_card])
  refine ⟨eig, b, hinj, fun i => ?_⟩
  have hb : ⇑b = r := coe_basisOfLinearIndependentOfCardEqFinrank' r hli _
  rw [congr_fun hb i]
  simpa only [Matrix.toLin'_apply] using (hr i).apply_eq_smul

theorem matrixGaussian_exists_eigenbasis_ae (n : ℕ) :
    ∀ᵐ G ∂matrixGaussianMeasure n,
      ∃ eig : Fin n → ℂ, ∃ b : Module.Basis (Fin n) ℂ (Fin n → ℂ),
        Function.Injective eig ∧ ∀ i, G *ᵥ b i = eig i • b i := by
  filter_upwards [matrixGaussian_charpoly_separable_ae n] with G hG
  exact matrixSimpleSpectrum_exists_eigenbasis n G hG

/-- The left vectors dual to any basis in the standard complex coordinates. -/
def matrixBasisLeftVector {n : ℕ} (b : Module.Basis (Fin n) ℂ (Fin n → ℂ))
    (j : Fin n) : Fin n → ℂ := fun k => star (b.coord j (Pi.single k 1))

theorem matrixBasisLeftVector_dot {n : ℕ} (b : Module.Basis (Fin n) ℂ (Fin n → ℂ))
    (j : Fin n) (x : Fin n → ℂ) :
    star (matrixBasisLeftVector b j) ⬝ᵥ x = b.coord j x := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → ℂ) := by
    ext k
    simp [Pi.single_apply]
  have h := congrArg (b.coord j) hx
  simpa [matrixBasisLeftVector, dotProduct, mul_comm] using h.symm

theorem matrixBasisLeftVector_biorthogonal {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (Fin n → ℂ)) (j k : Fin n) :
    star (matrixBasisLeftVector b j) ⬝ᵥ b k = if j = k then 1 else 0 := by
  rw [matrixBasisLeftVector_dot]
  simp [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]

theorem matrixBasisLeftVector_left_eigenvector {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (eig : Fin n → ℂ)
    (b : Module.Basis (Fin n) ℂ (Fin n → ℂ))
    (hG : ∀ i, G *ᵥ b i = eig i • b i) (j : Fin n) :
    star (matrixBasisLeftVector b j) ᵥ* G = eig j • star (matrixBasisLeftVector b j) := by
  have hc : (b.coord j).comp G.toLin' = eig j • b.coord j := by
    apply b.ext
    intro k
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hG, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    by_cases h : j = k
    · subst k; simp [Module.Basis.coord_apply]
    · simp [Module.Basis.coord_apply, h]
  ext k
  have he := congrArg (fun f : (Fin n → ℂ) →ₗ[ℂ] ℂ => f (Pi.single k 1)) hc
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.smul_apply,
    smul_eq_mul, ← matrixBasisLeftVector_dot] at he
  simpa [Matrix.dotProduct_mulVec, Matrix.vecMul, dotProduct, Pi.single_apply] using he

/-- The normalized biorthogonal left/right eigenvectors used in the matrix
lift exist for every simple-spectrum matrix. -/
theorem matrixSimpleSpectrum_exists_biorthogonal_eigenvectors (n : ℕ)
    (G : Matrix (Fin n) (Fin n) ℂ) (hs : G.charpoly.Separable) :
    ∃ eig : Fin n → ℂ, ∃ r l : Fin n → Fin n → ℂ,
      Function.Injective eig ∧
        (∀ j, G *ᵥ r j = eig j • r j) ∧
        (∀ j, star (l j) ᵥ* G = eig j • star (l j)) ∧
        (∀ j k, star (l j) ⬝ᵥ r k = if j = k then 1 else 0) := by
  obtain ⟨eig, b, hi, hr⟩ := matrixSimpleSpectrum_exists_eigenbasis n G hs
  exact ⟨eig, b, matrixBasisLeftVector b, hi, hr,
    fun j => matrixBasisLeftVector_left_eigenvector G eig b hr j,
    matrixBasisLeftVector_biorthogonal b⟩

end
end GinibrePoincare
