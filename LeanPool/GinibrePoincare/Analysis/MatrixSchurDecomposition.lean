/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurDecomposition.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralBasis
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.LinearAlgebra.Matrix.Basis

/-! # Schur decomposition on simple spectrum

An eigenbasis gives an invariant flag of initial spans. Gram–Schmidt preserves
these initial spans, so the same endomorphism is upper triangular in the resulting
orthonormal basis. Changing from that basis to a fixed orthonormal basis produces
a unitary matrix and the Schur conjugation identity. The matrix endpoint applies
this construction to the eigenbasis available on simple spectrum; the Gaussian
endpoint uses almost-everywhere separability of the characteristic polynomial.
This proof establishes the simple-spectrum case needed by the integration route.
-/

@[expose] public section

open Submodule InnerProductSpace
open scoped Matrix
namespace GinibrePoincare
noncomputable section

/-- Applying Gram--Schmidt to an eigenbasis gives an actual orthonormal basis in
which the endomorphism is upper triangular. -/
theorem eigenbasis_exists_orthonormal_upperTriangular {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (n : ℕ) (f : E →ₗ[ℂ] E) (b : Module.Basis (Fin n) ℂ E) (eig : Fin n → ℂ)
    (hb : ∀ i, f (b i) = eig i • b i) :
    ∃ o : OrthonormalBasis (Fin n) ℂ E, ∀ i j, j < i → o.repr (f (o j)) i = 0 := by
  classical
  have hdim : Module.finrank ℂ E = Fintype.card (Fin n) := Module.finrank_eq_card_basis b
  let o := gramSchmidtOrthonormalBasis hdim b
  have ho : (o : Fin n → E) = gramSchmidtNormed ℂ b := by
    funext i
    exact gramSchmidtOrthonormalBasis_apply hdim
      ((gramSchmidtNormed_linearIndependent b.linearIndependent).ne_zero i)
  have hspan (j : Fin n) : Submodule.span ℂ (o '' Set.Iic j) =
      Submodule.span ℂ (b '' Set.Iic j) := by
    rw [ho, span_gramSchmidtNormed, span_gramSchmidt_Iic]
  refine ⟨o, fun i j hij => ?_⟩
  have hj : o j ∈ Submodule.span ℂ (b '' Set.Iic j) := by
    rw [← hspan j]
    exact Submodule.subset_span (Set.mem_image_of_mem o (by simp))
  have hf : f (o j) ∈ Submodule.span ℂ (b '' Set.Iic j) := by
    apply Submodule.span_induction (p := fun x _ => f x ∈ Submodule.span ℂ (b '' Set.Iic j))
      ?_ ?_ ?_ ?_ hj
    · rintro x ⟨k, hk, rfl⟩
      rw [hb k]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_image_of_mem b hk))
    · simp
    · intro x y hx hy hfx hfy
      simpa only [map_add] using Submodule.add_mem _ hfx hfy
    · intro c x hx hfx
      simpa only [map_smul] using Submodule.smul_mem _ c hfx
  rw [← hspan j] at hf
  have hs := o.toBasis.repr_support_subset_of_mem_span (Set.Iic j) hf
  have hz := (Finsupp.mem_supported' _ _).mp ((Finsupp.mem_supported ℂ _).mpr hs)
    i (show i ∉ Set.Iic j from not_le_of_gt hij)
  simpa only [OrthonormalBasis.coe_toBasis_repr_apply] using hz

theorem eigenbasis_exists_unitary_schur {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (n : ℕ) (f : E →ₗ[ℂ] E) (b : Module.Basis (Fin n) ℂ E) (eig : Fin n → ℂ)
    (hb : ∀ i, f (b i) = eig i • b i) (s : OrthonormalBasis (Fin n) ℂ E) :
    ∃ Q T : Matrix (Fin n) (Fin n) ℂ,
      Q ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ (∀ i j, j < i → T i j = 0) ∧
        LinearMap.toMatrix s.toBasis s.toBasis f = Q * T * Qᴴ := by
  classical
  obtain ⟨o, ho⟩ := eigenbasis_exists_orthonormal_upperTriangular n f b eig hb
  let Q := s.toBasis.toMatrix o
  let R := o.toBasis.toMatrix s
  let T := LinearMap.toMatrix o.toBasis o.toBasis f
  have hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ := s.toMatrix_orthonormalBasis_mem_unitary o
  have hQQ : Q * Qᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hQ
  have hRQ : R * Q = 1 := by
    change o.toBasis.toMatrix s.toBasis * s.toBasis.toMatrix o.toBasis = 1
    rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
  have hR : R = Qᴴ := by
    calc
      R = R * (Q * Qᴴ) := by rw [hQQ, Matrix.mul_one]
      _ = (R * Q) * Qᴴ := by rw [Matrix.mul_assoc]
      _ = Qᴴ := by rw [hRQ, Matrix.one_mul]
  have he : Q * T * R = LinearMap.toMatrix s.toBasis s.toBasis f := by
    change s.toBasis.toMatrix o.toBasis * T * o.toBasis.toMatrix s.toBasis = _
    simp only [← LinearMap.toMatrix_id_eq_basis_toMatrix]
    unfold T
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    simp
  refine ⟨Q, T, hQ, ?_, ?_⟩
  · intro i j hij
    simpa only [T, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply] using ho i j hij
  · rw [← hR]
    exact he.symm

/-- Every actual simple complex matrix admits a unitary Schur decomposition. -/
theorem matrixSimpleSpectrum_exists_unitary_schur (n : ℕ)
    (G : Matrix (Fin n) (Fin n) ℂ) (hs : G.charpoly.Separable) :
    ∃ Q T : Matrix (Fin n) (Fin n) ℂ,
      Q ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ (∀ i j, j < i → T i j = 0) ∧ G = Q * T * Qᴴ := by
  classical
  obtain ⟨eig, b, hi, hb⟩ := matrixSimpleSpectrum_exists_eigenbasis n G hs
  let e := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  let f := e.symm.toLinearMap.comp (G.toLin'.comp e.toLinearMap)
  let b' := b.map e.symm
  have hb' (i : Fin n) : f (b' i) = eig i • b' i := by
    change e.symm (G *ᵥ e (e.symm (b i))) = eig i • e.symm (b i)
    rw [e.apply_symm_apply, hb i, map_smul]
  let s := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨Q, T, hQ, hT, he⟩ := eigenbasis_exists_unitary_schur n f b' eig hb' s
  have hmat : LinearMap.toMatrix s.toBasis s.toBasis f = G := by
    ext i j
    simp [LinearMap.toMatrix_apply, s, f, e, EuclideanSpace.basisFun_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      Matrix.toLin'_apply]
  exact ⟨Q, T, hQ, hT, hmat ▸ he⟩

theorem matrixGaussian_exists_unitary_schur_ae (n : ℕ) :
    ∀ᵐ G ∂matrixGaussianMeasure n, ∃ Q T : Matrix (Fin n) (Fin n) ℂ,
      Q ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ (∀ i j, j < i → T i j = 0) ∧ G = Q * T * Qᴴ := by
  filter_upwards [matrixGaussian_charpoly_separable_ae n] with G hG
  exact matrixSimpleSpectrum_exists_unitary_schur n G hG

end
end GinibrePoincare
