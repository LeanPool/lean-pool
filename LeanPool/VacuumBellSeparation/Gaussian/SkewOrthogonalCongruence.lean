/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SkewMatrixNormalForm

/-!
# Orthogonal congruence for an actual nonsingular skew matrix

The columns are the constructed orthonormal normal-form basis, expressed
in the actual Euclidean standard basis. Both orthogonality identities are
proved even though the mode index type differs from the original index.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℝ E] in
theorem orthonormal_basis_matrix_transpose
    (a : OrthonormalBasis ι ℝ E) (b : OrthonormalBasis κ ℝ E) :
    (a.toBasis.toMatrix b)ᵀ = b.toBasis.toMatrix a := by
  ext i j
  simpa only [Matrix.transpose_apply, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply] using
      (real_inner_comm (a j) (b i)).symm

variable [DecidableEq ι] [DecidableEq κ]

theorem orthonormal_basis_matrix_congruence
    (a : OrthonormalBasis ι ℝ E) (b : OrthonormalBasis κ ℝ E)
    (A : E →ₗ[ℝ] E) :
    a.toBasis.toMatrix b * LinearMap.toMatrixOrthonormal b A *
      (a.toBasis.toMatrix b)ᵀ = LinearMap.toMatrixOrthonormal a A := by
  rw [orthonormal_basis_matrix_transpose]
  exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    a.toBasis b.toBasis a.toBasis b.toBasis A

/-- Nonsingular real skew matrices have an actual orthogonal congruence
with positive symplectic mode blocks. -/
theorem exists_skew_orthogonal_congruence (B : Matrix ι ι ℝ)
    (hB : Bᵀ = -B) (hunit : IsUnit B) :
    ∃ (m : ℕ) (ν : Fin m → ℝ) (O : Matrix ι (Fin m × Fin 2) ℝ),
      (∀ i, 0 < ν i) ∧ O * Oᵀ = 1 ∧ Oᵀ * O = 1 ∧
      O * (modeDiagonal ν * modeSymplecticForm) * Oᵀ = B := by
  let A := B.toEuclideanLin
  have hA : A.adjoint = -A := by
    dsimp [A]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial, hB, map_neg]
  have hinj : Function.Injective A := by
    exact (ContinuousLinearMap.isUnit_iff_bijective.mp
      (hunit.map (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).toMonoidHom)).1
  obtain ⟨m, ν, b, hν, hb⟩ := exists_real_skew_matrix_normal_form A hA hinj
  let a := EuclideanSpace.basisFun ι ℝ
  let O := a.toBasis.toMatrix b
  have haa : LinearMap.toMatrixOrthonormal a A = B :=
    LinearMap.toMatrix_toLin a.toBasis a.toBasis B
  refine ⟨m, ν, O, hν, ?_, ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      a.toMatrix_orthonormalBasis_self_mul_conjTranspose b
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      a.toMatrix_orthonormalBasis_conjTranspose_mul_self b
  · rw [← hb]
    exact (orthonormal_basis_matrix_congruence a b A).trans haa

end VacuumBellSeparation.Gaussian
