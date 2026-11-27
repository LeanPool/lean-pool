/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteMatrixPositiveTrace
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianCoordinateTransport
public import LeanPool.VacuumBellSeparation.Gaussian.CompactTraceNorm

/-!
# Real covariance matrix norms equal the actual complex operator norms

Entrywise complexification preserves the genuine positive square root
and absolute value. Real orthogonal spectral diagonalization proves
operator-norm preservation, including the empty index type. The actual
Hilbert positive trace identifies the nuclear norm without a dimension
factor or an entrywise matrix norm substitution.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {ι : Type*}

theorem matrixOperator_real_smulCommClass {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    SMulCommClass ℝ (E →L[ℂ] E) (E →L[ℂ] E) := Algebra.to_smulCommClass

/-- Real scalar multiplication commutes with composition on the coordinate Hilbert space. -/
local instance euclideanOperatorRealSMulCommClass [Finite ι] :
    let _ : Fintype ι := Fintype.ofFinite ι
    SMulCommClass ℝ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
      (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  exact matrixOperator_real_smulCommClass

variable [Fintype ι]

theorem complexifyMatrix_sqrt {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    open scoped Classical in
    complexifyMatrix (CFC.sqrt A) = CFC.sqrt (complexifyMatrix A) := by
  classical
  symm
  apply CFC.sqrt_unique
  · rw [← complexifyMatrix_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact (complexifyMatrix_posSemidef (CFC.sqrt_nonneg A).posSemidef).nonneg

theorem complexifyMatrix_abs (A : Matrix ι ι ℝ) :
    open scoped Classical in
    complexifyMatrix (CFC.abs A) = CFC.abs (complexifyMatrix A) := by
  classical
  simp only [CFC.abs, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [complexifyMatrix_sqrt (by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A), complexifyMatrix_mul,
    complexifyMatrix_transpose]

variable [DecidableEq ι]

omit [Fintype ι] in
theorem complexifyMatrix_diagonal (d : ι → ℝ) :
    complexifyMatrix (Matrix.diagonal d) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [Matrix.diagonal_apply_ne _ h]

omit [DecidableEq ι] in
theorem norm_complex_ofReal_pi (d : ι → ℝ) : ‖fun i => (d i : ℂ)‖ = ‖d‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg d)).mpr
    intro i
    simpa using norm_le_pi_norm d i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun i => (d i : ℂ)))).mpr
    intro i
    simpa using norm_le_pi_norm (fun j => (d j : ℂ)) i

theorem norm_complexifyMatrix_of_isHermitian {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) : ‖complexifyMatrix A‖ = ‖A‖ := by
  let O : Matrix ι ι ℝ := hA.eigenvectorUnitary
  have hO : Oᵀ * O = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  let U := orthogonalComplexUnitary O hO
  have he : A = O * Matrix.diagonal hA.eigenvalues * Oᵀ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id,
      Function.id_comp] using hA.spectral_theorem
  calc
    ‖complexifyMatrix A‖ =
        ‖(U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
          ((star U : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)‖ := by
      conv_lhs => rw [he]
      rw [complexifyMatrix_mul, complexifyMatrix_mul,
        complexifyMatrix_transpose, complexifyMatrix_diagonal]
      rfl
    _ = ‖Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))‖ := by
      rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
    _ = ‖hA.eigenvalues‖ := by rw [Matrix.l2_opNorm_diagonal, norm_complex_ofReal_pi]
    _ = ‖A‖ := by
      conv_rhs => rw [he]
      rw [norm_real_orthogonal_conjugate O _ hO, Matrix.l2_opNorm_diagonal]

theorem norm_complexifyMatrix (A : Matrix ι ι ℝ) : ‖complexifyMatrix A‖ = ‖A‖ := by
  have hh := norm_complexifyMatrix_of_isHermitian
    (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, complexifyMatrix_mul,
    complexifyMatrix_transpose, Matrix.l2_opNorm_conjTranspose_mul_self] at hh
  have hr : ‖Aᵀ * A‖ = ‖A‖ * ‖A‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose_mul_self A
  rw [hr] at hh
  nlinarith [norm_nonneg (complexifyMatrix A), norm_nonneg A]

theorem toEuclideanCLM_sqrt {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (CFC.sqrt A) = CFC.sqrt ((Matrix.toEuclideanCLM
      (n := ι) (𝕜 := ℂ)) A) := by
  symm
  apply CFC.sqrt_unique
  · rw [← map_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact map_nonneg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (CFC.sqrt_nonneg A)

theorem toEuclideanCLM_abs (A : Matrix ι ι ℂ) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (CFC.abs A) = CFC.abs ((Matrix.toEuclideanCLM
      (n := ι) (𝕜 := ℂ)) A) := by
  have hA : (star A * A).PosSemidef := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self A
  rw [CFC.abs, toEuclideanCLM_sqrt hA, map_mul, map_star]
  rfl

/-- Continuous linear map for the real matrix operator, of type `EuclideanSpace ℂ ι →L[ℂ]
EuclideanSpace ℂ ι`. -/
def realMatrixOperator (A : Matrix ι ι ℝ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (complexifyMatrix A)

theorem norm_realMatrixOperator (A : Matrix ι ι ℝ) : ‖realMatrixOperator A‖ = ‖A‖ := by
  rw [realMatrixOperator, Matrix.l2_opNorm_toEuclideanCLM, norm_complexifyMatrix]

theorem operatorTraceNorm_realMatrixOperator (A : Matrix ι ι ℝ) :
    operatorTraceNorm (realMatrixOperator A) = ENNReal.ofReal (matrixTraceNorm A) := by
  rw [operatorTraceNorm, realMatrixOperator, ← toEuclideanCLM_abs,
    positiveTrace_toEuclideanCLM (CFC.abs_nonneg (complexifyMatrix A)).posSemidef,
    ← complexifyMatrix_abs]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, complexifyMatrix_apply,
    Complex.ofReal_re, matrixTraceNorm]

end VacuumBellSeparation.Gaussian
