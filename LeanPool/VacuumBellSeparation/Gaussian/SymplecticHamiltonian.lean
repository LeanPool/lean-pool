/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveSquareRootDerivative
public import LeanPool.VacuumBellSeparation.Gaussian.HermitianTraceDerivative
public import LeanPool.VacuumBellSeparation.Gaussian.QuantumWilliamson

/-!
# The actual Hermitian matrix carrying the symplectic spectrum

For a real skew form Ω and a positive covariance V, the matrix is
literally i sqrt(V) Ω sqrt(V). The square-root derivative proved by the
inverse function theorem gives its actual derivative. This module does not
identify the Gaussian purity with a function of its signed spectrum; that identification is
`log_positiveTrace_gaussianPhysical_rpow_eq_covariancePurityTrace` in
`Gaussian/SymplecticHamiltonianNormalForm.lean`.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexConjugate Topology RightActions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complexify matrix continuous linear map of type `Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℂ`. -/
def complexifyMatrixCLM : Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := complexifyMatrix
      map_add' := by intro A B; ext i j; simp [complexifyMatrix]
      map_smul' := by intro c A; ext i j; simp [complexifyMatrix] }

omit [DecidableEq ι] in
@[simp] theorem complexifyMatrixCLM_apply (A : Matrix ι ι ℝ) :
    complexifyMatrixCLM A = complexifyMatrix A := rfl

omit [DecidableEq ι] [Fintype ι] in
theorem complexifyMatrix_neg (A : Matrix ι ι ℝ) :
    complexifyMatrix (-A) = -complexifyMatrix A := by
  ext i j
  simp [complexifyMatrix]

omit [DecidableEq ι] [Fintype ι] in
theorem complexifyMatrix_add (A B : Matrix ι ι ℝ) :
    complexifyMatrix (A + B) = complexifyMatrix A + complexifyMatrix B := by
  ext i j
  simp [complexifyMatrix]

/-- Symplectic Hamiltonian given by `Complex.I • complexifyMatrix (CFC.sqrt V * Ω * CFC.sqrt V)`. -/
def symplecticHamiltonian (Ω V : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  Complex.I • complexifyMatrix (CFC.sqrt V * Ω * CFC.sqrt V)

theorem symplecticHamiltonian_isHermitian {Ω : Matrix ι ι ℝ}
    (hΩ : Ωᵀ = -Ω) (V : Matrix ι ι ℝ) :
    (symplecticHamiltonian Ω V).IsHermitian := by
  have hR : (CFC.sqrt V)ᵀ = CFC.sqrt V := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg V).isSelfAdjoint.star_eq
  have hK : (CFC.sqrt V * Ω * CFC.sqrt V)ᵀ = -(CFC.sqrt V * Ω * CFC.sqrt V) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hR, hΩ]
    simp only [Matrix.neg_mul, Matrix.mul_neg]
    congr 1
    noncomm_ring
  change (symplecticHamiltonian Ω V)ᴴ = symplecticHamiltonian Ω V
  rw [symplecticHamiltonian, Matrix.conjTranspose_smul, ← complexifyMatrix_transpose,
    hK, complexifyMatrix_neg]
  simp

/-- Symmetric Hamiltonian represented by `symplecticHamiltonian Ω V`. -/
def symmetricHamiltonian (Ω : Matrix ι ι ℝ) (hΩ : Ωᵀ = -Ω)
    (V : RealSymmetricMatrixSpace ι) : HermitianMatrixSpace ι :=
  ⟨symplecticHamiltonian Ω V, symplecticHamiltonian_isHermitian hΩ V⟩

/-- Directional derivative of the symplectic Hamiltonian with respect to covariance. -/
def symplecticHamiltonianDerivative (Ω : Matrix ι ι ℝ)
    (V : RealSymmetricMatrixSpace ι) (hV : (V : Matrix ι ι ℝ).PosDef) :
    RealSymmetricMatrixSpace ι →L[ℝ] Matrix ι ι ℂ :=
  let R := CFC.sqrt (V : Matrix ι ι ℝ)
  let D := (positiveSylvesterSelfAdjointContinuousEquiv (matrix_sqrt_posDef hV)).symm
  LinearMap.toContinuousLinearMap
    { toFun := fun X => Complex.I • complexifyMatrix
        (((D X : RealSymmetricMatrixSpace ι) : Matrix ι ι ℝ) * Ω * R +
          R * Ω * ((D X : RealSymmetricMatrixSpace ι) : Matrix ι ι ℝ))
      map_add' := by
        intro X Y
        simp only [map_add, Submodule.coe_add, Matrix.add_mul, Matrix.mul_add,
          complexifyMatrix_add, smul_add]
        exact add_add_add_comm _ _ _ _
      map_smul' := by
        intro c X
        simp only [map_smul, Submodule.coe_smul, Matrix.smul_mul, Matrix.mul_smul,
          ← smul_add, ← complexifyMatrixCLM_apply, map_smul]
        exact smul_comm Complex.I c _ }

@[simp] theorem symplecticHamiltonianDerivative_apply (Ω : Matrix ι ι ℝ)
    (V X : RealSymmetricMatrixSpace ι) (hV : (V : Matrix ι ι ℝ).PosDef) :
    symplecticHamiltonianDerivative Ω V hV X = Complex.I • complexifyMatrix
      ((((positiveSylvesterSelfAdjointContinuousEquiv (matrix_sqrt_posDef hV)).symm X :
          RealSymmetricMatrixSpace ι) : Matrix ι ι ℝ) * Ω * CFC.sqrt (V : Matrix ι ι ℝ) +
        CFC.sqrt (V : Matrix ι ι ℝ) * Ω *
          (((positiveSylvesterSelfAdjointContinuousEquiv (matrix_sqrt_posDef hV)).symm X :
            RealSymmetricMatrixSpace ι) : Matrix ι ι ℝ)) := rfl

theorem hasFDerivAt_symplecticHamiltonian (Ω : Matrix ι ι ℝ)
    (V : RealSymmetricMatrixSpace ι) (hV : (V : Matrix ι ι ℝ).PosDef) :
    HasFDerivAt (fun X : RealSymmetricMatrixSpace ι => symplecticHamiltonian Ω X)
      (symplecticHamiltonianDerivative Ω V hV) V := by
  let e : RealSymmetricMatrixSpace ι →L[ℝ] Matrix ι ι ℝ :=
    (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)).subtypeL
  have hs := e.hasFDerivAt.comp V (hasFDerivAt_symmetricMatrixSqrt V hV)
  have hp := (hs.mul_const' Ω).mul' hs
  have hc := (complexifyMatrixCLM (ι := ι)).hasFDerivAt.comp V hp
  have hi := hc.const_smul Complex.I
  convert hi using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro X
    let R := CFC.sqrt (V : Matrix ι ι ℝ)
    let D := (positiveSylvesterSelfAdjointContinuousEquiv (matrix_sqrt_posDef hV)).symm
    change Complex.I • complexifyMatrix
      (((D X : RealSymmetricMatrixSpace ι) : Matrix ι ι ℝ) * Ω * R +
        R * Ω * ((D X : RealSymmetricMatrixSpace ι) : Matrix ι ι ℝ)) =
      Complex.I • complexifyMatrix
        (R * Ω * ((D X : RealSymmetricMatrixSpace ι) : Matrix ι ι ℝ) +
          ((D X : RealSymmetricMatrixSpace ι) : Matrix ι ι ℝ) * Ω * R)
    rw [add_comm]

end VacuumBellSeparation.Gaussian
