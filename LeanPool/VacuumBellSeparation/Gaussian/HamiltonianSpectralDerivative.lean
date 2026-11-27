/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SymplecticHamiltonian

/-!
# Differentiation into the genuine Hermitian matrix space

The derivative of i sqrt(V) Ω sqrt(V) is itself Hermitian. Projecting the
already proved ambient derivative therefore gives its derivative in the
actual self-adjoint subspace, where the spectral trace derivative applies.
The scalar spectral remainder is explicit in the generic composition
theorem; this file does not assume a Gaussian purity differential.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix Filter
open scoped MatrixOrder Matrix.Norms.L2Operator Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem symplecticHamiltonianDerivative_isHermitian
    {Ω : Matrix ι ι ℝ} (hΩ : Ωᵀ = -Ω)
    (V X : RealSymmetricMatrixSpace ι) (hV : (V : Matrix ι ι ℝ).PosDef) :
    (symplecticHamiltonianDerivative Ω V hV X).IsHermitian := by
  let R := CFC.sqrt (V : Matrix ι ι ℝ)
  let Y : RealSymmetricMatrixSpace ι :=
    (positiveSylvesterSelfAdjointContinuousEquiv (matrix_sqrt_posDef hV)).symm X
  have hR : Rᵀ = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (matrix_sqrt_posDef hV).isHermitian.eq
  have hY : (Y : Matrix ι ι ℝ)ᵀ = Y := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (realSymmetricMatrix_isHermitian Y).eq
  have hK : ((Y : Matrix ι ι ℝ) * Ω * R + R * Ω * (Y : Matrix ι ι ℝ))ᵀ =
      -((Y : Matrix ι ι ℝ) * Ω * R + R * Ω * (Y : Matrix ι ι ℝ)) := by
    simp only [Matrix.transpose_add, Matrix.transpose_mul, hR, hY, hΩ,
      Matrix.neg_mul, Matrix.mul_neg]
    noncomm_ring
  change (Complex.I • complexifyMatrix ((Y : Matrix ι ι ℝ) * Ω * R + R * Ω *
    (Y : Matrix ι ι ℝ)))ᴴ = _
  rw [Matrix.conjTranspose_smul, ← complexifyMatrix_transpose, hK, complexifyMatrix_neg]
  simp [R, Y]

/-- The same self-adjoint projection, with the genuine real submodule as codomain. -/
def hermitianMatrixPartL : Matrix ι ι ℂ →L[ℝ] HermitianMatrixSpace ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => ⟨selfAdjointPart ℝ A, (selfAdjointPart ℝ A).property⟩
      map_add' := by
        intro A B
        apply Subtype.ext
        exact congrArg (fun X : selfAdjoint (Matrix ι ι ℂ) => (X : Matrix ι ι ℂ))
          (map_add (selfAdjointPart ℝ (A := Matrix ι ι ℂ)) A B)
      map_smul' := by
        intro c A
        apply Subtype.ext
        exact congrArg (fun X : selfAdjoint (Matrix ι ι ℂ) => (X : Matrix ι ι ℂ))
          (map_smul (selfAdjointPart ℝ (A := Matrix ι ι ℂ)) c A) }

/-- Continuous linear map for the symmetric Hamiltonian derivative, of type
`RealSymmetricMatrixSpace ι →L[ℝ] HermitianMatrixSpace ι`. -/
def symmetricHamiltonianDerivative (Ω : Matrix ι ι ℝ)
    (V : RealSymmetricMatrixSpace ι) (hV : (V : Matrix ι ι ℝ).PosDef) :
    RealSymmetricMatrixSpace ι →L[ℝ] HermitianMatrixSpace ι :=
  (hermitianMatrixPartL (ι := ι)).comp (symplecticHamiltonianDerivative Ω V hV)

theorem symmetricHamiltonianDerivative_coe
    {Ω : Matrix ι ι ℝ} (hΩ : Ωᵀ = -Ω)
    (V X : RealSymmetricMatrixSpace ι) (hV : (V : Matrix ι ι ℝ).PosDef) :
    ((symmetricHamiltonianDerivative Ω V hV X : HermitianMatrixSpace ι) : Matrix ι ι ℂ) =
      symplecticHamiltonianDerivative Ω V hV X := by
  exact (symplecticHamiltonianDerivative_isHermitian hΩ V X
    hV).isSelfAdjoint.coe_selfAdjointPart_apply ℝ

theorem hasFDerivAt_symmetricHamiltonian
    {Ω : Matrix ι ι ℝ} (hΩ : Ωᵀ = -Ω)
    (V : RealSymmetricMatrixSpace ι) (hV : (V : Matrix ι ι ℝ).PosDef) :
    HasFDerivAt (symmetricHamiltonian Ω hΩ)
      (symmetricHamiltonianDerivative Ω V hV) V := by
  have h := (hermitianMatrixPartL (ι := ι)).hasFDerivAt.comp V
    (hasFDerivAt_symplecticHamiltonian Ω V hV)
  convert h using 1
  · funext X
    apply Subtype.ext
    exact ((symplecticHamiltonian_isHermitian hΩ X).isSelfAdjoint.coe_selfAdjointPart_apply ℝ).symm
  · rfl

/-- Continuous linear map for the hamiltonian spectral derivative, of type
`RealSymmetricMatrixSpace ι →L[ℝ] ℝ`. -/
def hamiltonianSpectralDerivative (Ω : Matrix ι ι ℝ) (hΩ : Ωᵀ = -Ω)
    (V : RealSymmetricMatrixSpace ι) (hV : (V : Matrix ι ι ℝ).PosDef) (d : ℝ → ℝ) :
    RealSymmetricMatrixSpace ι →L[ℝ] ℝ :=
  (hermitianTraceDerivative (symmetricHamiltonian Ω hΩ V) d).comp
    (symmetricHamiltonianDerivative Ω V hV)

theorem hamiltonianSpectralDerivative_apply
    (Ω : Matrix ι ι ℝ) (hΩ : Ωᵀ = -Ω)
    (V X : RealSymmetricMatrixSpace ι) (hV : (V : Matrix ι ι ℝ).PosDef) (d : ℝ → ℝ) :
    hamiltonianSpectralDerivative Ω hΩ V hV d X =
      (cfc d (symplecticHamiltonian Ω V) *
        symplecticHamiltonianDerivative Ω V hV X).trace.re := by
  change (cfc d (symplecticHamiltonian Ω V) *
    ((symmetricHamiltonianDerivative Ω V hV X : HermitianMatrixSpace ι) : Matrix ι ι
      ℂ)).trace.re = _
  rw [symmetricHamiltonianDerivative_coe hΩ V X hV]

theorem hasFDerivAt_hamiltonianSpectralTrace_of_scalar_remainder
    (Ω : Matrix ι ι ℝ) (hΩ : Ωᵀ = -Ω)
    (V : RealSymmetricMatrixSpace ι) (hV : (V : Matrix ι ι ℝ).PosDef)
    (f d : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hrem : ∀ᶠ B : HermitianMatrixSpace ι in 𝓝 (symmetricHamiltonian Ω hΩ V), ∀ i j,
      |f ((hermitianMatrix_isHermitian B).eigenvalues j) -
        f ((hermitianMatrix_isHermitian (symmetricHamiltonian Ω hΩ V)).eigenvalues i) -
        d ((hermitianMatrix_isHermitian (symmetricHamiltonian Ω hΩ V)).eigenvalues i) *
          ((hermitianMatrix_isHermitian B).eigenvalues j -
            (hermitianMatrix_isHermitian (symmetricHamiltonian Ω hΩ V)).eigenvalues i)| ≤
        C * ((hermitianMatrix_isHermitian B).eigenvalues j -
          (hermitianMatrix_isHermitian (symmetricHamiltonian Ω hΩ V)).eigenvalues i) ^ 2) :
    HasFDerivAt (fun X : RealSymmetricMatrixSpace ι =>
      (cfc f (symplecticHamiltonian Ω X)).trace.re)
      (hamiltonianSpectralDerivative Ω hΩ V hV d) V := by
  exact (hasFDerivAt_hermitianSpectralTrace_of_scalar_remainder
    (symmetricHamiltonian Ω hΩ V) f d hC hrem).comp V
      (hasFDerivAt_symmetricHamiltonian hΩ V hV)

end VacuumBellSeparation.Gaussian
