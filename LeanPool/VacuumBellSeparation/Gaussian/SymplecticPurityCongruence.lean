/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ModePurityDifferential

/-!
# Actual purity invariance under fixed symplectic congruence

The positive-root normalized congruence is an actual orthogonal matrix.
It conjugates the actual Hermitian Hamiltonians for V and S V Sᵀ, so all
even spectral traces, in particular the actual Gaussian purity value,
are invariant. The congruence also acts as a genuine continuous linear
map on the real symmetric subspace.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix Filter
open scoped MatrixOrder Matrix.Norms.L2Operator Topology

variable {m : ℕ}

/-- Symmetric congruence continuous linear map of type `RealSymmetricMatrixSpace (Fin m × Fin 2)
→L[ℝ] RealSymmetricMatrixSpace (Fin m × Fin 2)`. -/
def symmetricCongruenceCLM
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    RealSymmetricMatrixSpace (Fin m × Fin 2) →L[ℝ]
      RealSymmetricMatrixSpace (Fin m × Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ⟨S * (X : Matrix _ _ ℝ) * Sᵀ, by
        change IsSelfAdjoint (S * (X : Matrix _ _ ℝ) * Sᵀ)
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
          (Matrix.isHermitian_mul_mul_conjTranspose S
            (realSymmetricMatrix_isHermitian X)).isSelfAdjoint⟩
      map_add' := by intro X Y; apply Subtype.ext; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; apply Subtype.ext; simp [] }

@[simp] theorem symmetricCongruenceCLM_apply
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (X : RealSymmetricMatrixSpace (Fin m × Fin 2)) :
    ((symmetricCongruenceCLM S X : RealSymmetricMatrixSpace (Fin m × Fin 2)) :
      Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) = S * (X : Matrix _ _ ℝ) * Sᵀ := rfl

theorem canonical_symplectic_congruence_posDef
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.PosDef) :
    (S * V * Sᵀ).PosDef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hV.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_isUnit (canonical_symplectic_isUnit S hS))

/-- Symplectic Hamiltonian congruence unitary. -/
def symplecticHamiltonianCongruenceUnitary
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.PosDef) :
    unitary (Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ) :=
  orthogonalComplexUnitary (relativeCongruenceOrthogonal S V)
    (relativeCongruenceOrthogonal_transpose_mul S hV
      (canonical_symplectic_congruence_posDef S hS hV))

theorem symplecticHamiltonian_real_congruence
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.PosDef) :
    (relativeCongruenceOrthogonal S V)ᵀ *
      (CFC.sqrt (S * V * Sᵀ) * modeSymplecticForm * CFC.sqrt (S * V * Sᵀ)) *
        relativeCongruenceOrthogonal S V = CFC.sqrt V * modeSymplecticForm * CFC.sqrt V := by
  let R := CFC.sqrt V
  let Q := CFC.sqrt (S * V * Sᵀ)
  have hR := matrix_sqrt_posDef hV
  have hQ := matrix_sqrt_posDef (canonical_symplectic_congruence_posDef S hS hV)
  have hRt : Rᵀ = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  have hQit : (Q⁻¹)ᵀ = Q⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.inv.isHermitian.eq
  have hQdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
  have hQiQ : Q⁻¹ * Q = 1 := Q.nonsing_inv_mul hQdet
  have hQQi : Q * Q⁻¹ = 1 := Q.mul_nonsing_inv hQdet
  change (Q⁻¹ * S * R)ᵀ * (Q * modeSymplecticForm * Q) * (Q⁻¹ * S * R) = _
  simp only [Matrix.transpose_mul, hRt, hQit]
  calc
    _ = R * Sᵀ * (Q⁻¹ * Q) * modeSymplecticForm * (Q * Q⁻¹) * S * R := by noncomm_ring
    _ = R * (Sᵀ * modeSymplecticForm * S) * R := by
      rw [hQiQ, hQQi, Matrix.mul_one, Matrix.mul_one]
      noncomm_ring
    _ = _ := by rw [canonical_symplectic_transpose_congruence S hS]

theorem symplecticHamiltonian_congruence
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.PosDef) :
    symplecticHamiltonian modeSymplecticForm (S * V * Sᵀ) =
      (symplecticHamiltonianCongruenceUnitary S hS hV : Matrix _ _ ℂ) *
        symplecticHamiltonian modeSymplecticForm V *
          (symplecticHamiltonianCongruenceUnitary S hS hV : Matrix _ _ ℂ)ᴴ := by
  let U := symplecticHamiltonianCongruenceUnitary S hS hV
  let H := symplecticHamiltonian modeSymplecticForm (S * V * Sᵀ)
  have hn : (U : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ)ᴴ * H *
      (U : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ) =
        symplecticHamiltonian modeSymplecticForm V := by
    change (complexifyMatrix (relativeCongruenceOrthogonal S V))ᴴ * _ *
      complexifyMatrix (relativeCongruenceOrthogonal S V) = _
    dsimp only [H]
    rw [symplecticHamiltonian, Matrix.mul_smul, Matrix.smul_mul,
      ← complexifyMatrix_transpose, ← complexifyMatrix_mul, ← complexifyMatrix_mul,
      symplecticHamiltonian_real_congruence S hS hV]
    rfl
  have hUU : (U : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ) *
      (U : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ)ᴴ = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self U
  calc
    H = ((U : Matrix _ _ ℂ) * (U : Matrix _ _ ℂ)ᴴ) * H *
        ((U : Matrix _ _ ℂ) * (U : Matrix _ _ ℂ)ᴴ) := by
      rw [hUU, Matrix.one_mul, Matrix.mul_one]
    _ = (U : Matrix _ _ ℂ) * ((U : Matrix _ _ ℂ)ᴴ * H *
        (U : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ)) * (U : Matrix _ _ ℂ)ᴴ := by
      noncomm_ring
    _ = _ := by rw [hn]

theorem covariancePurityTrace_symplectic_congruence (r : ℝ)
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.PosDef) :
    covariancePurityTrace r (S * V * Sᵀ) = covariancePurityTrace r V := by
  rw [covariancePurityTrace, symplecticHamiltonian_congruence S hS hV,
    real_trace_cfc_unitary_conjugate _
      (symplecticHamiltonian_isHermitian transpose_modeSymplecticForm V)]
  rfl

theorem covariancePurityTrace_symplectic_congruence_eventually (r : ℝ)
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    (V : RealSymmetricMatrixSpace (Fin m × Fin 2))
    (hV : (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ).PosDef) :
    ∀ᶠ X : RealSymmetricMatrixSpace (Fin m × Fin 2) in 𝓝 V,
      covariancePurityTrace r
        (symmetricCongruenceCLM S X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) =
      covariancePurityTrace r (X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) := by
  filter_upwards [eventually_posDef_at_positive_symmetric V hV] with X hX
  change covariancePurityTrace r (S * (X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) * Sᵀ) =
    covariancePurityTrace r (X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
  exact covariancePurityTrace_symplectic_congruence r S hS hX

end VacuumBellSeparation.Gaussian
