/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# Constructive Williamson normal form for one real mode

For a real positive-definite `2×2` covariance matrix `V`, set
`ν=√det(V)` and `S=(√ν)⁻¹ √V`, using the genuine matrix functional calculus.
The resulting matrix has determinant one, preserves the canonical
symplectic form, and satisfies `V=S (νI) Sᵀ`. This proves the real matrix
normal form in one mode, without assuming a symplectic diagonalization.
Oscillator unitary implementation and the multimode theorem are separate.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- One mode symplectic form. -/
def oneModeSymplecticForm : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- In two real dimensions the alternating form transforms by determinant. -/
theorem matrix_two_symplectic_congruence (S : Matrix (Fin 2) (Fin 2) ℝ) :
    S * oneModeSymplecticForm * Sᵀ = S.det • oneModeSymplecticForm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneModeSymplecticForm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.det_fin_two] <;> ring

/-- One mode symplectic eigenvalue obtained from `Real.sqrt`. -/
noncomputable def oneModeSymplecticEigenvalue (V : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Real.sqrt V.det

/-- One mode Williamson matrix. -/
noncomputable def oneModeWilliamsonMatrix (V : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt (oneModeSymplecticEigenvalue V))⁻¹ • CFC.sqrt V

theorem oneModeSymplecticEigenvalue_pos {V : Matrix (Fin 2) (Fin 2) ℝ}
    (hV : V.PosDef) : 0 < oneModeSymplecticEigenvalue V :=
  Real.sqrt_pos.mpr hV.det_pos

theorem oneModeWilliamson_scale_sq {V : Matrix (Fin 2) (Fin 2) ℝ}
    (hV : V.PosDef) :
    (Real.sqrt (oneModeSymplecticEigenvalue V))⁻¹ *
      (Real.sqrt (oneModeSymplecticEigenvalue V))⁻¹ *
        oneModeSymplecticEigenvalue V = 1 := by
  have hν := oneModeSymplecticEigenvalue_pos hV
  rw [← mul_inv, Real.mul_self_sqrt hν.le, inv_mul_cancel₀ hν.ne']

theorem det_oneModeWilliamsonMatrix {V : Matrix (Fin 2) (Fin 2) ℝ}
    (hV : V.PosDef) : (oneModeWilliamsonMatrix V).det = 1 := by
  rw [oneModeWilliamsonMatrix, Matrix.det_smul, hV.posSemidef.det_sqrt,
    RCLike.sqrt_real]
  change (Real.sqrt (oneModeSymplecticEigenvalue V))⁻¹ ^ 2 *
    oneModeSymplecticEigenvalue V = 1
  rw [pow_two, oneModeWilliamson_scale_sq hV]

theorem oneModeWilliamsonMatrix_symplectic {V : Matrix (Fin 2) (Fin 2) ℝ}
    (hV : V.PosDef) :
    oneModeWilliamsonMatrix V * oneModeSymplecticForm * (oneModeWilliamsonMatrix V)ᵀ =
      oneModeSymplecticForm := by
  rw [matrix_two_symplectic_congruence, det_oneModeWilliamsonMatrix hV, one_smul]

theorem oneModeWilliamsonMatrix_factorization {V : Matrix (Fin 2) (Fin 2) ℝ}
    (hV : V.PosDef) :
    oneModeWilliamsonMatrix V * (oneModeSymplecticEigenvalue V • 1) *
      (oneModeWilliamsonMatrix V)ᵀ = V := by
  have hroot : (CFC.sqrt V)ᵀ = CFC.sqrt V := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg V).isSelfAdjoint.star_eq
  have hscale := oneModeWilliamson_scale_sq hV
  rw [oneModeWilliamsonMatrix, Matrix.transpose_smul, hroot]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  rw [← pow_two, CFC.sq_sqrt V hV.posSemidef.nonneg]
  convert (one_smul ℝ V) using 1
  congr 1
  nlinarith [hscale]

/-- Actual one-mode Williamson existence, with all normal-form identities
proved for the explicitly constructed matrix. -/
theorem exists_oneModeWilliamson {V : Matrix (Fin 2) (Fin 2) ℝ} (hV : V.PosDef) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ S : Matrix (Fin 2) (Fin 2) ℝ,
      S * oneModeSymplecticForm * Sᵀ = oneModeSymplecticForm ∧
      S * (ν • 1) * Sᵀ = V ∧ ν = Real.sqrt V.det := by
  exact ⟨oneModeSymplecticEigenvalue V, oneModeSymplecticEigenvalue_pos hV,
    oneModeWilliamsonMatrix V, oneModeWilliamsonMatrix_symplectic hV,
    oneModeWilliamsonMatrix_factorization hV, rfl⟩

end VacuumBellSeparation.Gaussian
