/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ComplexMatrixPositivity
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPerturbationMultiplier

/-!
# The actual absolute symplectic Hamiltonian in Williamson coordinates

For the literal canonical form Ω, H=iDΩ has absolute value D whenever
the mode variances are nonnegative. Actual CFC composition therefore
evaluates every even scalar trace as twice the sum over mode variances.
No signed eigenvector enumeration or simplicity assumption is needed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {m : ℕ}

/-- Mode Hamiltonian given by `Complex.I • complexifyMatrix (modeDiagonal ν *
modeSymplecticForm)`. -/
def modeHamiltonian (ν : Fin m → ℝ) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ :=
  Complex.I • complexifyMatrix (modeDiagonal ν * modeSymplecticForm)

theorem complexifyMatrix_modeDiagonal (ν : Fin m → ℝ) :
    complexifyMatrix (modeDiagonal ν) = Matrix.diagonal (fun i : Fin m × Fin 2 => (ν i.1 : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [complexifyMatrix, modeDiagonal]
  · simp [complexifyMatrix, modeDiagonal, h]

theorem symplecticHamiltonian_modeDiagonal {ν : Fin m → ℝ} (hν : ∀ i, 0 ≤ ν i) :
    symplecticHamiltonian modeSymplecticForm (modeDiagonal ν) = modeHamiltonian ν := by
  rw [symplecticHamiltonian, modeDiagonal_sqrt hν, modeSqrt_symplectic_congruence ν hν]
  rfl

theorem modeHamiltonian_isHermitian {ν : Fin m → ℝ} (hν : ∀ i, 0 ≤ ν i) :
    (modeHamiltonian ν).IsHermitian := by
  rw [← symplecticHamiltonian_modeDiagonal hν]
  exact symplecticHamiltonian_isHermitian transpose_modeSymplecticForm _

theorem modeHamiltonian_square (ν : Fin m → ℝ) :
    modeHamiltonian ν * modeHamiltonian ν =
      complexifyMatrix (modeDiagonal ν) * complexifyMatrix (modeDiagonal ν) := by
  have hK : (modeDiagonal ν * modeSymplecticForm) *
      (modeDiagonal ν * modeSymplecticForm) = -(modeDiagonal ν * modeDiagonal ν) := by
    calc
      _ = modeDiagonal ν * (modeSymplecticForm * modeDiagonal ν) * modeSymplecticForm := by
        noncomm_ring
      _ = modeDiagonal ν * (modeDiagonal ν * modeSymplecticForm) * modeSymplecticForm := by
        rw [← (modeDiagonal_commute_symplectic ν).eq]
      _ = modeDiagonal ν * modeDiagonal ν * (modeSymplecticForm * modeSymplecticForm) := by
        noncomm_ring
      _ = _ := by rw [modeSymplecticForm_mul_self, Matrix.mul_neg, Matrix.mul_one]
  rw [modeHamiltonian, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I,
    neg_one_smul, ← complexifyMatrix_mul, hK, complexifyMatrix_neg, neg_neg,
    complexifyMatrix_mul]

/-- The absolute value is the genuine positive CFC square root of H†H. -/
theorem abs_modeHamiltonian {ν : Fin m → ℝ} (hν : ∀ i, 0 ≤ ν i) :
    CFC.abs (modeHamiltonian ν) = complexifyMatrix (modeDiagonal ν) := by
  have hD : (complexifyMatrix (modeDiagonal ν)).PosSemidef :=
    complexifyMatrix_posSemidef (Matrix.PosSemidef.diagonal (fun i => hν i.1))
  rw [CFC.abs, (modeHamiltonian_isHermitian hν).isSelfAdjoint.star_eq,
    modeHamiltonian_square, CFC.sqrt_mul_self _ hD.nonneg]

theorem real_trace_even_modeHamiltonian {ν : Fin m → ℝ} (hν : ∀ i, 0 ≤ ν i) (f : ℝ → ℝ) :
    (cfc (fun x : ℝ => f |x|) (modeHamiltonian ν)).trace.re = 2 * ∑ i, f (ν i) := by
  rw [cfc_complex_abs_composition (modeHamiltonian_isHermitian hν) f,
    abs_modeHamiltonian hν, complexifyMatrix_modeDiagonal, cfc_complex_real_diagonal,
    Matrix.trace_diagonal, Complex.re_sum]
  simp only [Complex.ofReal_re, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [Finset.sum_add_distrib]
  ring

end VacuumBellSeparation.Gaussian
