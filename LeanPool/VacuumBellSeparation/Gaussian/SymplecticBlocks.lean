/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WilliamsonOneMode

/-!
# Actual finite-mode symplectic and covariance block matrices

The phase-space indices are mode/quadrature pairs. The symplectic form is
literally `I ⊗ Ω₂`, with `Ω₂ = [[0,1],[-1,0]]`. Mode scalars are literal
diagonal matrices, and their positive square-root congruences are proved
entrywise. These are matrix identities, without a Williamson assumption.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Mode symplectic form. -/
def modeSymplecticForm : Matrix (ι × Fin 2) (ι × Fin 2) ℝ :=
  (1 : Matrix ι ι ℝ) ⊗ₖ oneModeSymplecticForm

/-- Mode diagonal given by `Matrix.diagonal (fun i => d i.1)`. -/
def modeDiagonal (d : ι → ℝ) : Matrix (ι × Fin 2) (ι × Fin 2) ℝ :=
  Matrix.diagonal (fun i => d i.1)

omit [Fintype ι] in
@[simp] theorem transpose_modeDiagonal (d : ι → ℝ) :
    (modeDiagonal d)ᵀ = modeDiagonal d := Matrix.diagonal_transpose _

omit [Fintype ι] in
@[simp] theorem modeDiagonal_one : modeDiagonal (fun _ : ι => 1) = 1 := rfl

@[simp] theorem modeDiagonal_mul (d e : ι → ℝ) :
    modeDiagonal d * modeDiagonal e = modeDiagonal (fun i => d i * e i) :=
  Matrix.diagonal_mul_diagonal _ _

omit [Fintype ι] in
@[simp] theorem transpose_modeSymplecticForm :
    (modeSymplecticForm (ι := ι))ᵀ = -modeSymplecticForm := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [modeSymplecticForm, oneModeSymplecticForm, Matrix.one_apply, eq_comm]

@[simp] theorem oneModeSymplecticForm_mul_self :
    oneModeSymplecticForm * oneModeSymplecticForm = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneModeSymplecticForm, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem modeSymplecticForm_mul_self :
    modeSymplecticForm (ι := ι) * modeSymplecticForm = -1 := by
  rw [modeSymplecticForm, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    oneModeSymplecticForm_mul_self]
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j <;> by_cases hab : a = b <;>
    simp [Prod.mk.injEq, hij, hab]

theorem modeDiagonal_commute_symplectic (d : ι → ℝ) :
    Commute (modeDiagonal d) modeSymplecticForm := by
  change modeDiagonal d * modeSymplecticForm = modeSymplecticForm * modeDiagonal d
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [modeDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
    modeSymplecticForm, Matrix.kronecker_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst j
    simp [mul_comm]
  · simp [h]

/-- Positive mode square roots multiply the symplectic blocks by the mode
frequencies, with the source's positive `Ω₂` orientation. -/
theorem modeSqrt_symplectic_congruence (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    modeDiagonal (fun i => Real.sqrt (d i)) * modeSymplecticForm *
      modeDiagonal (fun i => Real.sqrt (d i)) = modeDiagonal d * modeSymplecticForm := by
  let R := modeDiagonal (fun i => Real.sqrt (d i))
  have hcomm : Commute R modeSymplecticForm := modeDiagonal_commute_symplectic _
  calc
    R * modeSymplecticForm * R = R * R * modeSymplecticForm := by
      rw [mul_assoc, ← hcomm.eq, ← mul_assoc]
    _ = modeDiagonal d * modeSymplecticForm := by
      congr 1
      dsimp only [R]
      rw [modeDiagonal_mul]
      congr 1
      funext i
      exact Real.mul_self_sqrt (hd i)

/-- Reciprocal frequencies cancel the two positive square-root factors. -/
theorem modeSqrt_reciprocal_congruence (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    modeDiagonal (fun i => Real.sqrt (d i)) * modeDiagonal (fun i => (d i)⁻¹) *
      modeDiagonal (fun i => Real.sqrt (d i)) = 1 := by
  rw [modeDiagonal_mul, modeDiagonal_mul, ← modeDiagonal_one]
  congr 1
  funext i
  calc
    Real.sqrt (d i) * (d i)⁻¹ * Real.sqrt (d i) =
        (Real.sqrt (d i) * Real.sqrt (d i)) * (d i)⁻¹ := by ring
    _ = 1 := by rw [Real.mul_self_sqrt (hd i).le, mul_inv_cancel₀ (hd i).ne']

end VacuumBellSeparation.Gaussian
