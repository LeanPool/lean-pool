/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ModeHamiltonianAbsoluteValue

/-!
# Actual strict quantum uncertainty of faithful thermal mode matrices

The vacuum uncertainty matrix is a genuine Hermitian projection. Adding
the strictly positive diagonal excess proves quantum positivity directly,
without an assumed Gaussian representation or a spectral branch choice.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ}

/-- Canonical quantum form given by `(Complex.I / 2) • complexifyMatrix modeSymplecticForm`. -/
def canonicalQuantumForm (m : ℕ) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ :=
  (Complex.I / 2) • complexifyMatrix modeSymplecticForm

theorem canonicalQuantumForm_isHermitian : (canonicalQuantumForm m).IsHermitian := by
  change (canonicalQuantumForm m)ᴴ = canonicalQuantumForm m
  rw [canonicalQuantumForm, Matrix.conjTranspose_smul, ← complexifyMatrix_transpose,
    transpose_modeSymplecticForm, complexifyMatrix_neg]
  simp [neg_div, neg_smul]

theorem canonicalQuantumForm_square :
    canonicalQuantumForm m * canonicalQuantumForm m = (1 / 4 : ℂ) • 1 := by
  have hc : (Complex.I / 2) * (Complex.I / 2) = -(1 / 4 : ℂ) := by
    rw [div_mul_div_comm, Complex.I_mul_I]
    norm_num
  rw [canonicalQuantumForm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hc, ← complexifyMatrix_mul, modeSymplecticForm_mul_self,
    complexifyMatrix_neg, complexifyMatrix_one, smul_neg, neg_smul, neg_neg]

theorem vacuumQuantumProjection_posSemidef :
    ((1 / 2 : ℂ) • (1 : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ) +
      canonicalQuantumForm m).PosSemidef := by
  let P := (1 / 2 : ℂ) • (1 : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ) +
    canonicalQuantumForm m
  have hs : Pᴴ = P := by
    dsimp only [P]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, canonicalQuantumForm_isHermitian.eq]
    norm_num
  have hp : P * P = P := by
    dsimp only [P]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, canonicalQuantumForm_square]
    module
  have h := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [hs, hp] at h

theorem quantum_mode_posDef {ν : Fin m → ℝ} (hν : ∀ j, (1 : ℝ) / 2 < ν j) :
    (quantumCovariance (modeDiagonal ν) modeSymplecticForm).PosDef := by
  have hE := complexifyMatrix_posDef
    (modeDiagonal_posDef (fun j => sub_pos.mpr (hν j)))
  have he : quantumCovariance (modeDiagonal ν) modeSymplecticForm =
      complexifyMatrix (modeDiagonal (fun j => ν j - 1 / 2)) +
        ((1 / 2 : ℂ) • 1 + canonicalQuantumForm m) := by
    rw [quantumCovariance, canonicalQuantumForm, complexifyMatrix_modeDiagonal,
      complexifyMatrix_modeDiagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
      ring
    · simp [hij]
  rw [he]
  exact hE.add_posSemidef vacuumQuantumProjection_posSemidef

theorem thermalPowerCovariance_quantum_posDef {q : Fin m → ℝ} {a : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (ha : 0 < a) :
    (quantumCovariance (thermalPowerCovariance q a) modeSymplecticForm).PosDef :=
  quantum_mode_posDef fun j => half_lt_thermalQuadratureVariance
    (Real.rpow_pos_of_pos (hq₀ j) a) (Real.rpow_lt_one (hq₀ j).le (hq₁ j) ha)

end VacuumBellSeparation.Gaussian
