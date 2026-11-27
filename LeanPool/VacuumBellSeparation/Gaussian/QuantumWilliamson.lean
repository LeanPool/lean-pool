/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.QuantumCovarianceDefs
public import LeanPool.VacuumBellSeparation.Gaussian.WilliamsonFinite

/-!
# Quantum uncertainty bounds the actual Williamson eigenvalues

The uncertainty matrix is literally the complex matrix `V + i Ω / 2`.
Its positivity is transported through the actual inverse Williamson
coordinates, and the vector `(1,i)` in each genuine two-dimensional mode
shows `ν ≥ 1/2`. Thus the lower bound is proved from quantum uncertainty,
not added to the real Williamson theorem as an assumption or a field.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {ι κ η : Type*}

@[simp] theorem complexifyMatrix_apply (M : Matrix ι κ ℝ) (i : ι) (j : κ) :
    complexifyMatrix M i j = (M i j : ℂ) := rfl

@[simp] theorem complexifyMatrix_mul [Fintype κ] (M : Matrix ι κ ℝ) (N : Matrix κ η ℝ) :
    complexifyMatrix (M * N) = complexifyMatrix M * complexifyMatrix N := Matrix.map_mul

@[simp] theorem complexifyMatrix_transpose (M : Matrix ι κ ℝ) :
    complexifyMatrix Mᵀ = (complexifyMatrix M)ᴴ := by
  ext i j
  simp [complexifyMatrix, Matrix.conjTranspose_apply]

theorem quantumCovariance_congruence [Fintype ι] (V Ω : Matrix ι ι ℝ) (T : Matrix κ ι ℝ) :
    quantumCovariance (T * V * Tᵀ) (T * Ω * Tᵀ) =
      complexifyMatrix T * quantumCovariance V Ω * (complexifyMatrix T)ᴴ := by
  simp only [quantumCovariance, complexifyMatrix_mul, complexifyMatrix_transpose,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem quantumModeBlock [DecidableEq ι] (ν : ι → ℝ) (i : ι) :
    (quantumCovariance (modeDiagonal ν) modeSymplecticForm).submatrix
      (fun a : Fin 2 => (i, a)) (fun a : Fin 2 => (i, a)) =
      !![(ν i : ℂ), Complex.I / 2; -(Complex.I / 2), (ν i : ℂ)] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [quantumCovariance, Matrix.submatrix_apply, modeDiagonal,
      modeSymplecticForm, oneModeSymplecticForm]

/-- The literal uncertainty matrix in mode coordinates forces every
symplectic eigenvalue to be at least the vacuum value. -/
theorem half_le_of_quantum_mode_posSemidef [DecidableEq ι] (ν : ι → ℝ)
    (h : (quantumCovariance (modeDiagonal ν) modeSymplecticForm).PosSemidef) :
    ∀ i, (1 : ℝ) / 2 ≤ ν i := by
  intro i
  have hblock := h.submatrix (fun a : Fin 2 => (i, a))
  rw [quantumModeBlock] at hblock
  have ht := hblock.dotProduct_mulVec_nonneg (![1, Complex.I] : Fin 2 → ℂ)
  have hr := (Complex.nonneg_iff.mp ht).1
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] at hr
  linarith

/-- Actual Williamson eigenvalues satisfy the quantum uncertainty bound
when the literal covariance uncertainty matrix is positive semidefinite. -/
theorem exists_quantum_williamson_factorization [Fintype ι] [DecidableEq ι] (V Ω : Matrix ι ι ℝ)
    (hV : V.PosDef) (hΩ : Ωᵀ = -Ω) (hΩunit : IsUnit Ω)
    (hquantum : (quantumCovariance V Ω).PosSemidef) :
    ∃ (m : ℕ) (ν : Fin m → ℝ)
      (S : Matrix ι (Fin m × Fin 2) ℝ) (T : Matrix (Fin m × Fin 2) ι ℝ),
      Fintype.card ι = 2 * m ∧ (∀ i, (1 : ℝ) / 2 ≤ ν i) ∧
      S * T = 1 ∧ T * S = 1 ∧
      S * (modeSymplecticForm (ι := Fin m)) * Sᵀ = Ω ∧ S * modeDiagonal ν * Sᵀ = V := by
  obtain ⟨m, ν, S, T, hcard, hν, hST, hTS, hsymp, hcov⟩ :=
    exists_williamson_factorization V Ω hV hΩ hΩunit
  have hinv_cov : T * V * Tᵀ = modeDiagonal ν := by
    calc
      T * V * Tᵀ = (T * S) * modeDiagonal ν * (T * S)ᵀ := by
        rw [← hcov]
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = modeDiagonal ν := by simp only [hTS, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hinv_symp : T * Ω * Tᵀ = modeSymplecticForm := by
    calc
      T * Ω * Tᵀ = (T * S) * modeSymplecticForm * (T * S)ᵀ := by
        rw [← hsymp]
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = modeSymplecticForm := by
        simp only [hTS, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hnormal : (quantumCovariance (modeDiagonal ν) modeSymplecticForm).PosSemidef := by
    have h := hquantum.mul_mul_conjTranspose_same (complexifyMatrix T)
    rw [← quantumCovariance_congruence, hinv_cov, hinv_symp] at h
    exact h
  exact ⟨m, ν, S, T, hcard, half_le_of_quantum_mode_posSemidef ν hnormal,
    hST, hTS, hsymp, hcov⟩

end VacuumBellSeparation.Gaussian
