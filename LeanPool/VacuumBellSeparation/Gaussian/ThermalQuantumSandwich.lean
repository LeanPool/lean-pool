/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ComplexMatrixInverseOrder
public import LeanPool.VacuumBellSeparation.Gaussian.QuantumModePositivity
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalCovariancePerturbation

/-!
# Strict uncertainty of the actual Appendix A sandwich covariance

The thermal calibration L(T+iΩ/2)⁻¹L=T−iΩ/2 and strict complex
inverse order show that quantum positivity is preserved exactly on the
positive covariance-gap domain. The variable covariance need not commute
with the thermal reference. This proves the endpoint condition required
by the genuine aggregate purity segment estimate.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}

theorem complexifyMatrix_sub {n : Type*}
    (A B : Matrix n n ℝ) :
    complexifyMatrix (A - B) = complexifyMatrix A - complexifyMatrix B := by
  rw [sub_eq_add_neg, complexifyMatrix_add, complexifyMatrix_neg, sub_eq_add_neg]

theorem complexifyMatrix_inv {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : IsUnit A) :
    complexifyMatrix A⁻¹ = (complexifyMatrix A)⁻¹ := by
  have h := congrArg complexifyMatrix
    (A.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det A).mp hA))
  rw [complexifyMatrix_mul, complexifyMatrix_one] at h
  have hi := (complexifyMatrix A).nonsing_inv_mul
    ((Matrix.isUnit_iff_isUnit_det _).mp (complexifyMatrix_isUnit hA))
  have hh := congrArg (fun X => (complexifyMatrix A)⁻¹ * X) h
  simpa only [← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_one] using hh

theorem complex_mode_commute_quantumForm (ν : Fin m → ℝ) :
    complexifyMatrix (modeDiagonal ν) * canonicalQuantumForm m =
      canonicalQuantumForm m * complexifyMatrix (modeDiagonal ν) := by
  rw [canonicalQuantumForm, Matrix.mul_smul, Matrix.smul_mul,
    ← complexifyMatrix_mul, ← complexifyMatrix_mul, (modeDiagonal_commute_symplectic ν).eq]

theorem thermal_quantum_inverse_calibration
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    complexifyMatrix (thermalWoodburyFactor q τ) *
        (quantumCovariance (thermalPowerCovariance q τ) modeSymplecticForm)⁻¹ *
          complexifyMatrix (thermalWoodburyFactor q τ) =
      complexifyMatrix (thermalPowerCovariance q τ) - canonicalQuantumForm m := by
  let T := complexifyMatrix (thermalPowerCovariance q τ)
  let L := complexifyMatrix (thermalWoodburyFactor q τ)
  let J := canonicalQuantumForm m
  have hC : (T + J).PosDef := thermalPowerCovariance_quantum_posDef hq₀ hq₁ hτ
  have hTJ : T * J = J * T := complex_mode_commute_quantumForm _
  have hLJ : L * J = J * L := complex_mode_commute_quantumForm _
  have hTL : T * L = L * T := by
    dsimp only [T, L, thermalPowerCovariance, thermalWoodburyFactor]
    rw [← complexifyMatrix_mul, ← complexifyMatrix_mul, modeDiagonal_mul, modeDiagonal_mul]
    congr 2
    funext j
    ring
  have hcomm : (T + J) * L = L * (T + J) := by
    rw [Matrix.add_mul, Matrix.mul_add, hTL, ← hLJ]
  have hs : L * L = T * T - (1 / 4 : ℂ) • 1 := by
    dsimp only [L, T]
    rw [← complexifyMatrix_mul, thermalWoodburyFactor_sq hq₀ hq₁ hτ,
      complexifyMatrix_sub, pow_two, complexifyMatrix_mul]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [complexifyMatrix, hij]
  have hsq : L * L = (T + J) * (T - J) := by
    rw [hs]
    have hJJ : J * J = (1 / 4 : ℂ) • 1 := canonicalQuantumForm_square
    rw [← hJJ]
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, ← hTJ]
    abel
  exact complex_matrix_inverse_calibration hC.isUnit hcomm hsq

/-- Actual quantum uncertainty is equivalent before and after the
thermal sandwich whenever the actual covariance gap is positive. -/
theorem thermalSandwichCovariance_quantum_posDef_iff
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hgap : (thermalPowerCovariance q τ - V).PosDef) :
    (quantumCovariance (thermalSandwichCovariance q τ V) modeSymplecticForm).PosDef ↔
      (quantumCovariance V modeSymplecticForm).PosDef := by
  have hD := complexifyMatrix_posDef hgap
  have hC := thermalPowerCovariance_quantum_posDef hq₀ hq₁ hτ
  have hL := complexifyMatrix_posDef (thermalWoodburyFactor_posDef hq₀ hq₁ hτ)
  have h := complex_matrix_congruence_inverse_gap_iff hD hC hL
    (thermal_quantum_inverse_calibration hq₀ hq₁ hτ)
  have hleft : complexifyMatrix (thermalWoodburyFactor q τ) *
      (complexifyMatrix (thermalPowerCovariance q τ - V))⁻¹ *
      complexifyMatrix (thermalWoodburyFactor q τ) -
        (complexifyMatrix (thermalPowerCovariance q τ) - canonicalQuantumForm m) =
      quantumCovariance (thermalSandwichCovariance q τ V) modeSymplecticForm := by
    rw [quantumCovariance, thermalSandwichCovariance, complexifyMatrix_add,
      complexifyMatrix_neg, complexifyMatrix_mul, complexifyMatrix_mul,
      complexifyMatrix_inv hgap.isUnit]
    change _ = -complexifyMatrix (thermalPowerCovariance q τ) + _ + canonicalQuantumForm m
    abel
  have hright : quantumCovariance (thermalPowerCovariance q τ) modeSymplecticForm -
      complexifyMatrix (thermalPowerCovariance q τ - V) = quantumCovariance V modeSymplecticForm
        := by
    rw [quantumCovariance, quantumCovariance, complexifyMatrix_sub]
    abel
  rwa [hleft, hright] at h

end VacuumBellSeparation.Gaussian
