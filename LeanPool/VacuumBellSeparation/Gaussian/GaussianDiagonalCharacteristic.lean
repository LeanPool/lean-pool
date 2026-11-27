/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DensityCoherentFourier
public import LeanPool.VacuumBellSeparation.Gaussian.PhysicalGaussianHusimi

/-!
# Actual Gaussian coherent diagonal determines Gaussian characteristic

The proved coherent-frame Fourier identity recovers the actual Weyl
expectation from the actual Husimi density. A positive real precision
matrix is sufficient for the genuine matrix Fourier integral. The
physical covariance is the inverse precision minus half the identity,
with the displacement-label symplectic rotation kept explicit.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem physicalDisplacementCovariance_sub_scalar {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (c : ℝ) :
    physicalDisplacementCovariance (V - c • 1) = physicalDisplacementCovariance V - c • 1 := by
  simpa only [sub_eq_add_neg, neg_smul] using
    physicalDisplacementCovariance_add_scalar V (-c)

theorem physicalDisplacementCovariance_quadratic {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (u : Fin m × Fin 2 → ℝ) :
    (modeSymplecticForm *ᵥ u) ⬝ᵥ (V *ᵥ (modeSymplecticForm *ᵥ u)) =
      u ⬝ᵥ (physicalDisplacementCovariance V *ᵥ u) := by
  simpa only [Matrix.transpose_transpose, physicalDisplacementCovariance] using
    dotProduct_congruence modeSymplecticFormᵀ V u u

theorem coherentGaussian_phase_eq_fourier {m : ℕ}
    (P : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (z : MultiModePhaseSpace m) (w : Fin m → ℂ) :
    coherentFourierPhase z (WithLp.toLp 2 w) * (coherentMatrixGaussian P w : ℂ) =
      coherentMatrixFourier P (modeSymplecticForm *ᵥ complexRealCoordinates m
        (fun j => z j)) w := by
  rw [coherentFourierPhase, coherentMatrixGaussian, Complex.ofReal_exp,
    coherentMatrixFourier, ← Complex.exp_add, symplectic_rotated_dot_complexRealCoordinates]
  congr 1
  push_cast
  ring

theorem gaussianPhysical_characteristic_weight {m : ℕ}
    (P : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (z : Fin m → ℂ) :
    weylVacuumWeight m z * Complex.exp ((-(complexRealCoordinates m z ⬝ᵥ
      (physicalDisplacementCovariance (P⁻¹ - (1 / 2 : ℝ) • 1) *ᵥ
        complexRealCoordinates m z)) : ℝ) : ℂ) =
      Complex.exp ((-((modeSymplecticForm *ᵥ complexRealCoordinates m z) ⬝ᵥ
        (P⁻¹ *ᵥ (modeSymplecticForm *ᵥ complexRealCoordinates m z))) : ℝ) : ℂ) := by
  rw [weylVacuumWeight, ← Complex.exp_add, ← Complex.ofReal_add,
    physicalDisplacementCovariance_quadratic, physicalDisplacementCovariance_sub_scalar]
  congr 2
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, complexRealCoordinates_dot_self]
  ring

theorem densityExpectation_of_gaussian_coherentDiagonal {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {P : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hP : P.PosDef) (c : ℝ)
    (hdiag : ∀ w : Fin m → ℂ,
      multiCoherentPositiveDiagonal A w = c * coherentMatrixGaussian P w)
    (z : Fin m → ℂ) :
    densityExpectation (multiModeNumberBasis m) A (multiOscillatorWeyl (WithLp.toLp 2 z)) =
      ((c * Real.pi ^ m / Real.sqrt P.det : ℝ) : ℂ) *
        Complex.exp ((-(complexRealCoordinates m z ⬝ᵥ
          (physicalDisplacementCovariance (P⁻¹ - (1 / 2 : ℝ) • 1) *ᵥ
            complexRealCoordinates m z)) : ℝ) : ℂ) := by
  have h := integral_densityCoherentFourier hA (WithLp.toLp 2 z)
  have he (w : Fin m → ℂ) :
      coherentFourierPhase (WithLp.toLp 2 z) (WithLp.toLp 2 w) *
        (multiCoherentPositiveDiagonal A w : ℂ) =
      (c : ℂ) * coherentMatrixFourier P
        (modeSymplecticForm *ᵥ complexRealCoordinates m z) w := by
    rw [hdiag, Complex.ofReal_mul]
    calc
      _ = (c : ℂ) * (coherentFourierPhase (WithLp.toLp 2 z) (WithLp.toLp 2 w) *
        (coherentMatrixGaussian P w : ℂ)) := by ring
      _ = _ := by rw [coherentGaussian_phase_eq_fourier]
  simp_rw [he] at h
  rw [integral_const_mul, integral_coherentMatrixFourier hP] at h
  apply mul_left_cancel₀ (show weylVacuumWeight m z ≠ 0 from Complex.exp_ne_zero _)
  calc
    _ = (c : ℂ) * (((Real.pi ^ m / Real.sqrt P.det : ℝ) : ℂ) *
        Complex.exp ((-((modeSymplecticForm *ᵥ complexRealCoordinates m z) ⬝ᵥ
          (P⁻¹ *ᵥ (modeSymplecticForm *ᵥ complexRealCoordinates m z))) : ℝ) : ℂ)) := h.symm
    _ = _ := by
      rw [← gaussianPhysical_characteristic_weight]
      push_cast
      ring

/-- A normalized actual Gaussian coherent diagonal forces the actual
physical Gaussian characteristic, rather than serving as its definition. -/
theorem hasGaussianPhysicalCharacteristic_of_coherentDiagonal {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {P : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hP : P.PosDef)
    (hdiag : ∀ w : Fin m → ℂ,
      multiCoherentPositiveDiagonal A w =
        (Real.sqrt P.det / Real.pi ^ m) * coherentMatrixGaussian P w) :
    HasGaussianPhysicalCharacteristic A (P⁻¹ - (1 / 2 : ℝ) • 1) := by
  intro z
  have h := densityExpectation_of_gaussian_coherentDiagonal hA hP
    (Real.sqrt P.det / Real.pi ^ m) hdiag z
  have hc : (Real.sqrt P.det / Real.pi ^ m) * Real.pi ^ m / Real.sqrt P.det = 1 := by
    field_simp [show Real.pi ^ m ≠ 0 by positivity, ne_of_gt (Real.sqrt_pos.mpr hP.det_pos)]
  simpa only [hc, Complex.ofReal_one, one_mul] using h

end VacuumBellSeparation.Gaussian
