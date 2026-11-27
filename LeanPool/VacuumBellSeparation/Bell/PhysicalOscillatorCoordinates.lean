/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.RealCoordinateWeyl
public import LeanPool.VacuumBellSeparation.Gaussian.PhysicalGaussianHusimi

/-!
# Oscillator labels with the literal physical covariance convention

The raw real displacement is Ωᵀx/√2. This rotation and scale give both
the source Weyl phase exp(-i xᵀΩy/2) and the source characteristic
exp(-xᵀVx/2) for the existing physical Gaussian density convention.
The label map is a genuine real linear equivalence for every mode count.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian Matrix

/-- Linear equivalence for the physical oscillator label, of type `(Fin n × Fin 2 → ℝ) ≃ₗ[ℝ]
MultiModePhaseSpace n where toFun x`. -/
noncomputable def physicalOscillatorLabel (n : ℕ) :
    (Fin n × Fin 2 → ℝ) ≃ₗ[ℝ] MultiModePhaseSpace n where
  toFun x := (complexRealLinearEquiv n).symm
    ((Real.sqrt 2)⁻¹ • (modeSymplecticFormᵀ *ᵥ x))
  invFun z := Real.sqrt 2 • (modeSymplecticForm *ᵥ complexRealLinearEquiv n z)
  left_inv x := by
    have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    simp only [LinearEquiv.apply_symm_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      modeSymplecticForm_mul_transpose, Matrix.one_mulVec, smul_smul,
      mul_inv_cancel₀ hn, one_smul]
  right_inv z := by
    have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      modeSymplecticForm_transpose_mul, Matrix.one_mulVec, smul_smul,
      inv_mul_cancel₀ hn, one_smul, LinearEquiv.symm_apply_apply]
  map_add' x y := by simp only [Matrix.mulVec_add, smul_add, map_add]
  map_smul' a x := by simp only [Matrix.mulVec_smul, smul_comm _ a, map_smul, RingHom.id_apply]

theorem physicalOscillatorLabel_realCoordinates {n : ℕ} (x : Fin n × Fin 2 → ℝ) :
    complexRealLinearEquiv n (physicalOscillatorLabel n x) =
      (Real.sqrt 2)⁻¹ • (modeSymplecticFormᵀ *ᵥ x) :=
  (complexRealLinearEquiv n).apply_symm_apply _

theorem sqrt_two_inv_mul_self : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem physicalOscillatorLabel_symplectic {n : ℕ} (x y : Fin n × Fin 2 → ℝ) :
    (Real.sqrt 2)⁻¹ • (modeSymplecticFormᵀ *ᵥ x) ⬝ᵥ
      (modeSymplecticForm *ᵥ ((Real.sqrt 2)⁻¹ • (modeSymplecticFormᵀ *ᵥ y))) =
        x ⬝ᵥ (modeSymplecticForm *ᵥ y) / 2 := by
  rw [real_bilinear_smul, sqrt_two_inv_mul_self, dotProduct_congruence,
    Matrix.mul_assoc, modeSymplecticForm_mul_transpose, Matrix.mul_one]
  ring

theorem physicalOscillatorLabel_covariance {n : ℕ}
    (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (x y : Fin n × Fin 2 → ℝ) :
    (Real.sqrt 2)⁻¹ • (modeSymplecticFormᵀ *ᵥ x) ⬝ᵥ
      (physicalDisplacementCovariance V *ᵥ
        ((Real.sqrt 2)⁻¹ • (modeSymplecticFormᵀ *ᵥ y))) =
          x ⬝ᵥ (V *ᵥ y) / 2 := by
  have hrot : modeSymplecticForm * physicalDisplacementCovariance V * modeSymplecticFormᵀ = V := by
    unfold physicalDisplacementCovariance
    calc
      _ = (modeSymplecticForm * modeSymplecticFormᵀ) * V *
          (modeSymplecticForm * modeSymplecticFormᵀ) := by noncomm_ring
      _ = V := by rw [modeSymplecticForm_mul_transpose, Matrix.one_mul, Matrix.mul_one]
  rw [real_bilinear_smul, sqrt_two_inv_mul_self, dotProduct_congruence, hrot]
  ring

/-- Continuous linear map for the physical oscillator Weyl, of type `MultiModeOscillatorSpace n
→L[ℂ] MultiModeOscillatorSpace n`. -/
noncomputable def physicalOscillatorWeyl {n : ℕ} (x : Fin n × Fin 2 → ℝ) :
    MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n :=
  multiOscillatorWeyl (physicalOscillatorLabel n x)

theorem physicalOscillatorWeyl_zero (n : ℕ) :
    physicalOscillatorWeyl (0 : Fin n × Fin 2 → ℝ) = 1 := by
  rw [physicalOscillatorWeyl, map_zero, multiOscillatorWeyl_zero]

theorem physicalOscillatorWeyl_star {n : ℕ} (x : Fin n × Fin 2 → ℝ) :
    star (physicalOscillatorWeyl x) = physicalOscillatorWeyl (-x) := by
  simp only [physicalOscillatorWeyl, ContinuousLinearMap.star_eq_adjoint,
    multiOscillatorWeyl_adjoint, map_neg]

theorem physicalOscillatorWeyl_mul {n : ℕ} (x y : Fin n × Fin 2 → ℝ) :
    physicalOscillatorWeyl x * physicalOscillatorWeyl y =
      Complex.exp (-(Complex.I * ((x ⬝ᵥ (modeSymplecticForm *ᵥ y) / 2 : ℝ) : ℂ))) •
        physicalOscillatorWeyl (x + y) := by
  rw [physicalOscillatorWeyl, physicalOscillatorWeyl, multiOscillatorWeyl_mul,
    weylPhase, inner_im_eq_real_symplectic]
  simp only [id_eq]
  rw [physicalOscillatorLabel_realCoordinates, physicalOscillatorLabel_realCoordinates,
    physicalOscillatorLabel_symplectic]
  simp only [physicalOscillatorWeyl, map_add]

theorem range_physicalOscillatorWeyl (n : ℕ) :
    Set.range (physicalOscillatorWeyl (n := n)) =
      Set.range (multiOscillatorWeyl (m := n)) := by
  exact (physicalOscillatorLabel n).surjective.range_comp multiOscillatorWeyl

/-- The physical Gaussian convention agrees with the literal source covariance. -/
theorem gaussianPhysical_physicalOscillatorWeyl {n : ℕ}
    {A : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n}
    {V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic A V) (x : Fin n × Fin 2 → ℝ) :
    densityExpectation (multiModeNumberBasis n) A (physicalOscillatorWeyl x) =
      ((Real.exp (-(x ⬝ᵥ (V *ᵥ x) / 2)) : ℝ) : ℂ) := by
  change densityExpectation (multiModeNumberBasis n) A
    (realCoordinateWeyl ((Real.sqrt 2)⁻¹ • (modeSymplecticFormᵀ *ᵥ x))) = _
  rw [gaussianDisplacement_realCoordinateWeyl hG, physicalOscillatorLabel_covariance,
    Complex.ofReal_exp]

end VacuumBellSeparation
