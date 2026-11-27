/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianHusimi

/-!
# Literal physical covariance and the manuscript Husimi formula

Displacement D((x+iy)/sqrt2) equals exp(i(yQ-xP)). Its characteristic
covariance is Ωᵀ V Ω when V is the physical (Q,P) covariance. The actual
orthogonal symplectic rotation is proved and cancels from the derived
Husimi inverse quadratic form. The resulting formula uses the source
coherent coordinates u=(Re z,Im z), equivalently r=sqrt2 u.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem modeSymplecticForm_transpose_mul {m : ℕ} :
    (modeSymplecticForm (ι := Fin m))ᵀ * modeSymplecticForm = 1 := by
  rw [transpose_modeSymplecticForm, neg_mul, modeSymplecticForm_mul_self, neg_neg]

theorem modeSymplecticForm_mul_transpose {m : ℕ} :
    modeSymplecticForm (ι := Fin m) * modeSymplecticFormᵀ = 1 := by
  rw [transpose_modeSymplecticForm, mul_neg, modeSymplecticForm_mul_self, neg_neg]

theorem modeSymplecticForm_isUnit (m : ℕ) :
    IsUnit (modeSymplecticForm (ι := Fin m)) :=
  ⟨⟨modeSymplecticForm, modeSymplecticFormᵀ,
    modeSymplecticForm_mul_transpose, modeSymplecticForm_transpose_mul⟩, rfl⟩

/-- Physical displacement covariance given by `modeSymplecticFormᵀ * V * modeSymplecticForm`. -/
def physicalDisplacementCovariance {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  modeSymplecticFormᵀ * V * modeSymplecticForm

theorem physicalDisplacementCovariance_add_scalar {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (c : ℝ) :
    physicalDisplacementCovariance (V + c • 1) = physicalDisplacementCovariance V + c • 1 := by
  simp only [physicalDisplacementCovariance, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, modeSymplecticForm_transpose_mul]

theorem physicalDisplacementCovariance_posDef {m : ℕ}
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.PosDef) :
    (physicalDisplacementCovariance V).PosDef := by
  have h := (modeSymplecticForm_isUnit m).posDef_star_left_conjugate_iff (x := V)
  simpa only [physicalDisplacementCovariance, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using h.mpr hV

theorem physicalDisplacementCovariance_det {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    (physicalDisplacementCovariance V).det = V.det := by
  have h := congrArg Matrix.det (modeSymplecticForm_transpose_mul (m := m))
  rw [Matrix.det_mul, Matrix.det_one] at h
  rw [physicalDisplacementCovariance, Matrix.det_mul, Matrix.det_mul]
  calc
    _ = ((modeSymplecticForm (ι := Fin m))ᵀ.det * modeSymplecticForm.det) * V.det := by ring
    _ = _ := by rw [h, one_mul]

theorem physicalDisplacementCovariance_inv {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    (physicalDisplacementCovariance V)⁻¹ = physicalDisplacementCovariance V⁻¹ := by
  have hΩi : (modeSymplecticForm (ι := Fin m))⁻¹ = modeSymplecticFormᵀ :=
    Matrix.inv_eq_right_inv modeSymplecticForm_mul_transpose
  have hΩti : ((modeSymplecticForm (ι := Fin m))ᵀ)⁻¹ = modeSymplecticForm :=
    Matrix.inv_eq_right_inv modeSymplecticForm_transpose_mul
  rw [physicalDisplacementCovariance, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hΩi, hΩti]
  exact (Matrix.mul_assoc _ _ _).symm

theorem physicalDisplacementCovariance_involutive {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    physicalDisplacementCovariance (physicalDisplacementCovariance V) = V := by
  unfold physicalDisplacementCovariance
  calc
    _ = (modeSymplecticFormᵀ * modeSymplecticFormᵀ) * V *
        (modeSymplecticForm * modeSymplecticForm) := by noncomm_ring
    _ = V := by
      rw [transpose_modeSymplecticForm, neg_mul_neg,
        modeSymplecticForm_mul_self]
      simp

theorem physicalDisplacementCovariance_inverse_quadratic {m : ℕ}
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (u : Fin m × Fin 2 → ℝ) :
    (modeSymplecticForm *ᵥ u) ⬝ᵥ ((physicalDisplacementCovariance V)⁻¹ *ᵥ
      (modeSymplecticForm *ᵥ u)) = u ⬝ᵥ (V⁻¹ *ᵥ u) := by
  have h := dotProduct_congruence (modeSymplecticFormᵀ)
    (physicalDisplacementCovariance V)⁻¹ u u
  rw [Matrix.transpose_transpose] at h
  change _ = u ⬝ᵥ (physicalDisplacementCovariance ((physicalDisplacementCovariance V)⁻¹) *ᵥ u) at h
  rw [physicalDisplacementCovariance_inv, physicalDisplacementCovariance_involutive] at h
  simpa only [physicalDisplacementCovariance_inv] using h

/-- Condition that the data have Gaussian physical characteristic defined as
`HasGaussianDisplacementCharacteristic A (physicalDisplacementCovariance V)`. -/
def HasGaussianPhysicalCharacteristic {m : ℕ}
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) : Prop :=
  HasGaussianDisplacementCharacteristic A (physicalDisplacementCovariance V)

/-- The source Husimi formula derived from the actual Gaussian
characteristic, with physical covariance and literal coherent coordinates. -/
theorem gaussianPhysical_coherent_diagonal {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) (w : MultiModePhaseSpace m) :
    inner ℂ (multiCoherentVector w) (A (multiCoherentVector w)) =
      ((Real.sqrt (V + (1 / 2 : ℝ) • 1).det)⁻¹ : ℂ) *
        Complex.exp ((-(complexRealCoordinates m (fun j => w j) ⬝ᵥ
          ((V + (1 / 2 : ℝ) • 1)⁻¹ *ᵥ complexRealCoordinates m (fun j => w j))) : ℝ) : ℂ) := by
  have hc : (physicalDisplacementCovariance V + (1 / 2 : ℝ) • 1).PosDef := by
    rw [← physicalDisplacementCovariance_add_scalar]
    exact physicalDisplacementCovariance_posDef hC
  have h := gaussianDensity_coherent_diagonal hA hG hc w
  rw [← physicalDisplacementCovariance_add_scalar, physicalDisplacementCovariance_det,
    physicalDisplacementCovariance_inverse_quadratic] at h
  exact h

end VacuumBellSeparation.Gaussian
