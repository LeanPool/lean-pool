/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixWeylLabels
public import LeanPool.VacuumBellSeparation.Gaussian.DensityCharacteristicUniqueness

/-!
# Actual Weyl operators in raw real displacement coordinates

The label is the genuine inverse of interleaved real/imaginary coordinates.
The Weyl phase is exp(-i xᵀΩy), and the actual displacement Gaussian
characteristic is exp(-xᵀVx). These are raw displacement coordinates; the
physical covariance rotation and factor one half remain explicit later.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix

variable {m : ℕ}

/-- Real coordinate Weyl obtained from `multiOscillatorWeyl`. -/
def realCoordinateWeyl (x : Fin m × Fin 2 → ℝ) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  multiOscillatorWeyl ((complexRealLinearEquiv m).symm x)

@[simp] theorem realCoordinateWeyl_zero : realCoordinateWeyl (0 : Fin m × Fin 2 → ℝ) = 1 := by
  rw [realCoordinateWeyl, map_zero, multiOscillatorWeyl_zero]

theorem realCoordinateWeyl_star (x : Fin m × Fin 2 → ℝ) :
    star (realCoordinateWeyl x) = realCoordinateWeyl (-x) := by
  change (multiOscillatorWeyl ((complexRealLinearEquiv m).symm x)).adjoint = _
  rw [multiOscillatorWeyl_adjoint, realCoordinateWeyl, map_neg]

theorem realCoordinateWeyl_mul (x y : Fin m × Fin 2 → ℝ) :
    realCoordinateWeyl x * realCoordinateWeyl y =
      Complex.exp (-Complex.I * ((x ⬝ᵥ (modeSymplecticForm *ᵥ y) : ℝ) : ℂ)) •
        realCoordinateWeyl (x + y) := by
  rw [realCoordinateWeyl, realCoordinateWeyl, multiOscillatorWeyl_mul,
    weylPhase, inner_im_eq_real_symplectic]
  simp only [id_eq, LinearEquiv.apply_symm_apply, realCoordinateWeyl, map_add]
  congr 2
  ring

theorem gaussianDisplacement_realCoordinateWeyl
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianDisplacementCharacteristic A V) (x : Fin m × Fin 2 → ℝ) :
    densityExpectation (multiModeNumberBasis m) A (realCoordinateWeyl x) =
      Complex.exp ((-(x ⬝ᵥ (V *ᵥ x)) : ℝ) : ℂ) := by
  let z := (complexRealLinearEquiv m).symm x
  have hz : (WithLp.toLp 2 (fun j => z j) : MultiModePhaseSpace m) = z := by ext j; rfl
  have hx : complexRealCoordinates m (fun j => z j) = x :=
    (complexRealLinearEquiv m).apply_symm_apply x
  change densityExpectation (multiModeNumberBasis m) A (multiOscillatorWeyl z) = _
  simpa only [hz, hx] using hG (fun j => z j)

theorem real_bilinear_smul (M : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (x y : Fin m × Fin 2 → ℝ) (a b : ℝ) :
    (a • x) ⬝ᵥ (M *ᵥ (b • y)) = (a * b) * (x ⬝ᵥ (M *ᵥ y)) := by
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

end VacuumBellSeparation.Gaussian
