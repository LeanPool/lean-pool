/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixGaussianFourier
public import LeanPool.VacuumBellSeparation.Gaussian.ComplexMatrixGaussianIntegral

/-!
# Gaussian Fourier integration in actual complex coherent coordinates

The phase is `2 i y·u(z)`, where u gives real and imaginary coordinates.
The genuine complex product measure gives π^m/sqrt(det C) and inverse
quadratic form y·C⁻¹y, with explicit integrability.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Coherent matrix Fourier. -/
def coherentMatrixFourier {m : ℕ}
    (C : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (y : Fin m × Fin 2 → ℝ)
    (z : Fin m → ℂ) : ℂ :=
  Complex.exp ((-(complexRealCoordinates m z ⬝ᵥ (C *ᵥ complexRealCoordinates m z)) : ℝ) +
    2 * Complex.I * ((y ⬝ᵥ complexRealCoordinates m z : ℝ) : ℂ))

theorem coherentMatrixFourier_eq {m : ℕ}
    (C : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (y : Fin m × Fin 2 → ℝ)
    (z : Fin m → ℂ) :
    coherentMatrixFourier C y z =
      matrixGaussianFourier ((2 : ℝ) • C) ((2 : ℝ) • y) (complexRealCoordinates m z) := by
  simp only [coherentMatrixFourier, matrixGaussianFourier, Matrix.smul_mulVec,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  congr 1
  push_cast
  ring

theorem integrable_coherentMatrixFourier {m : ℕ}
    {C : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hC : C.PosDef)
    (y : Fin m × Fin 2 → ℝ) : Integrable (coherentMatrixFourier C y) := by
  have h := (complexRealCoordinates_measurePreserving m).integrable_comp_of_integrable
    (integrable_matrixGaussianFourier (hC.smul (by norm_num : (0 : ℝ) < 2)) ((2 : ℝ) • y))
  simpa only [Function.comp_def, ← coherentMatrixFourier_eq] using h

theorem integral_coherentMatrixFourier {m : ℕ}
    {C : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hC : C.PosDef)
    (y : Fin m × Fin 2 → ℝ) :
    (∫ z : Fin m → ℂ, coherentMatrixFourier C y z) =
      ((Real.pi ^ m / Real.sqrt C.det : ℝ) : ℂ) *
        Complex.exp ((-(y ⬝ᵥ (C⁻¹ *ᵥ y)) : ℝ) : ℂ) := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hi : ((2 : ℝ) • C)⁻¹ = (1 / 2 : ℝ) • C⁻¹ := by
    simpa only [invOf_eq_inv, inv_eq_one_div] using
      Matrix.inv_smul (A := C) (2 : ℝ) ((Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit)
  have hquad : -(1 / 2 : ℝ) * (((2 : ℝ) • y) ⬝ᵥ
      (((2 : ℝ) • C)⁻¹ *ᵥ ((2 : ℝ) • y))) = -(y ⬝ᵥ (C⁻¹ *ᵥ y)) := by
    rw [hi]
    simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    ring
  have h := (complexRealCoordinates_measurePreserving m).integral_comp
    (complexRealCoordinates m).measurableEmbedding
    (matrixGaussianFourier ((2 : ℝ) • C) ((2 : ℝ) • y))
  simp only [← coherentMatrixFourier_eq] at h
  rw [h, integral_matrixGaussianFourier (hC.smul (by norm_num : (0 : ℝ) < 2)),
    hquad, Matrix.det_smul, Fintype.card_prod]
  simp only [Fintype.card_fin]
  have hn : Real.sqrt (2 * Real.pi) ^ (m * 2) = (2 * Real.pi) ^ m := by
    rw [Nat.mul_comm m 2, pow_mul, Real.sq_sqrt (by positivity)]
  have hd : Real.sqrt (2 ^ (m * 2) * C.det) = (2 : ℝ) ^ m * Real.sqrt C.det := by
    rw [Real.sqrt_mul (by positivity), pow_mul, Real.sqrt_sq (by positivity)]
  rw [hn, hd, mul_pow]
  congr 2
  field_simp [show (2 : ℝ) ^ m ≠ 0 by positivity,
    ne_of_gt (Real.sqrt_pos.mpr hC.det_pos)]

end VacuumBellSeparation.Gaussian
