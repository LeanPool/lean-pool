/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixGaussianComplexLinear
public import LeanPool.VacuumBellSeparation.Gaussian.ComplexMatrixGaussianIntegral

/-!
# Complex-linear Gaussian integration in genuine coherent coordinates

The real/imaginary coordinate equivalence preserves the actual product
Lebesgue measures. Applying the actual matrix Gaussian formula at 2C gives
π^m/sqrt(det C) and the bilinear complex exponent aᵀC⁻¹a/4.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem complexifyMatrix_real_smul {ι κ : Type*}
    (c : ℝ) (M : Matrix ι κ ℝ) :
    complexifyMatrix (c • M) = (c : ℂ) • complexifyMatrix M := by
  classical
  ext i j
  simp only [complexifyMatrix_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]

/-- Coherent Gaussian complex linear. -/
def coherentGaussianComplexLinear {m : ℕ}
    (C : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (a : Fin m × Fin 2 → ℂ)
    (z : Fin m → ℂ) : ℂ :=
  Complex.exp ((-(complexRealCoordinates m z ⬝ᵥ (C *ᵥ complexRealCoordinates m z)) : ℝ) +
    a ⬝ᵥ (fun i => (complexRealCoordinates m z i : ℂ)))

theorem coherentGaussianComplexLinear_eq {m : ℕ}
    (C : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (a : Fin m × Fin 2 → ℂ)
    (z : Fin m → ℂ) :
    coherentGaussianComplexLinear C a z =
      matrixGaussianComplexLinear ((2 : ℝ) • C) a (complexRealCoordinates m z) := by
  simp only [coherentGaussianComplexLinear, matrixGaussianComplexLinear,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  push_cast
  ring

theorem integrable_coherentGaussianComplexLinear {m : ℕ}
    {C : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hC : C.PosDef)
    (a : Fin m × Fin 2 → ℂ) : Integrable (coherentGaussianComplexLinear C a) := by
  have h := (complexRealCoordinates_measurePreserving m).integrable_comp_of_integrable
    (integrable_matrixGaussianComplexLinear (hC.smul (by norm_num : (0 : ℝ) < 2)) a)
  simpa only [Function.comp_def, ← coherentGaussianComplexLinear_eq] using h

theorem integral_coherentGaussianComplexLinear {m : ℕ}
    {C : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hC : C.PosDef)
    (a : Fin m × Fin 2 → ℂ) :
    (∫ z : Fin m → ℂ, coherentGaussianComplexLinear C a z) =
      ((Real.pi ^ m / Real.sqrt C.det : ℝ) : ℂ) *
        Complex.exp ((1 / 4 : ℂ) * (a ⬝ᵥ (complexifyMatrix C⁻¹ *ᵥ a))) := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hi : ((2 : ℝ) • C)⁻¹ = (1 / 2 : ℝ) • C⁻¹ := by
    simpa only [invOf_eq_inv, inv_eq_one_div] using
      Matrix.inv_smul (A := C) (2 : ℝ) ((Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit)
  have hquad : (1 / 2 : ℂ) * (a ⬝ᵥ (complexifyMatrix ((2 : ℝ) • C)⁻¹ *ᵥ a)) =
      (1 / 4 : ℂ) * (a ⬝ᵥ (complexifyMatrix C⁻¹ *ᵥ a)) := by
    rw [hi, complexifyMatrix_real_smul]
    simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have h := (complexRealCoordinates_measurePreserving m).integral_comp
    (complexRealCoordinates m).measurableEmbedding
    (matrixGaussianComplexLinear ((2 : ℝ) • C) a)
  simp only [← coherentGaussianComplexLinear_eq] at h
  rw [h, integral_matrixGaussianComplexLinear (hC.smul (by norm_num : (0 : ℝ) < 2)),
    hquad, Matrix.det_smul, Fintype.card_prod]
  simp only [Fintype.card_fin]
  have hn : Real.sqrt (2 * Real.pi) ^ (m * 2) = (2 * Real.pi) ^ m := by
    rw [Nat.mul_comm m 2, pow_mul, Real.sq_sqrt (by positivity)]
  have hd : Real.sqrt (2 ^ (m * 2) * C.det) = (2 : ℝ) ^ m * Real.sqrt C.det := by
    rw [Real.sqrt_mul (by positivity), pow_mul, Real.sqrt_sq (by positivity)]
  rw [hn, hd, mul_pow]
  congr 2
  field_simp [show (2 : ℝ) ^ m ≠ 0 by positivity, ne_of_gt (Real.sqrt_pos.mpr hC.det_pos)]

end VacuumBellSeparation.Gaussian
