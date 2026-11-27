/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PhysicalGaussianHusimi
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeInverseBargmann
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPrecisionDomain

/-!
# The actual Gaussian Bargmann diagonal and thermal precision algebra

The physical characteristic determines the actual exponential-vector
diagonal. Literal inverse thermal labels act by the real block dilation.
Their Gaussian exponent is precisely the source precision matrix. These
facts precede all bounded inverse-sandwich existence assertions.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexConjugate MatrixOrder Matrix.Norms.L2Operator

theorem gaussianPhysical_bargmann_diagonal {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) (z : Fin m → ℂ) :
    multiBargmannKernel A z z =
      ((Real.sqrt (V + (1 / 2 : ℝ) • 1).det)⁻¹ : ℂ) *
        Complex.exp (((‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^ 2 -
          complexRealCoordinates m z ⬝ᵥ
            ((V + (1 / 2 : ℝ) • 1)⁻¹ *ᵥ complexRealCoordinates m z)) : ℝ) : ℂ) := by
  rw [multiBargmannKernel, multiExponentialVector_eq_normalized,
    map_smul, inner_smul_left, inner_smul_right,
    gaussianPhysical_coherent_diagonal hA hG hC]
  simp only [← Complex.exp_conj, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (V + (1 / 2 : ℝ) • 1).det)⁻¹ : ℂ) *
        (Complex.exp ((‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^ 2 / 2 : ℝ) : ℂ) *
          Complex.exp ((‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^ 2 / 2 : ℝ) : ℂ) *
          Complex.exp ((-(complexRealCoordinates m z ⬝ᵥ
            ((V + (1 / 2 : ℝ) • 1)⁻¹ *ᵥ complexRealCoordinates m z)) : ℝ) : ℂ)) := by ring
    _ = _ := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem complexRealCoordinates_inverseThermalLabel {m : ℕ}
    (q : Fin m → ℝ) (τ : ℝ) (z : Fin m → ℂ) :
    complexRealCoordinates m (multiModeInversePowerLabel q (τ / 2) z) =
      thermalQuadratureDilation q τ *ᵥ complexRealCoordinates m z := by
  funext ⟨j, a⟩
  simp only [thermalQuadratureDilation, modeDiagonal, Matrix.mulVec_diagonal]
  fin_cases a
  · change (((q j ^ (-(τ / 2)) : ℝ) : ℂ) * z j).re =
      q j ^ (-(τ / 2)) * (z j).re
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  · change (((q j ^ (-(τ / 2)) : ℝ) : ℂ) * z j).im =
      q j ^ (-(τ / 2)) * (z j).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

theorem thermalCoherentPrecision_quadratic {m : ℕ}
    (q : Fin m → ℝ) (τ : ℝ)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (u : Fin m × Fin 2 → ℝ) :
    u ⬝ᵥ (thermalCoherentPrecision q τ V *ᵥ u) =
      u ⬝ᵥ u - (thermalQuadratureDilation q τ *ᵥ u) ⬝ᵥ (thermalQuadratureDilation q τ *ᵥ u) +
        (thermalQuadratureDilation q τ *ᵥ u) ⬝ᵥ
          ((V + (1 / 2 : ℝ) • 1)⁻¹ *ᵥ (thermalQuadratureDilation q τ *ᵥ u)) := by
  let T := thermalQuadratureDilation q τ
  have hT : Tᵀ = T := transpose_modeDiagonal _
  have hsq := dotProduct_congruence T (1 : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) u u
  rw [hT, one_mulVec, mul_one] at hsq
  have hC := dotProduct_congruence T (V + (1 / 2 : ℝ) • 1)⁻¹ u u
  rw [hT] at hC
  rw [thermalCoherentPrecision, Matrix.add_mulVec, Matrix.sub_mulVec,
    dotProduct_add, dotProduct_sub, one_mulVec]
  rw [← hsq, ← hC]

theorem thermalCoherentPrecision_coherent_exponent {m : ℕ}
    (q : Fin m → ℝ) (τ : ℝ)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (z : Fin m → ℂ) :
    -‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^ 2 +
      (‖(WithLp.toLp 2 (multiModeInversePowerLabel q (τ / 2) z) : MultiModePhaseSpace m)‖ ^ 2 -
        complexRealCoordinates m (multiModeInversePowerLabel q (τ / 2) z) ⬝ᵥ
          ((V + (1 / 2 : ℝ) • 1)⁻¹ *ᵥ
            complexRealCoordinates m (multiModeInversePowerLabel q (τ / 2) z))) =
      -(complexRealCoordinates m z ⬝ᵥ (thermalCoherentPrecision q τ V *ᵥ
        complexRealCoordinates m z)) := by
  rw [← complexRealCoordinates_dot_self z,
    ← complexRealCoordinates_dot_self (multiModeInversePowerLabel q (τ / 2) z)]
  simp only [complexRealCoordinates_inverseThermalLabel]
  rw [thermalCoherentPrecision_quadratic]
  ring

end VacuumBellSeparation.Gaussian
