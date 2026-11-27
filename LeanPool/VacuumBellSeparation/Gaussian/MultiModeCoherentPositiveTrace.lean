/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeCoherentResolution
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveMatrixExtension

/-!
# Extended positive trace from the actual finite-mode coherent diagonal

Parseval and nonnegative Tonelli turn the proved weak coherent resolution
into an extended trace identity. The operator may have infinite trace.
The normalization is π^(-m) against complex product Lebesgue measure;
no Bochner integral of operators or finite-trace assumption is used.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ENNReal

theorem multiCoherentFrameCoordinate_norm_sq {m : ℕ}
    (x : MultiModeOscillatorSpace m) (z : Fin m → ℂ) :
    ‖multiCoherentFrameCoordinate x z‖ ^ 2 = (Real.pi ^ m)⁻¹ *
      ‖inner ℂ (multiCoherentVector (WithLp.toLp 2 z)) x‖ ^ 2 := by
  rw [multiCoherentFrameCoordinate, norm_mul, norm_inv, norm_pow,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
    ← pow_mul, Nat.mul_comm m 2, pow_mul, Real.sq_sqrt Real.pi_pos.le]

/-- Multi coherent positive diagonal. -/
def multiCoherentPositiveDiagonal {m : ℕ}
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) (z : Fin m → ℂ) : ℝ :=
  (Real.pi ^ m)⁻¹ * (inner ℂ (multiCoherentVector (WithLp.toLp 2 z))
    (A (multiCoherentVector (WithLp.toLp 2 z)))).re

theorem multiCoherentPositiveDiagonal_nonneg {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : 0 ≤ A) (z : Fin m → ℂ) : 0 ≤ multiCoherentPositiveDiagonal A z :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg Real.pi_pos.le _))
    ((ContinuousLinearMap.nonneg_iff_isPositive.mp hA).re_inner_nonneg_right _)

theorem tsum_multiCoherent_sqrt_basis {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : 0 ≤ A) (z : Fin m → ℂ) :
    (∑' k, ENNReal.ofReal (‖multiCoherentFrameCoordinate
      (CFC.sqrt A (multiModeNumberBasis m k)) z‖ ^ 2)) =
        ENNReal.ofReal (multiCoherentPositiveDiagonal A z) := by
  let S := CFC.sqrt A
  let v := multiCoherentVector (WithLp.toLp 2 z)
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hnorm (k : Fin m → ℕ) : ‖inner ℂ v (S (multiModeNumberBasis m k))‖ =
      ‖inner ℂ (multiModeNumberBasis m k) (S v)‖ := by
    rw [← S.adjoint_inner_left, hS.adjoint_eq, norm_inner_symm]
  simp only [multiCoherentFrameCoordinate_norm_sq,
    ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg Real.pi_pos.le m))]
  change (∑' k, ENNReal.ofReal ((Real.pi ^ m)⁻¹) *
    ENNReal.ofReal (‖inner ℂ v (S (multiModeNumberBasis m k))‖ ^ 2)) = _
  simp_rw [hnorm]
  rw [ENNReal.tsum_mul_left, tsum_basis_inner_norm_sq (multiModeNumberBasis m),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg Real.pi_pos.le m))]
  change ENNReal.ofReal ((Real.pi ^ m)⁻¹ * ‖CFC.sqrt A v‖ ^ 2) = _
  exact congrArg (fun t : ℝ => ENNReal.ofReal ((Real.pi ^ m)⁻¹ * t))
    (sqrt_norm_sq_eq_diagonal hA v)

/-- Coherent resolution evaluates the actual extended positive trace,
including infinity, on the full finite-mode oscillator Hilbert space. -/
theorem positiveTrace_eq_lintegral_multiCoherentDiagonal {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A) :
    positiveTrace A = ∫⁻ z : Fin m → ℂ, ENNReal.ofReal (multiCoherentPositiveDiagonal A z) := by
  let f : (Fin m → ℕ) → (Fin m → ℂ) → ℝ := fun k z =>
    ‖multiCoherentFrameCoordinate (CFC.sqrt A (multiModeNumberBasis m k)) z‖ ^ 2
  have hint (k : Fin m → ℕ) : Integrable (f k) :=
    integrable_multiCoherentFrameCoordinate_norm_sq _
  have heval (k : Fin m → ℕ) :
      (∫⁻ z, ENNReal.ofReal (f k z)) = ENNReal.ofReal (‖CFC.sqrt A
        (multiModeNumberBasis m k)‖ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint k)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
    exact congrArg ENNReal.ofReal (integral_multiCoherentFrameCoordinate_norm_sq _)
  rw [positiveTrace_eq_basisSquareTrace (multiModeNumberBasis m), basisSquareTrace]
  calc
    _ = ∑' k, ∫⁻ z, ENNReal.ofReal (f k z) := tsum_congr fun k => (heval k).symm
    _ = ∫⁻ z, ∑' k, ENNReal.ofReal (f k z) :=
      (lintegral_tsum (fun k => (hint k).aemeasurable.ennreal_ofReal)).symm
    _ = _ := by
      apply lintegral_congr
      intro z
      exact tsum_multiCoherent_sqrt_basis hA z

end VacuumBellSeparation.Gaussian
