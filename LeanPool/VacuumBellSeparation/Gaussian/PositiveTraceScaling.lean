/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveDensityState

/-!
# Real scaling and normalization of actual positive trace-class operators

The extended trace is scaled using the actual basis diagonal. Its finite,
strictly positive value is checked before normalization. No complex trace
of a nonpositive product or bounded inverse of a density is introduced.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem positiveTrace_real_smul (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : 0 ≤ A) {c : ℝ} (hc : 0 ≤ c) :
    positiveTrace (c • A) = ENNReal.ofReal c * positiveTrace A := by
  rw [positiveTrace_eq_tsum_diagonal b (smul_nonneg hc hA),
    positiveTrace_eq_tsum_diagonal b hA]
  simp only [smul_apply, inner_smul_right_eq_smul, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    ENNReal.ofReal_mul hc, ENNReal.tsum_mul_left]

theorem IsPositiveTraceClass.real_smul (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveTraceClass (c • A) := by
  refine ⟨smul_nonneg hc hA.1, ?_⟩
  rw [positiveTrace_real_smul b hA.1 hc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA.2

/-- Continuous linear map for the normalized positive density, of type `E →L[ℂ] E`. -/
def normalizedPositiveDensity (A : E →L[ℂ] E) : E →L[ℂ] E :=
  (positiveTrace A).toReal⁻¹ • A

theorem normalizedPositiveDensity_isPositiveTraceClass (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) :
    IsPositiveTraceClass (normalizedPositiveDensity A) :=
  hA.real_smul b (inv_nonneg.mpr ENNReal.toReal_nonneg)

theorem positiveTrace_normalizedPositiveDensity (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) (htrace : 0 < positiveTrace A) :
    positiveTrace (normalizedPositiveDensity A) = 1 := by
  have hr : 0 < (positiveTrace A).toReal := ENNReal.toReal_pos htrace.ne' hA.2.ne
  rw [normalizedPositiveDensity, positiveTrace_real_smul b hA.1 (inv_nonneg.mpr hr.le)]
  calc
    _ = ENNReal.ofReal (positiveTrace A).toReal⁻¹ *
        ENNReal.ofReal (positiveTrace A).toReal :=
      congrArg (fun t => ENNReal.ofReal (positiveTrace A).toReal⁻¹ * t)
        (ENNReal.ofReal_toReal hA.2.ne).symm
    _ = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le), inv_mul_cancel₀ hr.ne', ENNReal.ofReal_one]

end VacuumBellSeparation.Gaussian
