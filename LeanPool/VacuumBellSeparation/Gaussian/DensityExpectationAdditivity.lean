/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DensityExpectationIndependence
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceOrder

/-!
# Additivity of the actual density expectation in positive densities

For positive observables, the genuine square-root sandwich trace is
additive in the density after the proved positive trace interchange.
The actual complex-linear span of positive observables then proves the
identity for every bounded observable. No complex trace on nonpositive
operators or unproved cyclicity is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ComplexOrder ENNReal

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem densityExpectation_add_of_nonneg (b : HilbertBasis ι ℂ E)
    {ρ σ : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    {B : E →L[ℂ] E} (hB : 0 ≤ B) :
    densityExpectation b (ρ + σ) B = densityExpectation b ρ B + densityExpectation b σ B := by
  have he (A : E →L[ℂ] E) (hA : IsPositiveTraceClass A) :
      positiveTrace (CFC.sqrt B * A * CFC.sqrt B) = ENNReal.ofReal
        (densityExpectation b A B).re := by
    rw [positiveTrace_sqrt_sandwich_swap hB hA.1]
    exact positiveTrace_density_sandwich b hA hB
  have hρn := Complex.nonneg_iff.mp (densityExpectation_nonneg b ρ hB)
  have hσn := Complex.nonneg_iff.mp (densityExpectation_nonneg b σ hB)
  have hsum := Complex.nonneg_iff.mp (densityExpectation_nonneg b (ρ + σ) hB)
  have ht : ENNReal.ofReal (densityExpectation b (ρ + σ) B).re =
      ENNReal.ofReal (densityExpectation b ρ B).re + ENNReal.ofReal
        (densityExpectation b σ B).re := by
    rw [← he (ρ + σ) (hρ.add hσ), mul_add, add_mul,
      positiveTrace_add (conjugate_nonneg_of_nonneg hρ.1 (CFC.sqrt_nonneg B))
        (conjugate_nonneg_of_nonneg hσ.1 (CFC.sqrt_nonneg B)), he ρ hρ, he σ hσ]
  rw [← ENNReal.ofReal_add hρn.1 hσn.1] at ht
  apply Complex.ext
  · have hr := congrArg ENNReal.toReal ht
    simpa only [ENNReal.toReal_ofReal hsum.1,
      ENNReal.toReal_ofReal (add_nonneg hρn.1 hσn.1), Complex.add_re] using hr
  · rw [Complex.add_im, ← hsum.2, ← hρn.2, ← hσn.2, zero_add]

/-- Genuine density additivity for arbitrary bounded observables. -/
theorem densityExpectation_add (b : HilbertBasis ι ℂ E)
    {ρ σ : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    (B : E →L[ℂ] E) :
    densityExpectation b (ρ + σ) B = densityExpectation b ρ B + densityExpectation b σ B := by
  have heq : (densityExpectationCLM b (hρ.add hσ)).toLinearMap =
      (densityExpectationCLM b hρ).toLinearMap + (densityExpectationCLM b hσ).toLinearMap := by
    apply LinearMap.ext_on CStarAlgebra.span_nonneg
    intro A hA
    exact densityExpectation_add_of_nonneg b hρ hσ hA
  exact DFunLike.congr_fun heq B

end VacuumBellSeparation.Gaussian
