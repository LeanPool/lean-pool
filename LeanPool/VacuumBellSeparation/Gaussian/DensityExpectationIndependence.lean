/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveDensityState

/-!
# Basis independence of the actual complex density expectation

For positive inputs, the expectation is real and agrees with the proved
basis-independent positive trace. Mathlib's proved fact that nonnegative
elements span a complex C-star algebra extends this equality to every
bounded operator. Thus no cyclic complex trace identity is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped ComplexOrder

variable {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem densityExpectation_eq_of_nonneg (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) {B : E →L[ℂ] E} (hB : 0 ≤ B) :
    densityExpectation b A B = densityExpectation c A B := by
  have hb := Complex.nonneg_iff.mp (densityExpectation_nonneg b A hB)
  have hc := Complex.nonneg_iff.mp (densityExpectation_nonneg c A hB)
  have ht : ENNReal.ofReal (densityExpectation b A B).re =
      ENNReal.ofReal (densityExpectation c A B).re :=
    (positiveTrace_density_sandwich b hA hB).symm.trans (positiveTrace_density_sandwich c hA hB)
  apply Complex.ext
  · have hr := congrArg ENNReal.toReal ht
    simpa only [ENNReal.toReal_ofReal hb.1, ENNReal.toReal_ofReal hc.1] using hr
  · exact hb.2.symm.trans hc.2

/-- The complex expectation of every bounded operator is independent of
the Hilbert basis used for the absolutely convergent series. -/
theorem densityExpectation_eq (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) (B : E →L[ℂ] E) :
    densityExpectation b A B = densityExpectation c A B := by
  have hlin : (densityExpectationCLM b hA).toLinearMap =
      (densityExpectationCLM c hA).toLinearMap := by
    apply LinearMap.ext_on CStarAlgebra.span_nonneg
    intro T hT
    exact densityExpectation_eq_of_nonneg b c hA hT
  exact DFunLike.congr_fun hlin B

theorem positiveDensityState_apply_eq (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {A : E →L[ℂ] E} (hA : 0 ≤ A) (htrace : positiveTrace A = 1) (B : E →L[ℂ] E) :
    positiveDensityState b hA htrace B = positiveDensityState c hA htrace B :=
  densityExpectation_eq b c ⟨hA, by rw [htrace]; exact ENNReal.one_lt_top⟩ B

end VacuumBellSeparation.Gaussian
