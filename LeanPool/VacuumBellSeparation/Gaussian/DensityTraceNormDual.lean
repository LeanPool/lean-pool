/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DensityExpectationAdditivity
public import LeanPool.VacuumBellSeparation.Gaussian.CompactTraceNorm

/-!
# Actual trace-norm dual estimate for density expectations

The positive and negative CFC parts of the genuine compact selfadjoint
density difference are trace class. Additivity of actual density
expectations identifies their signed expectation with the original
functional difference. Its norm bound follows from the two proved positive
functional bounds and Tr(D_+)+Tr(D_-)=Tr|D|. No trace duality is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem density_difference_parts_traceClass {ρ σ : E →L[ℂ] E}
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ) :
    IsPositiveTraceClass ((ρ - σ)⁺) ∧ IsPositiveTraceClass ((ρ - σ)⁻) := by
  have hD : IsSelfAdjoint (ρ - σ) := hρ.1.isSelfAdjoint.sub hσ.1.isSelfAdjoint
  have hAbs : IsPositiveTraceClass (CFC.abs (ρ - σ)) :=
    ⟨CFC.abs_nonneg _, operatorTraceNorm_density_difference_lt_top hρ hσ⟩
  constructor
  · apply hAbs.of_le (CFC.posPart_nonneg _)
    rw [← CFC.posPart_add_negPart (ρ - σ) hD]
    exact le_add_of_nonneg_right (CFC.negPart_nonneg _)
  · apply hAbs.of_le (CFC.negPart_nonneg _)
    rw [← CFC.posPart_add_negPart (ρ - σ) hD]
    exact le_add_of_nonneg_left (CFC.posPart_nonneg _)

theorem densityExpectation_difference_jordan (b : HilbertBasis ι ℂ E)
    {ρ σ : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    (B : E →L[ℂ] E) :
    densityExpectation b ρ B - densityExpectation b σ B =
      densityExpectation b ((ρ - σ)⁺) B -
        densityExpectation b ((ρ - σ)⁻) B := by
  obtain ⟨hp, hn⟩ := density_difference_parts_traceClass hρ hσ
  have hD : IsSelfAdjoint (ρ - σ) := hρ.1.isSelfAdjoint.sub hσ.1.isSelfAdjoint
  have he : ρ + (ρ - σ)⁻ = σ + (ρ - σ)⁺ := by
    have h := (sub_eq_sub_iff_add_eq_add).mp (CFC.posPart_sub_negPart (ρ - σ) hD)
    exact h.symm.trans (add_comm _ _)
  have hf := congrArg (fun A => densityExpectation b A B) he
  rw [densityExpectation_add b hρ hn B, densityExpectation_add b hσ hp B] at hf
  apply (sub_eq_sub_iff_add_eq_add).mpr
  exact hf.trans (add_comm _ _)

/-- The actual bounded-observable trace dual bound, for arbitrary positive
trace-class densities and arbitrary bounded complex observables. -/
theorem norm_densityExpectation_sub_le_traceNorm (b : HilbertBasis ι ℂ E)
    {ρ σ : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    (B : E →L[ℂ] E) :
    ‖densityExpectation b ρ B - densityExpectation b σ B‖ ≤
      (operatorTraceNorm (ρ - σ)).toReal * ‖B‖ := by
  obtain ⟨hp, hn⟩ := density_difference_parts_traceClass hρ hσ
  have hD : IsSelfAdjoint (ρ - σ) := hρ.1.isSelfAdjoint.sub hσ.1.isSelfAdjoint
  have ht : (operatorTraceNorm (ρ - σ)).toReal =
      (positiveTrace ((ρ - σ)⁺)).toReal +
        (positiveTrace ((ρ - σ)⁻)).toReal := by
    rw [operatorTraceNorm, ← CFC.posPart_add_negPart (ρ - σ) hD,
      positiveTrace_add hp.1 hn.1, ENNReal.toReal_add hp.2.ne hn.2.ne]
  rw [densityExpectation_difference_jordan b hρ hσ B, ht]
  calc
    _ ≤ ‖densityExpectation b ((ρ - σ)⁺) B‖ +
        ‖densityExpectation b ((ρ - σ)⁻) B‖ := norm_sub_le _ _
    _ ≤ (positiveTrace ((ρ - σ)⁺)).toReal * ‖B‖ +
        (positiveTrace ((ρ - σ)⁻)).toReal * ‖B‖ :=
      add_le_add (norm_densityExpectation_le b hp B) (norm_densityExpectation_le b hn B)
    _ = _ := (add_mul _ _ _).symm

theorem enorm_densityExpectation_sub_le_traceNorm (b : HilbertBasis ι ℂ E)
    {ρ σ : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    (B : E →L[ℂ] E) :
    ENNReal.ofReal ‖densityExpectation b ρ B - densityExpectation b σ B‖ ≤
      operatorTraceNorm (ρ - σ) * ENNReal.ofReal ‖B‖ := by
  have h := ENNReal.ofReal_le_ofReal (norm_densityExpectation_sub_le_traceNorm b hρ hσ B)
  simpa only [ENNReal.ofReal_mul (ENNReal.toReal_nonneg),
    ENNReal.ofReal_toReal (operatorTraceNorm_density_difference_lt_top hρ hσ).ne] using h

end VacuumBellSeparation.Gaussian
