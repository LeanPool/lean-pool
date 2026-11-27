/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FinitePhysicalReverseSpatial
public import LeanPool.VacuumBellSeparation.FreeField.RegionalGaussianBounds

/-!
# Reverse estimates on the full physical regional algebras

The actual finite reverse Gaussian quantities obey one uniform bound.
Canonical exhaustion passes it to every regional effect and to the true
extended event constant, including zero-probability events.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped ENNReal InnerProductSpace

theorem exists_uniform_regional_reverse :
    ∃ Sgeo A : ℝ, 600 ≤ Sgeo ∧ 0 < A ∧
      ∀ (μ : ℝ) (hμ : 0 < μ) (s : ℝ), Sgeo ≤ s →
        A * s ^ (-gammaRev) ≤ aRev / 4 →
        ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (V : FreeFieldVacuum μ H) (U W : Set (EuclideanSpace ℝ (Fin 3))),
          U ⊆ Metric.ball 0 1 → W ⊆ Metric.ball (spatialAxisDisplacement s 0) 1 → Disjoint U W →
          (∀ E ∈ effects (timeZeroLocalAlgebra V hμ U), ∀ P ∈ effects (timeZeroLocalAlgebra V hμ W),
            ((⟪V.vacuum, E V.vacuum⟫_ℂ).re * (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^ rMinus ≤
              Real.exp (2 * rMinus * aRev⁻¹ * (A * s ^ (-gammaRev))) *
                (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ (rMinus - 1)) ∧
          eventConstMinus (vectorState V.vacuum V.vacuum_norm)
            (timeZeroLocalAlgebra V hμ U) (timeZeroLocalAlgebra V hμ W) rMinus ≤
              ENNReal.ofReal (Real.exp (2 * rMinus * aRev⁻¹ * (A * s ^ (-gammaRev)))) := by
  obtain ⟨Sgeo, A, hSgeo, hA, hfinite⟩ := exists_uniform_finite_physical_reverse
  refine ⟨Sgeo, A, hSgeo, hA, ?_⟩
  intro μ hμ s hs hsmall H _ _ _ V U W hU hW hUW
  have hfin := hfinite μ hμ s hs hsmall H V U W hU hW hUW
  refine ⟨?_, ?_⟩
  · intro E hE P hP
    exact regional_reverse_events_of_finite_gaussian V hμ U W hUW
      one_lt_rMinus_lt_two.1 (Real.exp_nonneg _) hfin hE hP
  · exact regional_eventConstMinus_le_of_finite_gaussian V hμ U W hUW
      one_lt_rMinus_lt_two.1 (Real.exp_nonneg _) hfin

end VacuumBellSeparation
