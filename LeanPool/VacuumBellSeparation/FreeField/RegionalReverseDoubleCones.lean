/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.RegionalReverseSpatial
public import LeanPool.VacuumBellSeparation.FreeField.RegionalBallSeparation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Unconditional eventual reverse estimates on the physical double cones

The true inverse-power decay supplies one mass-independent smallness
threshold. Actual disjointness and the proved time-slice equality then
give the reverse event bound on the full spacetime algebras.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian Metric Filter
open scoped ENNReal InnerProductSpace Topology

theorem exists_reverse_smallness_threshold (A : ℝ) :
    ∃ S : ℝ, 1 ≤ S ∧ ∀ s : ℝ, S ≤ s → A * s ^ (-gammaRev) ≤ aRev / 4 := by
  have hlim : Tendsto (fun s : ℝ => A * s ^ (-gammaRev)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop gammaRev_pos).const_mul A
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_le_nhds (div_pos aRev_pos_le.1 (by norm_num : (0 : ℝ) < 4))))
  exact ⟨max 1 S, le_max_left _ _, fun s hs => hS s ((le_max_right _ _).trans hs)⟩

/-- No source factor, Gaussian, approximation, disjointness or scalar
smallness premise remains in this full physical statement. -/
theorem exists_uniform_doubleCone_reverse :
    ∃ S A : ℝ, 600 ≤ S ∧ 0 < A ∧
      ∀ (μ : ℝ) (_ : 0 < μ) (s : ℝ), S ≤ s →
        ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (V : FreeFieldVacuum μ H),
          (∀ E ∈ effects (localAlgebra V (doubleCone (0, 0) 1)),
            ∀ P ∈ effects (localAlgebra V (doubleCone (0, spatialAxisDisplacement s 0) 1)),
              ((⟪V.vacuum, E V.vacuum⟫_ℂ).re * (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^ rMinus ≤
                Real.exp (2 * rMinus * aRev⁻¹ * (A * s ^ (-gammaRev))) *
                  (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ (rMinus - 1)) ∧
          eventConstMinus (vectorState V.vacuum V.vacuum_norm)
            (localAlgebra V (doubleCone (0, 0) 1))
            (localAlgebra V (doubleCone (0, spatialAxisDisplacement s 0) 1)) rMinus ≤
              ENNReal.ofReal (Real.exp (2 * rMinus * aRev⁻¹ * (A * s ^ (-gammaRev)))) := by
  obtain ⟨Sgeo, A, hSgeo, hA, hbound⟩ := exists_uniform_regional_reverse
  obtain ⟨Ssmall, _, hsmall⟩ := exists_reverse_smallness_threshold A
  refine ⟨max Sgeo Ssmall, A, hSgeo.trans (le_max_left _ _), hA, ?_⟩
  intro μ hμ s hs H _ _ _ V
  have hgeo : Sgeo ≤ s := (le_max_left _ _).trans hs
  have hs₂ : 2 ≤ s := by linarith
  have heps := hsmall s ((le_max_right _ _).trans hs)
  have h := hbound μ hμ s hgeo heps H V
    (ball 0 1) (ball (spatialAxisDisplacement s 0) 1) (Set.Subset.refl _) (Set.Subset.refl _)
    (regionalForward_unit_balls_disjoint hs₂)
  simpa only [← localAlgebra_doubleCone_eq_timeZeroLocalAlgebra V hμ (by norm_num : (0 : ℝ) < 1) 0,
    ← localAlgebra_doubleCone_eq_timeZeroLocalAlgebra V hμ (by norm_num : (0 : ℝ) < 1)
      (spatialAxisDisplacement s 0)] using h

end VacuumBellSeparation
