/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.RegionalForwardExactConstant
public import LeanPool.VacuumBellSeparation.FreeField.RegionalReverseDoubleCones
public import LeanPool.VacuumBellSeparation.FreeField.MainReduction

/-!
# The actual physical estimates used in Section 8

The forward and reverse constructions supply constants before the mass,
separation and vacuum representation. Taking the maximum of their eventual
thresholds gives the existing Section8Estimates statement. The original
double cones, their full von Neumann algebras and all local contractions are
retained. No estimate is supplied as a premise.
-/

@[expose] public section

namespace VacuumBellSeparation

theorem spatialAxisDisplacement_zero_eq_axis (s : ℝ) :
    spatialAxisDisplacement s 0 = s • e₁ := by
  ext i
  fin_cases i <;> simp [spatialAxisDisplacement, e₁]

/-- The Section 8 hypothesis of the previously established reduction is
discharged by the actual regional estimates. -/
theorem section8Estimates : Section8Estimates := by
  obtain ⟨Sp, Ap, hSp, hAp, hp⟩ :=
    exists_uniform_doubleCone_forward_exact_constant
  let Q₀ := 4 * Real.sqrt (Ap / expB rPlus)
  have hb : 0 < expB rPlus := by norm_num [expB, rPlus]
  have hQ₀ : 0 < Q₀ := mul_pos (by norm_num) (Real.sqrt_pos.2 (div_pos hAp hb))
  obtain ⟨Sm, Am, hSm, hAm, hm⟩ := exists_uniform_doubleCone_reverse
  refine ⟨Ap, Am, Q₀, max Sp Sm, hAp, hAm, hQ₀, ?_⟩
  intro μ s hμ hs _ _ _ H _ _ _ V
  have hforward := hp μ hμ s ((le_max_left _ _).trans hs) H V
  have hreverse := hm μ hμ s ((le_max_right _ _).trans hs) H V
  simp only [spatialAxisDisplacement_zero_eq_axis] at hforward hreverse
  refine ⟨hforward.2.1, ?_, ?_⟩
  · have h := hreverse.2
    rw [← div_eq_mul_inv] at h
    exact h
  · intro A hA B hB
    change ‖vacuumComplexCovariance V.vacuum A B‖ ≤ Q₀ / s
    exact hforward.2.2 A hA.1 B hB.1 hA.2.2 hB.2.2

end VacuumBellSeparation
