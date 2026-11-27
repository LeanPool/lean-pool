/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroVacuumCyclicity
public import LeanPool.VacuumBellSeparation.FreeField.TranslatedVacuum

/-!
# Vacuum cyclicity for every original positive-radius double cone

The local orbit is dense in the original full representation, at arbitrary
temporal and spatial centers. Translation covariance is proved by an actual
relabeling of the compact test functions with the same physical covariance.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The positive-mass free-field vacuum is cyclic for every actual double cone. -/
theorem FreeFieldVacuum.vacuum_cyclic_doubleCone
    {m : ℝ} (hm : 0 < m) (V : FreeFieldVacuum m H)
    (a : Spacetime) {R : ℝ} (hR : 0 < R) :
    (Submodule.span ℂ {x : H | ∃ A : H →L[ℂ] H,
      A ∈ localAlgebra V (doubleCone a R) ∧ x = A V.vacuum}).topologicalClosure = ⊤ := by
  have h := (V.translated a).vacuum_cyclic_doubleCone_timeZero hm 0 hR
  change (Submodule.span ℂ {x : H | ∃ A : H →L[ℂ] H,
    A ∈ localAlgebra (V.translated a) (doubleCone 0 R) ∧ x = A V.vacuum}).topologicalClosure = ⊤
      at h
  rw [V.localAlgebra_translated_doubleCone_zero] at h
  exact h

end VacuumBellSeparation
