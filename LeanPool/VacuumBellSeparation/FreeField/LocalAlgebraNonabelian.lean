/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroNonabelian
public import LeanPool.VacuumBellSeparation.FreeField.TranslatedVacuum
public import LeanPool.VacuumBellSeparation.FreeField.OpenVacuumCyclicity

/-!
# Nonabelian physical double-cone and open-region algebras

The witnesses are actual Weyl operators, transported only by the proved
spacetime relabeling. No nonabelianity assumption is added to the vacuum.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every positive-radius double cone has noncommuting local observables. -/
theorem FreeFieldVacuum.localAlgebra_doubleCone_nonabelian
    (V : FreeFieldVacuum m H) (hm : 0 < m) (a : Spacetime) {R : ℝ} (hR : 0 < R) :
    ∃ A ∈ localAlgebra V (doubleCone a R), ∃ B ∈ localAlgebra V (doubleCone a R),
      A * B ≠ B * A := by
  obtain ⟨A, hA, B, hB, hAB⟩ := (V.translated a).timeZeroLocalAlgebra_nonabelian hm
    (U := Metric.ball 0 R) Metric.isOpen_ball (Metric.nonempty_ball.mpr hR)
  have hinc : timeZeroLocalAlgebra (V.translated a) hm (Metric.ball 0 R) ≤
      localAlgebra V (doubleCone a R) := by
    rw [← V.localAlgebra_translated_doubleCone_zero a R]
    exact timeZeroLocalAlgebra_ball_le (V.translated a) hm hR 0
  exact ⟨A, hinc hA, B, hinc hB, hAB⟩

/-- Every nonempty open spacetime region has a nonabelian physical local algebra. -/
theorem FreeFieldVacuum.localAlgebra_open_nonabelian
    (V : FreeFieldVacuum m H) (hm : 0 < m)
    {O : Set Spacetime} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ A ∈ localAlgebra V O, ∃ B ∈ localAlgebra V O, A * B ≠ B * A := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨R, hR, hsub⟩ := exists_doubleCone_subset_of_isOpen_at hO ha
  obtain ⟨A, hA, B, hB, hAB⟩ := V.localAlgebra_doubleCone_nonabelian hm a hR
  exact ⟨A, localAlgebra_mono V hsub hA, B, localAlgebra_mono V hsub hB, hAB⟩

end VacuumBellSeparation
