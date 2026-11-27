/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LocalVacuumCyclicity
public import LeanPool.VacuumBellSeparation.FreeField.Isotony

/-!
# Local vacuum cyclicity for every nonempty open spacetime region

Every point of an open region admits a positive-radius double cone contained
in it. Isotony then extends the proved double-cone orbit density on full H.
The region need not be bounded; empty regions are explicitly excluded.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

theorem exists_doubleCone_subset_of_isOpen_at {O : Set Spacetime}
    (hO : IsOpen O) {a : Spacetime} (ha : a ∈ O) :
    ∃ R : ℝ, 0 < R ∧ doubleCone a R ⊆ O := by
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds ha)
  refine ⟨R, hR, fun x hx => hsub ?_⟩
  change |x.1 - a.1| + ‖x.2 - a.2‖ < R at hx
  rw [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm, Real.norm_eq_abs]
  exact max_lt (by linarith [norm_nonneg (x.2 - a.2)])
    (by linarith [abs_nonneg (x.1 - a.1)])

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The massive physical vacuum has a dense local-algebra orbit on every
nonempty open region, in its original full representation space. -/
theorem FreeFieldVacuum.vacuum_cyclic_open
    {m : ℝ} (hm : 0 < m) (V : FreeFieldVacuum m H)
    {O : Set Spacetime} (hO : IsOpen O) (hne : O.Nonempty) :
    (Submodule.span ℂ {x : H | ∃ A : H →L[ℂ] H,
      A ∈ localAlgebra V O ∧ x = A V.vacuum}).topologicalClosure = ⊤ := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨R, hR, hsub⟩ := exists_doubleCone_subset_of_isOpen_at hO ha
  apply top_unique
  rw [← V.vacuum_cyclic_doubleCone hm a hR]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro x ⟨A, hA, hx⟩
  exact ⟨A, localAlgebra_mono V hsub hA, hx⟩

end VacuumBellSeparation
