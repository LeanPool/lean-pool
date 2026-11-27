/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.EventConstants

/-!
# Upper event constants from denominator-free effect bounds

Both actual supremum definitions are bounded directly. In the reverse
direction the extended quotient retains the zero-denominator convention.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projections_subset_effects (M : VonNeumannAlgebra H) : projections M ⊆ effects M := by
  intro E hE
  exact ⟨hE.1, isPositive_of_mem_projections hE,
    isPositive_of_mem_projections (one_sub_mem_projections hE)⟩

theorem eventConstPlus_le_of_effect_bound (ω : State H) (M N : VonNeumannAlgebra H)
    {r K : ℝ}
    (hbound : ∀ E ∈ effects M, ∀ P ∈ effects N,
      (ω (E * P)).re ^ r ≤ K * ((ω E).re * (ω P).re) ^ (r - 1)) :
    eventConstPlus ω M N r ≤ ENNReal.ofReal K := by
  apply iSup_le
  intro E
  apply iSup_le
  intro hE
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  apply iSup_le
  intro hpos
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hpos (r - 1))).mpr
    (hbound E (projections_subset_effects M hE) P (projections_subset_effects N hP))

theorem eventConstMinus_le_of_effect_bound (ω : State H) (M N : VonNeumannAlgebra H)
    {r K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ E ∈ effects M, ∀ P ∈ effects N,
      ((ω E).re * (ω P).re) ^ r ≤ K * (ω (E * P)).re ^ (r - 1)) :
    eventConstMinus ω M N r ≤ ENNReal.ofReal K := by
  apply iSup_le
  intro E
  apply iSup_le
  intro hE
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  apply iSup_le
  intro hpos
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal
    (hbound E (projections_subset_effects M hE) P (projections_subset_effects N hP))

end VacuumBellSeparation
