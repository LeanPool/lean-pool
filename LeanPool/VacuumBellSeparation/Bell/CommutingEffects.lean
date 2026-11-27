/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.Cells

/-! # Products and complements of commuting effects -/

@[expose] public section

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual product of commuting effects remains an effect. -/
theorem commuting_effect_product {A B : H →L[ℂ] H}
    (hA₀ : 0 ≤ A) (hA₁ : A ≤ 1) (hB₀ : 0 ≤ B) (hB₁ : B ≤ 1)
    (hAB : A * B = B * A) : 0 ≤ A * B ∧ A * B ≤ 1 := by
  refine ⟨Commute.mul_nonneg hA₀ hB₀ hAB, ?_⟩
  have hc : Commute A (1 - B) := by
    change A * (1 - B) = (1 - B) * A
    rw [mul_sub, sub_mul, mul_one, one_mul, hAB]
  have hpos := Commute.mul_nonneg hA₀ (sub_nonneg.mpr hB₁) hc
  have hle : A * B ≤ A := by
    apply sub_nonneg.mp
    simpa only [mul_sub, mul_one] using hpos
  exact hle.trans hA₁

end VacuumBellSeparation
