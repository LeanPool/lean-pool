/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceSpace

/-!
# Explicit local symplectic partners

The quarter-turn (f,g) ↦ (-g,f) preserves local support. Its pairing
with (f,g) is the actual integral of f²+g², which vanishes only for the
zero smooth compact source. This supplies local partners constructively.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

/-- The support-preserving quarter-turn on the literal test pairs. -/
def timeZeroQuarterTurn : TimeZeroSource →ₗ[ℝ] TimeZeroSource where
  toFun u := (-u.2, u.1)
  map_add' u v := by
    apply Prod.ext
    · change -(u.2 + v.2) = -u.2 + -v.2
      exact neg_add u.2 v.2
    · rfl
  map_smul' a u := by ext <;> simp

@[simp] theorem timeZeroQuarterTurn_apply (u : TimeZeroSource) :
    timeZeroQuarterTurn u = (-u.2, u.1) := rfl

theorem timeZeroQuarterTurn_sq (u : TimeZeroSource) :
    timeZeroQuarterTurn (timeZeroQuarterTurn u) = -u := by
  apply Prod.ext <;> rfl

theorem timeZeroQuarterTurn_local {U : Set (EuclideanSpace ℝ (Fin 3))}
    {u : TimeZeroSource} (hu : u ∈ localizedTimeZeroSources U) :
    timeZeroQuarterTurn u ∈ localizedTimeZeroSources U := by
  refine ⟨?_, hu.1⟩
  change tsupport (fun x => -(u.2.1 x)) ⊆ U
  change tsupport (-u.2.1) ⊆ U
  simpa only [tsupport_neg] using hu.2

theorem timeZeroSymplectic_quarterTurn (u : TimeZeroSource) :
    timeZeroSymplectic u (timeZeroQuarterTurn u) =
      ∫ x : EuclideanSpace ℝ (Fin 3), (u.1.1 x) ^ 2 + (u.2.1 x) ^ 2 := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change u.1.1 x * u.1.1 x - u.2.1 x * (-(u.2.1 x)) = _
    ring

theorem timeZeroSymplectic_quarterTurn_eq_zero_iff (u : TimeZeroSource) :
    timeZeroSymplectic u (timeZeroQuarterTurn u) = 0 ↔ u = 0 := by
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (u.1.1 x) ^ 2 + (u.2.1 x) ^ 2) := by
    have he : (fun x : EuclideanSpace ℝ (Fin 3) =>
        u.1.1 x * (timeZeroQuarterTurn u).2.1 x -
          u.2.1 x * (timeZeroQuarterTurn u).1.1 x) =
        (fun x => (u.1.1 x) ^ 2 + (u.2.1 x) ^ 2) := by
      funext x
      change u.1.1 x * u.1.1 x - u.2.1 x * (-(u.2.1 x)) = _
      ring
    exact he ▸ integrable_timeZeroSymplectic u (timeZeroQuarterTurn u)
  rw [timeZeroSymplectic_quarterTurn]
  constructor
  · intro hz
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun x => add_nonneg (sq_nonneg _) (sq_nonneg _)) hint).mp hz
    have h₁ : u.1.1 =ᵐ[volume] 0 := hae.mono fun x hx => by
      have hp := sq_nonneg (u.2.1 x)
      dsimp only [Pi.zero_apply] at hx ⊢
      nlinarith [sq_nonneg (u.1.1 x)]
    have h₂ : u.2.1 =ᵐ[volume] 0 := hae.mono fun x hx => by
      have hp := sq_nonneg (u.1.1 x)
      dsimp only [Pi.zero_apply] at hx ⊢
      nlinarith [sq_nonneg (u.2.1 x)]
    apply Prod.ext
    · exact Subtype.ext (Measure.eq_of_ae_eq h₁ u.1.2.1.continuous continuous_const)
    · exact Subtype.ext (Measure.eq_of_ae_eq h₂ u.2.2.1.continuous continuous_const)
  · rintro rfl
    change (∫ x : EuclideanSpace ℝ (Fin 3), (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 0
    simp

/-- Actual nondegeneracy on every local smooth source space, with an explicit partner. -/
theorem exists_local_symplectic_partner {U : Set (EuclideanSpace ℝ (Fin 3))}
    {u : TimeZeroSource} (hu : u ∈ localizedTimeZeroSources U) (hne : u ≠ 0) :
    ∃ v ∈ localizedTimeZeroSources U, timeZeroSymplectic u v ≠ 0 :=
  ⟨timeZeroQuarterTurn u, timeZeroQuarterTurn_local hu,
    fun h => hne ((timeZeroSymplectic_quarterTurn_eq_zero_iff u).mp h)⟩

end VacuumBellSeparation
