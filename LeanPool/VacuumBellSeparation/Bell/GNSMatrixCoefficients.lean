/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.GNSUnitVector
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! # Literal GNS matrix coefficients and operator order -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open scoped InnerProductSpace ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gns_matrix_coefficient (φ : A →ₚ[ℂ] ℂ) (a X b : A) :
    inner ℂ (φ.gnsStarAlgHom a (gnsUnitVector φ))
      (φ.gnsStarAlgHom X (φ.gnsStarAlgHom b (gnsUnitVector φ))) =
        φ (star a * X * b) := by
  rw [← gnsUnitVector_expectation φ (star a * X * b)]
  simp only [map_mul, map_star, mul_apply_eq_comp]
  exact (φ.gnsStarAlgHom a).adjoint_inner_right _ _ |>.symm

/-- Positivity is derived from the C-star square root in the original algebra. -/
theorem gnsStarAlgHom_nonneg (φ : A →ₚ[ℂ] ℂ) {X : A} (hX : 0 ≤ X) :
    0 ≤ φ.gnsStarAlgHom X := by
  have he : star (CFC.sqrt X) * CFC.sqrt X = X := by
    rw [(CFC.sqrt_nonneg X).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self X hX]
  rw [← he, map_mul, map_star]
  exact star_mul_self_nonneg _

theorem gnsStarAlgHom_monotone (φ : A →ₚ[ℂ] ℂ) : Monotone φ.gnsStarAlgHom := by
  intro X Y hXY
  apply sub_nonneg.mp
  simpa only [map_sub] using gnsStarAlgHom_nonneg φ (sub_nonneg.mpr hXY)

theorem gns_apply_unitVector_eq_zero_iff_of_faithful (φ : A →ₚ[ℂ] ℂ)
    (hfaithful : ∀ a : A, φ (star a * a) = 0 → a = 0) (a : A) :
    φ.gnsStarAlgHom a (gnsUnitVector φ) = 0 ↔ a = 0 := by
  constructor
  · intro ha
    apply hfaithful a
    rw [← gns_apply_unitVector_norm_sq, ha]
    norm_num
  · rintro rfl
    simp

end VacuumBellSeparation
