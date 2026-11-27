/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioResolvent

/-!
# A full partial operator is determined by its bounded resolvent

The universal resolvent equation retains the entire graph, including its
domain. We use it to prove independence of two bounded ratio representations
whose numerators and denominators give the same cross product. This is the
regularizer-independence step for an extended continuous functional calculus.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem partialOperator_eq_of_resolvent (T S : E →ₗ.[ℂ] E) (R : E →L[ℂ] E)
    (hT : ∀ x y : E, (∃ hy : y ∈ T.domain, y + T ⟨y, hy⟩ = x) ↔ R x = y)
    (hS : ∀ x y : E, (∃ hy : y ∈ S.domain, y + S ⟨y, hy⟩ = x) ↔ R x = y) : T = S := by
  have hTS (x : E) (hx : x ∈ T.domain) :
      ∃ hy : x ∈ S.domain, S ⟨x, hy⟩ = T ⟨x, hx⟩ := by
    have hr := (hT (x + T ⟨x, hx⟩) x).mp ⟨hx, rfl⟩
    obtain ⟨hy, hh⟩ := (hS (x + T ⟨x, hx⟩) x).mpr hr
    exact ⟨hy, add_left_cancel hh⟩
  have hST (x : E) (hx : x ∈ S.domain) : x ∈ T.domain := by
    have hr := (hS (x + S ⟨x, hx⟩) x).mp ⟨hx, rfl⟩
    exact ((hT (x + S ⟨x, hx⟩) x).mpr hr).choose
  apply LinearPMap.ext
  · ext x
    exact ⟨fun hx => (hTS x hx).choose, hST x⟩
  · intro x hx hy
    obtain ⟨hy', hh⟩ := hTS x hx
    exact hh.symm

omit [CompleteSpace E] in
/-- Equal bounded resolvents imply equality of the full ratio operators. -/
theorem boundedRatio_eq_of_resolvent_eq (A B C D : E →L[ℂ] E)
    (hA : Function.Injective A) (hC : Function.Injective C)
    (hAB : IsUnit (A + B)) (hCD : IsUnit (C + D))
    (heq : A * Ring.inverse (A + B) = C * Ring.inverse (C + D)) :
    boundedRatio A B hA = boundedRatio C D hC := by
  apply partialOperator_eq_of_resolvent _ _ (A * Ring.inverse (A + B))
    (boundedRatio_resolvent_iff A B hA hAB)
  intro x y
  rw [boundedRatio_resolvent_iff C D hC hCD, heq]

omit [CompleteSpace E] in
/-- Actual regularizer independence. The cross-product identity is literal
bounded-operator equality; it can be supplied by bounded CFC scalar equality. -/
theorem boundedRatio_eq_of_cross_product (A B C D : E →L[ℂ] E)
    (hA : Function.Injective A) (hC : Function.Injective C)
    (hc : Commute A B) (hAB : IsUnit (A + B)) (hCD : IsUnit (C + D))
    (hcross : A * D = B * C) :
    boundedRatio A B hA = boundedRatio C D hC := by
  apply boundedRatio_eq_of_resolvent_eq A B C D hA hC hAB hCD
  have hAi : Commute A (Ring.inverse (A + B)) := by
    rw [Ring.inverse_of_isUnit hAB]
    apply Commute.units_inv_right
    simpa only [IsUnit.unit_spec] using (Commute.refl A).add_right hc
  have hprod : A * (C + D) = (A + B) * C := by
    rw [mul_add, add_mul, hcross]
  calc
    A * Ring.inverse (A + B) =
        A * Ring.inverse (A + B) * ((C + D) * Ring.inverse (C + D)) := by
          rw [Ring.mul_inverse_cancel _ hCD, mul_one]
    _ = Ring.inverse (A + B) * (A * (C + D)) * Ring.inverse (C + D) := by
      rw [hAi.eq]
      simp only [mul_assoc]
    _ = Ring.inverse (A + B) * ((A + B) * C) * Ring.inverse (C + D) := by rw [hprod]
    _ = C * Ring.inverse (C + D) := by
      rw [← mul_assoc (Ring.inverse (A + B)), Ring.inverse_mul_cancel _ hAB, one_mul]

end VacuumBellSeparation
