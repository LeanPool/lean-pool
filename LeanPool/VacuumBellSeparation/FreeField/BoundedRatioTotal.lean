/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.RatioRegularizerIndependence

/-!
# The bounded case of an actual partial ratio

If the denominator is a bounded unit, its range really is the whole
Hilbert space, and the partial ratio agrees with the ordinary bounded
operator. This result concerns equality of full partial maps.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem boundedRatio_eq_toPMap_of_isUnit (A B : E →L[ℂ] E)
    (hi : Function.Injective A) (hA : IsUnit A) :
    boundedRatio A B hi = (B * Ring.inverse A).toPMap ⊤ := by
  have hr (x : E) : A (Ring.inverse A x) = x := by
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using
      congrArg (fun Q : E →L[ℂ] E => Q x) (Ring.mul_inverse_cancel A hA)
  apply LinearPMap.ext
  · ext x
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨Ring.inverse A x, hr x⟩
  · intro x hx hy
    have hh : (⟨x, hx⟩ : (boundedRatio A B hi).domain) =
        ⟨A (Ring.inverse A x), ⟨Ring.inverse A x, rfl⟩⟩ := Subtype.ext (hr x).symm
    rw [hh, boundedRatio_apply_range]
    rfl

omit [CompleteSpace E] in
theorem boundedRatio_eq_toPMap_of_factorization (A B F : E →L[ℂ] E)
    (hi : Function.Injective A) (hA : IsUnit A) (hB : B = F * A) :
    boundedRatio A B hi = F.toPMap ⊤ := by
  rw [boundedRatio_eq_toPMap_of_isUnit A B hi hA, hB,
    mul_assoc, Ring.mul_inverse_cancel A hA, mul_one]

end VacuumBellSeparation
