/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.DenseRangeFactorization
public import LeanPool.VacuumBellSeparation.FreeField.SourceReserve
public import LeanPool.VacuumBellSeparation.FreeField.PositiveOperatorPowers

/-!
# Literal negative-reserve factorization convention

For 0≤b≤1 the positive reserve power is injective with dense range,
even if its spectrum accumulates at zero. A norm bound against R^b
is equivalent to a unique bounded factor on the whole source Hilbert
space. This is the continuous-extension meaning of T R^(-b).
-/

@[expose] public section

namespace VacuumBellSeparation

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem sourceReserve_rpow_injective (hU : Bornology.IsBounded U)
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : Function.Injective (sourceReserve hm U ^ b) :=
  positiveOperator_rpow_injective _ (sourceReserve_nonneg hm U)
    (sourceReserve_injective hm U hU) hb0 hb1

theorem sourceReserve_rpow_denseRange (hU : Bornology.IsBounded U)
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : DenseRange (sourceReserve hm U ^ b) :=
  positiveOperator_rpow_denseRange _ (sourceReserve_nonneg hm U)
    (sourceReserve_injective hm U hU) hb0 hb1

/-- Exact range-norm interpretation, for vector maps and hence for scalar functionals. -/
theorem sourceReserve_factorization_iff (hU : Bornology.IsBounded U)
    (T : ComplexSourceHilbert hm U →ₗ[ℂ] F) {b C : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hC : 0 ≤ C) :
    (∀ z, ‖T z‖ ≤ C * ‖(sourceReserve hm U ^ b) z‖) ↔
      ∃! L : ComplexSourceHilbert hm U →L[ℂ] F,
        (∀ z, L ((sourceReserve hm U ^ b) z) = T z) ∧ ‖L‖ ≤ C := by
  constructor
  · exact existsUnique_factor_of_denseRange_bound _
      (sourceReserve_rpow_injective hm U hU hb0 hb1)
      (sourceReserve_rpow_denseRange hm U hU hb0 hb1) T hC
  · rintro ⟨L, ⟨hL, hnorm⟩, _⟩
    exact bound_of_factor _ T L hL hnorm

end VacuumBellSeparation
