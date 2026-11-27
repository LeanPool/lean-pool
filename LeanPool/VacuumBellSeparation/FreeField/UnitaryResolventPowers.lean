/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ExponentialResolventCalculus
public import LeanPool.VacuumBellSeparation.FreeField.UnitaryPartialTransport

/-!
# Unitary naturality of the full resolvent power construction

Bounded real CFC naturality and universal resolvent uniqueness transport
the entire partial operator, including its range domain.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem positiveContraction_spectrum_subset_unitInterval (R : E →L[ℂ] E)
    (hR : 0 ≤ R) (hR1 : R ≤ 1) : spectrum ℝ R ⊆ Set.Icc 0 1 := by
  intro x hx
  refine ⟨(StarOrderedRing.nonneg_iff_spectrum_nonneg R hR.isSelfAdjoint).mp hR x hx, ?_⟩
  exact (Real.le_norm_self x).trans
    ((IsometricContinuousFunctionalCalculus.norm_spectrum_le R hx hR.isSelfAdjoint).trans
      ((CStarAlgebra.norm_le_one_iff_of_nonneg R hR).mpr hR1))

theorem unitaryPartialTransport_resolventPowerRatio (V : E ≃ₗᵢ[ℂ] F)
    (R : E →L[ℂ] E) (hR : 0 ≤ R) (hR1 : R ≤ 1) (hiR : Function.Injective R)
    (S : F →L[ℂ] F) (hS : 0 ≤ S) (hS1 : S ≤ 1) (hiS : Function.Injective S)
    (hRS : V.conjStarAlgEquiv R = S) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    unitaryPartialTransport V (resolventPowerRatio R hR hiR c hc hc1) =
      resolventPowerRatio S hS hiS c hc hc1 := by
  have hm : V.conjStarAlgEquiv (cfc (powerResolventFunction c) R) =
      cfc (powerResolventFunction c) S := by
    have hs : IsSelfAdjoint (V.conjStarAlgEquiv R) := hRS.symm ▸ hS.isSelfAdjoint
    have hh := StarAlgHomClass.map_cfc V.conjStarAlgEquiv (powerResolventFunction c) R
      ((continuousOn_powerResolventFunction hc hc1).mono
        (positiveContraction_spectrum_subset_unitInterval R hR hR1))
      (by
        change Continuous V.toContinuousLinearEquiv.conjContinuousAlgEquiv
        exact V.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous)
      hR.isSelfAdjoint hs
    rwa [hRS] at hh
  apply partialOperator_eq_of_resolvent _ _ (cfc (powerResolventFunction c) S)
  · intro x y
    rw [unitaryPartialTransport_resolvent V _ (cfc (powerResolventFunction c) R)
      (resolventPowerRatio_resolvent_cfc R hR hR1 hiR c hc hc1)]
    change (V.conjStarAlgEquiv (cfc (powerResolventFunction c) R)) x = y ↔ _
    rw [hm]
  · exact resolventPowerRatio_resolvent_cfc S hS hS1 hiS c hc hc1

end VacuumBellSeparation
