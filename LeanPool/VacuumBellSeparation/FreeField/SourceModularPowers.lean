/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourcePowerRangeWitness
public import LeanPool.VacuumBellSeparation.FreeField.ResolventPowerBounded
public import LeanPool.VacuumBellSeparation.FreeField.UnitaryPartialTransport
public import LeanPool.VacuumBellSeparation.FreeField.SourceTomitaAdjoint

/-!
# Resolvent functional calculus and the bounded whole-source modular weights

The intrinsic resolvent of the actual source modular operator is G/2.
The positive powers below use the constructed regularizable continuous
calculus on that resolvent. They are actual positive selfadjoint partial
operators. At exponent one they equal the original modular ratio, with
full domain equality. For 0≤c≤1/2, an explicit range witness proves that
every sqrt(G)z lies in the power domain and its image is the literal
bounded operator h_c=G^(1/2-c)Gbar^c applied to z.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap
open scoped InnerProductSpace

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- The regularizable continuous power associated with the intrinsic resolvent. -/
noncomputable def sourceModularPower (hU : Bornology.IsBounded U)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    ComplexSourceHilbert hm U →ₗ.[ℂ] ComplexSourceHilbert hm U :=
  resolventPowerRatio (sourceModularResolvent hm U) (sourceModularResolvent_nonneg hm U)
    (sourceModularResolvent_injective hm U hU) c hc hc1

theorem sourceModularPower_isSelfAdjoint (hU : Bornology.IsBounded U)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    IsSelfAdjoint (sourceModularPower hm U hU c hc hc1) :=
  resolventPowerRatio_isSelfAdjoint _ (sourceModularResolvent_nonneg hm U)
    (sourceModularResolvent_le_one hm U) _ c hc hc1

theorem sourceModularPower_one (hU : Bornology.IsBounded U) :
    sourceModularPower hm U hU 1 (by norm_num) (by norm_num) = sourceModularOperator hm U hU := by
  apply partialOperator_eq_of_resolvent _ _ (sourceModularResolvent hm U)
  · intro x y
    rw [sourceModularPower, resolventPowerRatio_resolvent _
      (sourceModularResolvent_nonneg hm U) (sourceModularResolvent_le_one hm U)]
    have hb : 0 ≤ 1 - sourceModularResolvent hm U := sub_nonneg.mpr
      (sourceModularResolvent_le_one hm U)
    rw [CFC.rpow_one _ (sourceModularResolvent_nonneg hm U), CFC.rpow_one _ hb,
      show sourceModularResolvent hm U + (1 - sourceModularResolvent hm U) = 1 by abel,
      Ring.inverse_one, mul_one]
  · exact sourceModularResolvent_spec hm U hU

/-- Every source vector is in the true partial power domain after sqrt(G).
The witness remains valid at c=0 and c=1/2, with no inverse of G. -/
theorem sourceModularPower_apply_sqrt (hU : Bornology.IsBounded U)
    (c : ℝ) (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) (z : ComplexSourceHilbert hm U) :
    ∃ hx : sourceGramRoot hm U z ∈ (sourceModularPower hm U hU c hc (by linarith)).domain,
      sourceModularPower hm U hU c hc (by linarith) ⟨sourceGramRoot hm U z, hx⟩ =
        sourceModularWeight hm U c z := by
  let R := sourceModularResolvent hm U
  obtain ⟨w, hAw, hBw⟩ := sourceModularWeight_range_witness hm U hc hc2 z
  refine ⟨⟨w, hAw⟩, ?_⟩
  have hh : (⟨sourceGramRoot hm U z, ⟨w, hAw⟩⟩ :
      (sourceModularPower hm U hU c hc (by linarith)).domain) =
        ⟨(R ^ c) w, ⟨w, rfl⟩⟩ := Subtype.ext hAw.symm
  rw [hh]
  exact (resolventPowerRatio_apply R (sourceModularResolvent_nonneg hm U)
    (sourceModularResolvent_injective hm U hU) c hc (by linarith) w).trans hBw

end VacuumBellSeparation
