/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceModularResolvent
public import LeanPool.VacuumBellSeparation.FreeField.ResolventPowerBounded
public import LeanPool.VacuumBellSeparation.FreeField.UnitaryPartialTransport
public import LeanPool.VacuumBellSeparation.FreeField.SourceTomitaAdjoint
public import LeanPool.VacuumBellSeparation.Gaussian.NormalizedDensityPowers

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

/-- The bounded source weight, made from the actual positive Gram operators. -/
noncomputable def sourceModularWeight (c : ℝ) :
    ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U :=
  sourceGram hm U ^ (1 / 2 - c) * conjugateSourceGram hm U ^ c

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

theorem one_sub_sourceModularResolvent :
    1 - sourceModularResolvent hm U = (1 / 2 : ℝ) • conjugateSourceGram hm U := by
  rw [sourceModularResolvent, conjugateSourceGram_eq_two_sub, smul_sub]
  have htwo : (1 / 2 : ℝ) • (2 : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U) = 1
    := by
    rw [show (2 : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U) =
      (2 : ℝ) • 1 by norm_num [two_smul], smul_smul]
    norm_num
  rw [htwo]

/-- Every source vector is in the true partial power domain after sqrt(G).
The witness remains valid at c=0 and c=1/2, with no inverse of G. -/
theorem sourceModularPower_apply_sqrt (hU : Bornology.IsBounded U)
    (c : ℝ) (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) (z : ComplexSourceHilbert hm U) :
    ∃ hx : sourceGramRoot hm U z ∈ (sourceModularPower hm U hU c hc (by linarith)).domain,
      sourceModularPower hm U hU c hc (by linarith) ⟨sourceGramRoot hm U z, hx⟩ =
        sourceModularWeight hm U c z := by
  let G := sourceGram hm U
  let H := conjugateSourceGram hm U
  let R := sourceModularResolvent hm U
  let a : ℝ := (1 / 2 : ℝ) ^ c
  have ha : a ≠ 0 := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) c).ne'
  have hG : 0 ≤ G := nonneg_iff_isPositive.mpr (sourceGram_isPositive hm U)
  have hH : 0 ≤ H := conjugateSourceGram_nonneg hm U
  have hRp : R ^ c = a • G ^ c :=
    Gaussian.positiveOperator_real_smul_rpow hG (by norm_num) hc
  have hHp : (1 - R) ^ c = a • H ^ c := by
    rw [show 1 - R = (1 / 2 : ℝ) • H from one_sub_sourceModularResolvent hm U]
    exact Gaussian.positiveOperator_real_smul_rpow hH (by norm_num) hc
  have hGG : G ^ c * G ^ (1 / 2 - c) = sourceGramRoot hm U := by
    rw [← positiveOperator_rpow_add G hc (sub_nonneg.mpr hc2),
      show c + (1 / 2 - c) = 1 / 2 by ring]
    exact (CFC.sqrt_eq_rpow (a := G)).symm
  have hcomm : Commute (G ^ (1 / 2 - c)) (H ^ c) :=
    (((sourceGram_commute_conjugateSourceGram hm U).cfc_nnreal
      (fun x => x ^ (1 / 2 - c))).symm.cfc_nnreal (fun x => x ^ c)).symm
  let w := a⁻¹ • ((G ^ (1 / 2 - c)) z)
  have hAw : (R ^ c) w = sourceGramRoot hm U z := by
    rw [hRp]
    change a • (G ^ c) (a⁻¹ • ((G ^ (1 / 2 - c)) z)) = _
    rw [map_smul_of_tower, smul_smul, mul_inv_cancel₀ ha, one_smul]
    exact congrArg (fun Q : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U => Q z) hGG
  have hBw : ((1 - R) ^ c) w = sourceModularWeight hm U c z := by
    rw [hHp]
    change a • (H ^ c) (a⁻¹ • ((G ^ (1 / 2 - c)) z)) = _
    rw [map_smul_of_tower, smul_smul, mul_inv_cancel₀ ha, one_smul]
    exact congrArg (fun Q : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U => Q z)
      hcomm.eq.symm
  refine ⟨⟨w, hAw⟩, ?_⟩
  have hh : (⟨sourceGramRoot hm U z, ⟨w, hAw⟩⟩ :
      (sourceModularPower hm U hU c hc (by linarith)).domain) =
        ⟨(R ^ c) w, ⟨w, rfl⟩⟩ := Subtype.ext hAw.symm
  rw [hh]
  exact (resolventPowerRatio_apply R (sourceModularResolvent_nonneg hm U)
    (sourceModularResolvent_injective hm U hU) c hc (by linarith) w).trans hBw

end VacuumBellSeparation
