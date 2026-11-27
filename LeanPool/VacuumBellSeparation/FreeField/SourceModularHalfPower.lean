/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceModularPowers
public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioGraph

/-!
# The full half-power is the actual positive modular root

This is equality of partial maps, not merely agreement on source vectors.
It identifies the regularized continuous half-power with the independently
constructed positive selfadjoint root whose maximal square is the modular
operator.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

theorem sourceModularPower_half (hU : Bornology.IsBounded U) :
    sourceModularPower hm U hU (1 / 2) (by norm_num) (by norm_num) =
      sourceModularRoot hm U hU := by
  let a : ℝ := (1 / 2 : ℝ) ^ (1 / 2 : ℝ)
  have ha : a ≠ 0 := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) _).ne'
  have hG : 0 ≤ sourceGram hm U := nonneg_iff_isPositive.mpr (sourceGram_isPositive hm U)
  have hR : sourceModularResolvent hm U ^ (1 / 2 : ℝ) = a • sourceGramRoot hm U := by
    rw [sourceModularResolvent, Gaussian.positiveOperator_real_smul_rpow hG
      (by norm_num) (by norm_num), ← CFC.sqrt_eq_rpow]
    rfl
  have hB : (1 - sourceModularResolvent hm U) ^ (1 / 2 : ℝ) =
      a • conjugateSourceGramRoot hm U := by
    rw [one_sub_sourceModularResolvent, Gaussian.positiveOperator_real_smul_rpow
      (conjugateSourceGram_nonneg hm U) (by norm_num) (by norm_num), ← CFC.sqrt_eq_rpow]
    rfl
  unfold sourceModularPower resolventPowerRatio sourceModularRoot
  apply LinearPMap.eq_of_eq_graph
  ext p
  rcases p with ⟨x, y⟩
  rw [boundedRatio_mem_graph, boundedRatio_mem_graph, hR, hB]
  constructor
  · rintro ⟨z, hz, hv⟩
    refine ⟨a • z, ?_, ?_⟩
    · simpa only [map_smul_of_tower, smul_apply] using hz
    · simpa only [map_smul_of_tower, smul_apply] using hv
  · rintro ⟨z, rfl, rfl⟩
    refine ⟨a⁻¹ • z, ?_, ?_⟩ <;>
      simp only [smul_apply, map_smul_of_tower, smul_smul, mul_inv_cancel₀ ha, one_smul]

theorem sourceModularPower_half_square (hU : Bornology.IsBounded U) :
    partialComp (sourceModularPower hm U hU (1 / 2) (by norm_num) (by norm_num))
      (sourceModularPower hm U hU (1 / 2) (by norm_num) (by norm_num)) =
        sourceModularOperator hm U hU := by
  rw [sourceModularPower_half, sourceModularRoot_square]

end VacuumBellSeparation
