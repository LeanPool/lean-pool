/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceModularResolvent
public import LeanPool.VacuumBellSeparation.Gaussian.NormalizedDensityPowers

/-!
# A whole-source range witness without a bounded-region premise

The explicit witness uses only nonnegative CFC powers, and requires neither
injectivity nor an inverse of the Gram operator. It therefore also applies
to the original unbounded halfspace source completion.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- The bounded source weight, made from the actual positive Gram operators. -/
noncomputable def sourceModularWeight (c : ℝ) :
    ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U :=
  sourceGram hm U ^ (1 / 2 - c) * conjugateSourceGram hm U ^ c

theorem one_sub_sourceModularResolvent :
    1 - sourceModularResolvent hm U = (1 / 2 : ℝ) • conjugateSourceGram hm U := by
  rw [sourceModularResolvent, conjugateSourceGram_eq_two_sub, smul_sub]
  have htwo : (1 / 2 : ℝ) • (2 : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U) = 1
    := by
    rw [show (2 : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U) =
      (2 : ℝ) • 1 by norm_num [two_smul], smul_smul]
    norm_num
  rw [htwo]

theorem sourceModularWeight_range_witness {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2)
    (z : ComplexSourceHilbert hm U) :
    ∃ w : ComplexSourceHilbert hm U,
      (sourceModularResolvent hm U ^ c) w = sourceGramRoot hm U z ∧
        ((1 - sourceModularResolvent hm U) ^ c) w = sourceModularWeight hm U c z := by
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
  exact ⟨w, hAw, hBw⟩

end VacuumBellSeparation
