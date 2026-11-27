/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceModularOperator
public import LeanPool.VacuumBellSeparation.FreeField.PositiveContractionPowers

/-!
# The intrinsic source modular resolvent

The universal equation y+Delta y=x has the unique solution Gx/2.
Consequently the source ratio has the actual injective positive contraction
R=G/2 as its resolvent. This supplies the intrinsic input for the extended
continuous calculus, while allowing spectrum at zero.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- Continuous linear map for the source modular resolvent, of type `ComplexSourceHilbert hm U
→L[ℂ] ComplexSourceHilbert hm U`. -/
noncomputable def sourceModularResolvent :
    ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U :=
  (1 / 2 : ℝ) • sourceGram hm U

theorem sourceModularResolvent_nonneg : 0 ≤ sourceModularResolvent hm U :=
  smul_nonneg (by norm_num) (nonneg_iff_isPositive.mpr (sourceGram_isPositive hm U))

theorem sourceModularResolvent_le_one : sourceModularResolvent hm U ≤ 1 := by
  have hG : sourceGram hm U ≤ 2 := by
    exact sub_nonneg.mp ((conjugateSourceGram_eq_two_sub hm U) ▸ conjugateSourceGram_nonneg hm U)
  have hh := smul_le_smul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have htwo : (1 / 2 : ℝ) • (2 : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U) = 1
    := by
    rw [show (2 : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U) =
      (2 : ℝ) • 1 by norm_num [two_smul], smul_smul]
    norm_num
  change (1 / 2 : ℝ) • sourceGram hm U ≤ 1
  rwa [htwo] at hh

theorem sourceModularResolvent_injective (hU : Bornology.IsBounded U) :
    Function.Injective (sourceModularResolvent hm U) := by
  intro x y h
  apply sourceGram_injective hm U hU
  change (1 / 2 : ℝ) • sourceGram hm U x = (1 / 2 : ℝ) • sourceGram hm U y at h
  exact (smul_right_injective _ (by norm_num : (1 / 2 : ℝ) ≠ 0)) h

theorem sourceModularResolvent_spec (hU : Bornology.IsBounded U)
    (x y : ComplexSourceHilbert hm U) :
    (∃ hy : y ∈ (sourceModularOperator hm U hU).domain,
      y + sourceModularOperator hm U hU ⟨y, hy⟩ = x) ↔
        sourceModularResolvent hm U x = y := by
  have hsum (z : ComplexSourceHilbert hm U) :
      sourceGram hm U z + conjugateSourceGram hm U z = (2 : ℝ) • z := by
    rw [conjugateSourceGram_eq_two_sub]
    simp only [sub_apply, ofNat_apply, two_smul]
    abel
  constructor
  · rintro ⟨hy, heq⟩
    obtain ⟨z, hz, hv⟩ := boundedRatio_representation (sourceGram hm U)
      (conjugateSourceGram hm U) (sourceGram_injective hm U hU) ⟨y, hy⟩
    have hx : (2 : ℝ) • z = x := by
      rw [← hsum, hz, hv]
      exact heq
    rw [← hx]
    change (1 / 2 : ℝ) • sourceGram hm U ((2 : ℝ) • z) = y
    simpa only [map_smul_of_tower, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
      one_smul] using hz
  · intro heq
    let z := (1 / 2 : ℝ) • x
    have hz : sourceGram hm U z = y := by
      simpa only [z, map_smul_of_tower, sourceModularResolvent, smul_apply] using heq
    refine ⟨⟨z, hz⟩, ?_⟩
    have hh : (⟨y, ⟨z, hz⟩⟩ : (sourceModularOperator hm U hU).domain) =
        ⟨sourceGram hm U z, ⟨z, rfl⟩⟩ := Subtype.ext hz.symm
    rw [hh, sourceModularOperator_apply, ← hz, hsum]
    dsimp [z]
    norm_num [smul_smul]

end VacuumBellSeparation
