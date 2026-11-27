/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PositiveOperatorPowers
public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioResolvent
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Positive contraction powers and the associated maximal ratios

For an injective positive contraction R and 0≤c≤1, the operators R^c
and (1-R)^c have a boundedly invertible sum. Their actual partial ratio
is positive selfadjoint, and its full resolvent is explicitly computed.
This is a construction step for extended continuous calculus: compatibility
with bounded powers and independence of regularizers are separate results.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem positiveContraction_le_rpow (R : E →L[ℂ] E) (hR : 0 ≤ R) (hR1 : R ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) : R ≤ R ^ c := by
  rw [CFC.rpow_eq_cfc_real hR]
  conv_lhs => rw [← cfc_id' ℝ R hR.isSelfAdjoint]
  apply cfc_mono (hf := continuous_id.continuousOn)
    (hg := (Real.continuous_rpow_const hc).continuousOn)
  intro x hx
  have hx0 : 0 ≤ x :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg R hR.isSelfAdjoint).mp hR x hx
  have hx1 : x ≤ 1 := (Real.le_norm_self x).trans
    ((IsometricContinuousFunctionalCalculus.norm_spectrum_le R hx hR.isSelfAdjoint).trans
      ((CStarAlgebra.norm_le_one_iff_of_nonneg R hR).mpr hR1))
  exact Real.self_le_rpow_of_le_one hx0 hx1 hc1

theorem positiveContraction_power_sum_isUnit (R : E →L[ℂ] E)
    (hR : 0 ≤ R) (hR1 : R ≤ 1) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    IsUnit (R ^ c + (1 - R) ^ c) := by
  have hB : 0 ≤ 1 - R := sub_nonneg.mpr hR1
  have hB1 : 1 - R ≤ 1 := sub_le_self _ hR
  have hsum : 1 ≤ R ^ c + (1 - R) ^ c := by
    calc
      1 = R + (1 - R) := by abel
      _ ≤ R ^ c + (1 - R) ^ c := add_le_add
        (positiveContraction_le_rpow R hR hR1 hc hc1)
        (positiveContraction_le_rpow (1 - R) hB hB1 hc hc1)
  exact CStarAlgebra.isUnit_of_le 1 hsum

theorem positiveContraction_powers_commute (R : E →L[ℂ] E) (c : ℝ) :
    Commute (R ^ c) ((1 - R) ^ c) := by
  have h : Commute R (1 - R) := (Commute.one_right R).sub_right (Commute.refl R)
  exact ((h.cfc_nnreal (fun x => x ^ c)).symm.cfc_nnreal (fun x => x ^ c)).symm

/-- The actual ratio associated with a positive contraction's real powers.
The name records its construction; spectral-power compatibility must be proved. -/
noncomputable def resolventPowerRatio (R : E →L[ℂ] E) (hR : 0 ≤ R)
    (hi : Function.Injective R) (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) : E →ₗ.[ℂ] E :=
  boundedRatio (R ^ c) ((1 - R) ^ c) (positiveOperator_rpow_injective R hR hi hc hc1)

@[simp] theorem resolventPowerRatio_apply (R : E →L[ℂ] E) (hR : 0 ≤ R)
    (hi : Function.Injective R) (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (x : E) :
    resolventPowerRatio R hR hi c hc hc1 ⟨(R ^ c) x, ⟨x, rfl⟩⟩ = ((1 - R) ^ c) x :=
  boundedRatio_apply_range _ _ _ x

theorem resolventPowerRatio_isSelfAdjoint (R : E →L[ℂ] E)
    (hR : 0 ≤ R) (hR1 : R ≤ 1) (hi : Function.Injective R)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    IsSelfAdjoint (resolventPowerRatio R hR hi c hc hc1) :=
  boundedRatio_isSelfAdjoint_of_isUnit_add _ _ _
    (positiveOperator_rpow_denseRange R hR hi hc hc1)
    CFC.rpow_nonneg.isSelfAdjoint CFC.rpow_nonneg.isSelfAdjoint
    (positiveContraction_powers_commute R c)
    (positiveContraction_power_sum_isUnit R hR hR1 hc hc1)

theorem resolventPowerRatio_inner_nonneg (R : E →L[ℂ] E)
    (hR : 0 ≤ R) (hi : Function.Injective R)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (x : (resolventPowerRatio R hR hi c hc hc1).domain) :
    0 ≤ (inner ℂ (x : E) (resolventPowerRatio R hR hi c hc hc1 x)).re := by
  obtain ⟨z, hz, hv⟩ := boundedRatio_representation (R ^ c) ((1 - R) ^ c)
    (positiveOperator_rpow_injective R hR hi hc hc1) x
  change 0 ≤ (inner ℂ (x : E)
    (boundedRatio (R ^ c) ((1 - R) ^ c) (positiveOperator_rpow_injective R hR hi hc hc1) x)).re
  rw [← hz, ← hv]
  have hs := (CFC.rpow_nonneg (a := R) (y := c)).isSelfAdjoint.isSymmetric
    z (((1 - R) ^ c) z)
  change inner ℂ ((R ^ c) z) (((1 - R) ^ c) z) =
    inner ℂ z ((R ^ c) (((1 - R) ^ c) z)) at hs
  rw [hs]
  exact (nonneg_iff_isPositive.mp
    (Commute.mul_nonneg CFC.rpow_nonneg CFC.rpow_nonneg
      (positiveContraction_powers_commute R c))).re_inner_nonneg_right z

/-- The intrinsic inverse (1+L)⁻¹ is an everywhere-defined bounded operator. -/
theorem resolventPowerRatio_resolvent (R : E →L[ℂ] E)
    (hR : 0 ≤ R) (hR1 : R ≤ 1) (hi : Function.Injective R)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (x y : E) :
    (∃ hy : y ∈ (resolventPowerRatio R hR hi c hc hc1).domain,
      y + resolventPowerRatio R hR hi c hc hc1 ⟨y, hy⟩ = x) ↔
        (R ^ c * Ring.inverse (R ^ c + (1 - R) ^ c)) x = y :=
  boundedRatio_resolvent_iff _ _ _ (positiveContraction_power_sum_isUnit R hR hR1 hc hc1) x y

end VacuumBellSeparation
