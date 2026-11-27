/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PositiveContractionPowers

/-!
# The intrinsic bounded function of the resolvent for positive powers

The full resolvent of the constructed power is the genuine bounded CFC
of r ↦ r^c/(r^c+(1-r)^c). The denominator is at least one on [0,1]
for 0≤c≤1. All endpoint conventions are those of unital real powers.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The bounded scalar transform `x ^ c / (x ^ c + (1 - x) ^ c)` used for modular powers. -/
noncomputable def powerResolventFunction (c x : ℝ) : ℝ := x ^ c / (x ^ c + (1 - x) ^ c)

theorem powerResolventFunction_cfc (R : E →L[ℂ] E) (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    cfc (powerResolventFunction c) R = R ^ c * Ring.inverse (R ^ c + (1 - R) ^ c) := by
  have hs (x : ℝ) (hx : x ∈ spectrum ℝ R) : 0 ≤ x ∧ x ≤ 1 := by
    refine ⟨(StarOrderedRing.nonneg_iff_spectrum_nonneg R hR.isSelfAdjoint).mp hR x hx, ?_⟩
    exact (Real.le_norm_self x).trans
      ((IsometricContinuousFunctionalCalculus.norm_spectrum_le R hx hR.isSelfAdjoint).trans
        ((CStarAlgebra.norm_le_one_iff_of_nonneg R hR).mpr hR1))
  have hp : Continuous (fun x : ℝ => x ^ c) := Real.continuous_rpow_const hc
  have hb : Continuous (fun x : ℝ => (1 - x) ^ c) := hp.comp (continuous_const.sub continuous_id)
  have hden (x : ℝ) (hx : x ∈ spectrum ℝ R) : x ^ c + (1 - x) ^ c ≠ 0 := by
    have h₁ := Real.self_le_rpow_of_le_one (hs x hx).1 (hs x hx).2 hc1
    have h₂ := Real.self_le_rpow_of_le_one (sub_nonneg.mpr (hs x hx).2)
      (sub_le_self _ (hs x hx).1) hc1
    linarith
  have hsub : cfc (fun x : ℝ => 1 - x) R = 1 - R := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => x) R
      continuous_const.continuousOn continuous_id.continuousOn,
      cfc_const_one ℝ R hR.isSelfAdjoint, cfc_id' ℝ R hR.isSelfAdjoint]
  have hBc : (1 - R) ^ c = cfc (fun x : ℝ => (1 - x) ^ c) R := by
    rw [CFC.rpow_eq_cfc_real (sub_nonneg.mpr hR1), ← hsub,
      ← cfc_comp' (fun x : ℝ => x ^ c) (fun x : ℝ => 1 - x) R hp.continuousOn
        (continuous_const.sub continuous_id).continuousOn hR.isSelfAdjoint]
  unfold powerResolventFunction
  rw [cfc_map_div (fun x : ℝ => x ^ c)
    (fun x : ℝ => x ^ c + (1 - x) ^ c) R hden hp.continuousOn
      (hp.add hb).continuousOn hR.isSelfAdjoint,
    cfc_add R (fun x : ℝ => x ^ c) (fun x : ℝ => (1 - x) ^ c)
      hp.continuousOn hb.continuousOn, ← CFC.rpow_eq_cfc_real hR, ← hBc]

theorem resolventPowerRatio_resolvent_cfc (R : E →L[ℂ] E)
    (hR : 0 ≤ R) (hR1 : R ≤ 1) (hi : Function.Injective R)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (x y : E) :
    (∃ hy : y ∈ (resolventPowerRatio R hR hi c hc hc1).domain,
      y + resolventPowerRatio R hR hi c hc hc1 ⟨y, hy⟩ = x) ↔
        cfc (powerResolventFunction c) R x = y := by
  rw [powerResolventFunction_cfc R hR hR1 c hc hc1]
  exact resolventPowerRatio_resolvent R hR hR1 hi c hc hc1 x y

end VacuumBellSeparation
