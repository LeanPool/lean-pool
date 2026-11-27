/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.RationalResolvent
public import LeanPool.VacuumBellSeparation.Bell.DirectedAlgebraUnion

/-!
# Every strict scalar multiple of an effect is a quadratic resolvent transform

For 0≤E≤1 and 0≤r<1, the genuine bounded selfadjoint parameter is the real
functional calculus of sqrt(rt/(1-rt)). Its quadratic resolvent is exactly
1-rE. This uses only the true spectrum of E and does not assume an inverse
at r=1.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Effect parameter function given by `Real.sqrt (r * t / (1 - r * t))`. -/
noncomputable def effectParameterFunction (r t : ℝ) : ℝ := Real.sqrt (r * t / (1 - r * t))

theorem effect_spectrum_bounds {E : H →L[ℂ] H} (hE : 0 ≤ E) (hE1 : E ≤ 1)
    {t : ℝ} (ht : t ∈ spectrum ℝ E) : 0 ≤ t ∧ t ≤ 1 := by
  refine ⟨(StarOrderedRing.nonneg_iff_spectrum_nonneg E hE.isSelfAdjoint).mp hE t ht, ?_⟩
  exact (Real.le_norm_self t).trans
    ((IsometricContinuousFunctionalCalculus.norm_spectrum_le E ht hE.isSelfAdjoint).trans
      ((CStarAlgebra.norm_le_one_iff_of_nonneg E hE).mpr hE1))

theorem effectParameterFunction_continuousOn {E : H →L[ℂ] H}
    (hE : 0 ≤ E) (hE1 : E ≤ 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (effectParameterFunction r) (spectrum ℝ E) := by
  apply Real.continuous_sqrt.comp_continuousOn
  apply (continuous_const.mul continuous_id).continuousOn.div
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  intro t ht
  have ht1 := (effect_spectrum_bounds hE hE1 ht).2
  have hrt : r * t < 1 := (mul_le_of_le_one_right hr ht1).trans_lt hr1
  exact ne_of_gt (sub_pos.mpr hrt)

theorem quadraticResolventFunction_effectParameter {r t : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    quadraticResolventFunction (effectParameterFunction r t) = 1 - r * t := by
  have hrt : r * t < 1 := (mul_le_of_le_one_right hr ht1).trans_lt hr1
  have hden : 0 < 1 - r * t := sub_pos.mpr hrt
  have hnonneg : 0 ≤ r * t / (1 - r * t) := div_nonneg (mul_nonneg hr ht) hden.le
  rw [quadraticResolventFunction, effectParameterFunction, Real.sq_sqrt hnonneg]
  have he : 1 + r * t / (1 - r * t) = 1 / (1 - r * t) := by
    field_simp [hden.ne']; ring
  rw [he, one_div_one_div]

/-- Effect resolvent parameter obtained from `cfc`. -/
noncomputable def effectResolventParameter (r : ℝ) (E : H →L[ℂ] H) : H →L[ℂ] H :=
  cfc (effectParameterFunction r) E

theorem effectResolventParameter_isSelfAdjoint (r : ℝ) (E : H →L[ℂ] H) :
    IsSelfAdjoint (effectResolventParameter r E) := cfc_predicate _ _

theorem quadraticResolvent_effectResolventParameter {E : H →L[ℂ] H}
    (hE : 0 ≤ E) (hE1 : E ≤ 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    quadraticResolvent (effectResolventParameter r E) = 1 - r • E := by
  rw [quadraticResolvent, effectResolventParameter,
    ← cfc_comp' quadraticResolventFunction (effectParameterFunction r) E
      quadraticResolventFunction_continuous.continuousOn
      (effectParameterFunction_continuousOn hE hE1 hr hr1) hE.isSelfAdjoint]
  calc
    cfc (fun t => quadraticResolventFunction (effectParameterFunction r t)) E =
        cfc (fun t : ℝ => 1 - r * t) E := cfc_congr (fun t ht =>
          quadraticResolventFunction_effectParameter hr hr1
            (effect_spectrum_bounds hE hE1 ht).1 (effect_spectrum_bounds hE hE1 ht).2)
    _ = 1 - r • E := by
      rw [cfc_sub (fun _ : ℝ => 1) (fun t : ℝ => r * t) E
        continuous_const.continuousOn (continuous_const.mul continuous_id).continuousOn,
        cfc_const_one ℝ E hE.isSelfAdjoint, cfc_const_mul_id r E hE.isSelfAdjoint]

theorem one_sub_quadraticResolvent_effectResolventParameter {E : H →L[ℂ] H}
    (hE : 0 ≤ E) (hE1 : E ≤ 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    1 - quadraticResolvent (effectResolventParameter r E) = r • E := by
  rw [quadraticResolvent_effectResolventParameter hE hE1 hr hr1, sub_sub_cancel]

theorem effectResolventParameter_mem (A : VonNeumannAlgebra H)
    {E : H →L[ℂ] H} (hE : E ∈ A) (r : ℝ) : effectResolventParameter r E ∈ A :=
  cfc_mem_vonNeumannAlgebra A _ hE

end VacuumBellSeparation
