/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Ambient.CoefficientFieldHilbert

/-!
# CoefficientPairing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Coefficient pairing

This file defines the integral pairing induced by a coefficient field on
Hilbert-vector `L²` fields. It also proves the pairing signs obtained when the
second field agrees almost everywhere with an indicator localization of the
first field or its negative.

## Main definitions

- `DivergenceFormProcess.Form.coefficientPairing`: the integral pairing induced by a
  coefficient field.

## Main results

- `DivergenceFormProcess.Form.coefficientPairing_nonneg_of_ae_eq_indicator`
- `DivergenceFormProcess.Form.coefficientPairing_nonpos_of_ae_eq_neg_indicator`
-/

namespace DivergenceFormProcess.Form

open HCPolySupport

/-- The integral pairing of two Hilbert-vector `L²` fields induced by a coefficient field. -/
noncomputable def coefficientPairing {d : ℕ} (a : CoeffField d) (U : Set (Vec d))
    (F G : HilbertVectorL2 U) : ℝ :=
  ∫ x in U,
    vecDot
      (matVecMul (a x) ((hilbertVectorL2ToVectorL2 (U := U) F) x))
      ((hilbertVectorL2ToVectorL2 (U := U) G) x) ∂MeasureTheory.volume

/-- The coefficient pairing is nonnegative when its second field agrees almost
everywhere with an indicator localization of its first field. The set is
arbitrary; its indicator is controlled through the supplied almost-everywhere
identity. -/
theorem coefficientPairing_nonneg_of_ae_eq_indicator
    {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (F G : HilbertVectorL2 U)
    (S : Set (Vec d))
    (hG : ∀ᵐ x ∂volumeMeasureOn U, G x = S.indicator F x) :
    0 ≤ coefficientPairing a U F G := by
  classical
  have hmem : ∀ᵐ x ∂volumeMeasureOn U, x ∈ U :=
    (MeasureTheory.ae_restrict_iff'
      (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun _ hx => hx)
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [hmem, hG,
      coeFn_hilbertVectorL2ToVectorL2 (U := U) F,
      coeFn_hilbertVectorL2ToVectorL2 (U := U) G] with x hxU hxG hxF hxGcoe
  have hxGvec :
      (hilbertVectorL2ToVectorL2 (U := U) G) x =
        S.indicator (hilbertVectorL2ToVectorL2 (U := U) F) x := by
    rw [hxGcoe, Set.indicator_apply]
    by_cases hxS : x ∈ S
    · rw [ite_eq_left hxS, hxF]
      rw [Set.indicator_apply, ite_eq_left hxS] at hxG
      exact congrArg HilbertVec.toVec hxG
    · rw [ite_eq_right hxS]
      rw [Set.indicator_apply, ite_eq_right hxS] at hxG
      simpa only [map_zero] using! congrArg HilbertVec.toVec hxG
  rw [hxGvec, Set.indicator_apply]
  split_ifs
  · let f := (hilbertVectorL2ToVectorL2 (U := U) F) x
    have hAx := hEll.2 x hxU
    have hlower := hAx.2.2.1 f
    have hquad : 0 ≤ vecDot f (matVecMul (a x) f) :=
      (mul_nonneg (le_of_lt hAx.1) (vecNormSq_nonneg f)).trans hlower
    change 0 ≤ vecDot (matVecMul (a x) f) f
    rw [vecDot_comm]
    exact hquad
  · rw [vecDot_zero_right]
    change (0 : ℝ) ≤ 0
    exact le_rfl

/-- The coefficient pairing is nonpositive when its second field agrees almost
everywhere with an indicator localization of the negative of its first field.
The set is arbitrary; its indicator is controlled through the supplied
almost-everywhere identity. -/
theorem coefficientPairing_nonpos_of_ae_eq_neg_indicator
    {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (F G : HilbertVectorL2 U)
    (S : Set (Vec d))
    (hG : ∀ᵐ x ∂volumeMeasureOn U, G x = S.indicator (fun y => -F y) x) :
    coefficientPairing a U F G ≤ 0 := by
  classical
  have hmem : ∀ᵐ x ∂volumeMeasureOn U, x ∈ U :=
    (MeasureTheory.ae_restrict_iff'
      (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun _ hx => hx)
  apply MeasureTheory.integral_nonpos_of_ae
  filter_upwards [hmem, hG,
      coeFn_hilbertVectorL2ToVectorL2 (U := U) F,
      coeFn_hilbertVectorL2ToVectorL2 (U := U) G] with x hxU hxG hxF hxGcoe
  have hxGvec :
      (hilbertVectorL2ToVectorL2 (U := U) G) x =
        S.indicator (fun y => -(hilbertVectorL2ToVectorL2 (U := U) F) y) x := by
    rw [hxGcoe, Set.indicator_apply]
    by_cases hxS : x ∈ S
    · rw [ite_eq_left hxS, hxF]
      rw [Set.indicator_apply, ite_eq_left hxS] at hxG
      simpa only [map_neg] using! congrArg HilbertVec.toVec hxG
    · rw [ite_eq_right hxS]
      rw [Set.indicator_apply, ite_eq_right hxS] at hxG
      simpa only [map_zero] using! congrArg HilbertVec.toVec hxG
  rw [hxGvec, Set.indicator_apply]
  split_ifs
  · rw [vecDot_neg_right]
    let f := (hilbertVectorL2ToVectorL2 (U := U) F) x
    have hAx := hEll.2 x hxU
    have hquad : 0 ≤ vecDot f (matVecMul (a x) f) :=
      (mul_nonneg (le_of_lt hAx.1) (vecNormSq_nonneg f)).trans (hAx.2.2.1 f)
    apply neg_nonpos.mpr
    change 0 ≤ vecDot (matVecMul (a x) f) f
    rw [vecDot_comm]
    exact hquad
  · rw [vecDot_zero_right]
    change (0 : ℝ) ≤ 0
    exact le_rfl

end DivergenceFormProcess.Form
