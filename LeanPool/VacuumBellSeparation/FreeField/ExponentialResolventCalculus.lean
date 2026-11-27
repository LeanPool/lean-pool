/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LpContinuousFunctionalCalculus
public import LeanPool.VacuumBellSeparation.FreeField.ExponentialMultiplicationPositive
public import LeanPool.VacuumBellSeparation.FreeField.ResolventPowerFunction
public import LeanPool.VacuumBellSeparation.FreeField.RatioRegularizerIndependence

/-!
# Exact fractional powers of the maximal exponential multiplication operator

The genuine bounded CFC of the logistic resolvent gives the logistic
resolvent of the scaled exponent. Equality of universal resolvents then
identifies the full partial maps, including all domain vectors. Endpoint
c=0 uses the unital power convention and yields the identity operator.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ContinuousLinearMap
open scoped ENNReal

theorem continuousOn_powerResolventFunction {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    ContinuousOn (powerResolventFunction c) (Set.Icc 0 1) := by
  have ha := Real.continuous_rpow_const hc
  have hb : Continuous (fun x : ℝ => (1 - x) ^ c) :=
    ha.comp (continuous_const.sub continuous_id)
  apply ha.continuousOn.div (ha.add hb).continuousOn
  intro x hx
  have h₁ := Real.self_le_rpow_of_le_one hx.1 hx.2 hc1
  have h₂ := Real.self_le_rpow_of_le_one (sub_nonneg.mpr hx.2)
    (sub_le_self 1 hx.1) hc1
  change x ^ c + (1 - x) ^ c ≠ 0
  linarith

theorem powerResolventFunction_exponentialRatio (c t : ℝ) :
    powerResolventFunction c (exponentialRatioCoefficient t) =
      exponentialRatioCoefficient (c * t) := by
  have he : 0 < Real.exp t := Real.exp_pos t
  have hd : 0 < 1 + Real.exp t := by positivity
  have hs : 1 - exponentialRatioCoefficient t = Real.exp t / (1 + Real.exp t) := by
    unfold exponentialRatioCoefficient
    field_simp [hd.ne']; ring
  have hdcp : 0 < (1 + Real.exp t) ^ c := Real.rpow_pos_of_pos hd c
  have ha : exponentialRatioCoefficient t ^ c = 1 / (1 + Real.exp t) ^ c := by
    rw [exponentialRatioCoefficient, Real.div_rpow (by norm_num) hd.le, Real.one_rpow]
  have hb : (1 - exponentialRatioCoefficient t) ^ c =
      Real.exp (c * t) / (1 + Real.exp t) ^ c := by
    rw [hs, Real.div_rpow he.le hd.le, ← Real.exp_mul, mul_comm t c]
  rw [powerResolventFunction, ha, hb, exponentialRatioCoefficient]
  have hct : 0 < 1 + Real.exp (c * t) := by positivity
  field_simp [hdcp.ne', hct.ne']


theorem exponentialHilbertOperator_realCFC
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    IsometricContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

local instance :
    IsometricContinuousFunctionalCalculus ℝ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) IsSelfAdjoint :=
  exponentialHilbertOperator_realCFC

/-- View the exponential ratio coefficient as a point of the closed unit interval. -/
noncomputable def exponentialRatioInUnitInterval (w : α → ℝ) (x : α) : Set.Icc (0 : ℝ) 1 :=
  ⟨exponentialRatioCoefficient (w x),
    (exponentialRatioCoefficient_bounds (w x)).1.le,
    (exponentialRatioCoefficient_bounds (w x)).2⟩

theorem measurable_exponentialRatioInUnitInterval (w : α → ℝ) (hw : Measurable w) :
    Measurable (exponentialRatioInUnitInterval w) := by
  unfold exponentialRatioInUnitInterval exponentialRatioCoefficient
  fun_prop

theorem exponentialResolvent_nonneg (w : α → ℝ) (hw : Measurable w) :
    0 ≤ exponentialResolvent μ w hw := by
  apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _
    (exponentialResolvent_isSelfAdjoint μ w hw)).mpr
  intro x hx
  have hs := continuousMultiplier_spectrum_subset μ (exponentialRatioInUnitInterval w)
    (measurable_exponentialRatioInUnitInterval w hw)
  exact (hs hx).1

theorem exponentialResolvent_le_one (w : α → ℝ) (hw : Measurable w) :
    exponentialResolvent μ w hw ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (exponentialResolvent_nonneg μ w hw)).mp
  apply lpMultiplication_norm_le μ _ _ (by norm_num)
  exact Filter.Eventually.of_forall fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (exponentialRatioCoefficient_bounds (w x)).1]
    exact (exponentialRatioCoefficient_bounds (w x)).2

theorem cfc_powerResolventFunction_exponentialResolvent (w : α → ℝ) (hw : Measurable w)
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    cfc (powerResolventFunction c) (exponentialResolvent μ w hw) =
      exponentialResolvent μ (fun x => c * w x) (measurable_const.mul hw) := by
  have he := cfc_continuousMultiplier μ (exponentialRatioInUnitInterval w)
    (measurable_exponentialRatioInUnitInterval w hw) (powerResolventFunction c)
    (continuousOn_powerResolventFunction hc hc1)
  change cfc (powerResolventFunction c) (exponentialResolvent μ w hw) =
    continuousMultiplier μ (exponentialRatioInUnitInterval w)
      (measurable_exponentialRatioInUnitInterval w hw)
      ⟨fun x => powerResolventFunction c x, (continuousOn_powerResolventFunction hc
        hc1).domRestrict⟩ at he
  rw [he]
  apply lpMultiplication_congr
  exact Filter.Eventually.of_forall fun x => by
    change (powerResolventFunction c (exponentialRatioCoefficient (w x)) : ℂ) =
      (exponentialRatioCoefficient (c * w x) : ℂ)
    rw [powerResolventFunction_exponentialRatio]

theorem resolventPowerRatio_exponentialResolvent (w : α → ℝ) (hw : Measurable w)
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    resolventPowerRatio (exponentialResolvent μ w hw) (exponentialResolvent_nonneg μ w hw)
      (exponentialResolvent_injective μ w hw) c hc hc1 =
        exponentialMultiplication μ (fun x => c * w x) (measurable_const.mul hw) := by
  apply partialOperator_eq_of_resolvent _ _
    (exponentialResolvent μ (fun x => c * w x) (measurable_const.mul hw))
  · intro x y
    rw [resolventPowerRatio_resolvent_cfc _ (exponentialResolvent_nonneg μ w hw)
      (exponentialResolvent_le_one μ w hw)]
    erw [cfc_powerResolventFunction_exponentialResolvent μ w hw hc hc1]
  · exact exponentialMultiplication_resolvent μ _ _

end VacuumBellSeparation
