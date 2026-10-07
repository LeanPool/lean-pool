/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSpaceTimeMollify
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Spatial mollification at the `L∞` endpoint

Positive, unit-mass spatial mollification preserves an almost-everywhere
spatial bound. This is the endpoint domination used for the convection
density limit (`lem:lps-comparison`).
-/

public section

open MeasureTheory
open scoped ENNReal Convolution
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A normalized nonnegative spatial mollifier does not increase an
almost-everywhere scalar `L∞` bound. -/
theorem lps_endpoint_mollify_linf_bound
    {f : Vec3 → ℝ} {ε M : ℝ} (hε : 0 < ε)
    (hf : AEStronglyMeasurable f volume)
    (hfBound : ∀ᵐ x ∂volume, |f x| ≤ M) (y : Vec3) :
    |CKN.mollify f ε hε y| ≤ M := by
  let κ : Vec3 → ℝ := CKN.mollifier (d := 3) ε hε
  let κy : Vec3 → ℝ := fun x => κ (y - x)
  have hκcont : Continuous κ :=
    (CKN.mollifier_contDiff (d := 3) hε (n := 0)).continuous
  have hκc : HasCompactSupport κ := CKN.mollifier_hasCompactSupport hε
  have hκycont : Continuous κy := hκcont.comp (continuous_const.sub continuous_id)
  have hκyc : HasCompactSupport κy :=
    hκc.comp_homeomorph (Homeomorph.subLeft y)
  have hκyint : Integrable κy volume := hκycont.integrable_of_hasCompactSupport hκyc
  have hκynonneg : ∀ x, 0 ≤ κy x := fun x => CKN.mollifier_nonneg hε _
  have hκyone : ∫ x : Vec3, κy x = 1 := by
    calc
      ∫ x : Vec3, κy x = ∫ x : Vec3, κ x := by
        rw [show κy = fun x : Vec3 => κ (y - x) from rfl]
        rw [← integral_sub_left_eq_self (fun x : Vec3 => κ x) volume y]
      _ = 1 := CKN.mollifier_integral_one hε
  have hfInf : MemLp f ∞ volume := memLp_top_of_bound hf M hfBound
  have hκy1 : MemLp κy 1 volume := memLp_one_iff_integrable.mpr hκyint
  have htriple : ENNReal.HolderTriple ∞ 1 1 := by
    constructor
    simp
  have hprodMem : MemLp (fun x : Vec3 => f x * κy x) 1 volume :=
    hfInf.mul hκy1 (hpqr := htriple)
  have hprodInt : Integrable (fun x : Vec3 => f x * κy x) volume :=
    memLp_one_iff_integrable.mp hprodMem
  have hdomInt : Integrable (fun x : Vec3 => M * κy x) volume := hκyint.const_mul M
  have hprodLe : ∀ᵐ x ∂volume, f x * κy x ≤ M * κy x := by
    filter_upwards [hfBound] with x hx
    exact mul_le_mul_of_nonneg_right (le_trans (le_abs_self _) hx) (hκynonneg x)
  have hIntLe : ∫ x : Vec3, f x * κy x ≤ M := by
    calc
      ∫ x : Vec3, f x * κy x ≤ ∫ x : Vec3, M * κy x :=
        integral_mono_ae hprodInt hdomInt hprodLe
      _ = M := by rw [integral_const_mul, hκyone, mul_one]
  have hAbsInt : |∫ x : Vec3, f x * κy x| ≤
      ∫ x : Vec3, |f x * κy x| := abs_integral_le_integral_abs
  have hAbsProdInt : ∫ x : Vec3, |f x * κy x| ≤ M := by
    have hAbsProd : Integrable (fun x : Vec3 => |f x * κy x|) volume :=
      hprodInt.abs
    have hAbsDom : Integrable (fun x : Vec3 => M * κy x) volume := hdomInt
    have hLe : ∀ᵐ x ∂volume, |f x * κy x| ≤ M * κy x := by
      filter_upwards [hfBound] with x hx
      rw [abs_mul, abs_of_nonneg (hκynonneg x)]
      exact mul_le_mul_of_nonneg_right hx (hκynonneg x)
    calc
      ∫ x : Vec3, |f x * κy x| ≤ ∫ x : Vec3, M * κy x :=
        integral_mono_ae hAbsProd hAbsDom hLe
      _ = M := by rw [integral_const_mul, hκyone, mul_one]
  rw [serrin_mollify_eq_integral f hε y]
  exact hAbsInt.trans hAbsProdInt

end ESS

end
