/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# L6 From Gradient

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- If `u` agrees with a `C¹` compactly supported function `g` on a ball of radius `ρ`,
then the `L⁶` norm of `u` on that ball is controlled by the `L²` norm of the gradient of `g`.

This is the key estimate used in the closure argument of `lem:aniso:closure` to bound
local `L⁶` averages by global energy quantities. -/
theorem lintegral_pow_six_le_of_eq_on_ball {C : ℝ} (hC : 0 < C)
    (hsob : ∀ g : Vec3 → ℝ, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm g 6 ≤ ENNReal.ofReal C * eLpNorm (fderiv ℝ g) 2)
    {u g : Vec3 → ℝ} {ρ : ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (heq : ∀ x ∈ vec3Ball 0 ρ, g x = u x) :
    (∫⁻ x in vec3Ball 0 ρ, ENNReal.ofReal |u x| ^ (6 : ℝ)) ^ (1 / 6 : ℝ) ≤
      ENNReal.ofReal C * eLpNorm (fderiv ℝ g) 2 := by
  have h_measBall : MeasurableSet (vec3Ball (0 : Vec3) ρ) :=
    (isOpen_vec3Ball (0 : Vec3) ρ).measurableSet
  have h_ae_g : AEStronglyMeasurable g :=
    hg.continuous.measurable.aestronglyMeasurable
  have h_eq_lintegral : (∫⁻ x in vec3Ball (0 : Vec3) ρ, ENNReal.ofReal |u x| ^ (6 : ℝ)) =
      (∫⁻ x in vec3Ball (0 : Vec3) ρ, ‖g x‖ₑ ^ (6 : ℝ)) := by
    refine setLIntegral_congr_fun h_measBall fun x hx => ?_
    rw [Real.enorm_eq_ofReal_abs, heq x hx]
  have h_int_ball_le_total : (∫⁻ x in vec3Ball (0 : Vec3) ρ, ‖g x‖ₑ ^ (6 : ℝ)) ≤
      (∫⁻ x, ‖g x‖ₑ ^ (6 : ℝ)) :=
    setLIntegral_le_lintegral _ _
  have h_sobolev : eLpNorm g 6 ≤ ENNReal.ofReal C * eLpNorm (fderiv ℝ g) 2 :=
    hsob g hg hgc
  have _hCpos : 0 < ENNReal.ofReal C := ENNReal.ofReal_pos.mpr hC
  have h_eq_on_ball_pow : (∫⁻ x in vec3Ball (0 : Vec3) ρ, ENNReal.ofReal |u x| ^ (6 : ℝ)) ^ (1 /
    6 : ℝ)
      = (∫⁻ x in vec3Ball (0 : Vec3) ρ, ‖g x‖ₑ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) := by rw [h_eq_lintegral]
  have h_ball_le_total : (∫⁻ x in vec3Ball (0 : Vec3) ρ, ‖g x‖ₑ ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
      ≤ (∫⁻ x, ‖g x‖ₑ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) :=
    ENNReal.rpow_le_rpow h_int_ball_le_total (by norm_num : (0 : ℝ) ≤ 1/6)
  have h_total_eq_sobolev : (∫⁻ x, ‖g x‖ₑ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) = eLpNorm g 6 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (6 : ℝ≥0∞) ≠ 0)
      (by norm_num : (6 : ℝ≥0∞) ≠ ∞) h_ae_g]
    norm_num
  exact h_eq_on_ball_pow.trans_le (h_ball_le_total.trans (h_total_eq_sobolev ▸ h_sobolev))

end CIV
