/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.Meridional
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Setting.RotationLemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Time weights

Derivatives and integrals of functions of `-s` for `s < 0`. These appear in the
proof of the time-weighted energy inequality (`lem:aniso:closure` in the paper).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- The derivative of `s ↦ (-s)^η` at a negative point `t`. -/
theorem hasDerivAt_neg_rpow {η t : ℝ} (ht : t < 0) :
    HasDerivAt (fun s : ℝ => (-s) ^ η) (-(η * (-t) ^ (η - 1))) t := by
  have hpos : -t ≠ 0 := by linarith only [ht]
  have hderiv_neg : HasDerivAt (fun s : ℝ => -s) (-1) t := by
    simpa using hasDerivAt_neg t
  have hchain := hderiv_neg.rpow_const (p := η) (Or.inl hpos)
  -- hchain : HasDerivAt (fun s => (-s) ^ η) ((-1) * η * (-t) ^ (η - 1)) t
  simpa [mul_comm, mul_left_comm, mul_assoc] using hchain

/-- Integral of `(-s)⁻¹` over `[a, b]` for `a < b < 0`. -/
theorem integral_inv_neg {a b : ℝ} (ha : a < b) (hb : b < 0) :
    ∫ s in a..b, (-s)⁻¹ = Real.log (-a) - Real.log (-b) := by
  have ha_neg : a < 0 := lt_trans ha hb
  have ha_pos : 0 < -a := neg_pos.mpr ha_neg
  have hb_pos : 0 < -b := neg_pos.mpr hb
  calc
    ∫ s in a..b, (-s)⁻¹ = ∫ s in (-b)..(-a), s⁻¹ := by
      simpa using intervalIntegral.integral_comp_neg (f := fun x => x⁻¹) (a := a) (b := b)
    _ = Real.log ((-a) / (-b)) := by rw [integral_inv_of_pos hb_pos ha_pos]
    _ = Real.log (-a) - Real.log (-b) := by rw [Real.log_div ha_pos.ne' hb_pos.ne']

/-- Integral of `(-s)^(-β)` over `[a, b]` for `a < b ≤ 0` and `β < 1`. -/
theorem integral_neg_rpow {a b β : ℝ} (ha : a < b) (hb : b ≤ 0) (hβ : β < 1) :
    ∫ s in a..b, (-s) ^ (-β) = ((-a) ^ (1 - β) - (-b) ^ (1 - β)) / (1 - β) := by
  have h_exp_gt : -1 < -β := by linarith only [hβ]
  have ha_neg : a < 0 := lt_of_lt_of_le ha hb
  have ha_pos : 0 < -a := neg_pos.mpr ha_neg
  have hb_nonneg : 0 ≤ -b := neg_nonneg.mpr hb
  calc
    ∫ s in a..b, (-s) ^ (-β) = ∫ s in (-b)..(-a), s ^ (-β) := by
      simpa using intervalIntegral.integral_comp_neg (f := fun x => x ^ (-β)) (a := a) (b := b)
    _ = (((-a) ^ ((-β) + 1) - (-b) ^ ((-β) + 1)) / ((-β) + 1)) := by
      rw [integral_rpow (Or.inl h_exp_gt)]
    _ = ((-a) ^ (1 - β) - (-b) ^ (1 - β)) / (1 - β) := by ring_nf

/-- Exponential of the integral of `c * (-s)⁻¹` over `[a, b]` for `a < b < 0` and `c ≥ 0`. -/
theorem exp_integral_inv_neg {a b c : ℝ} (ha : a < b) (hb : b < 0) (hc : 0 ≤ c) :
    Real.exp (∫ s in a..b, c * (-s)⁻¹) = ((-a) / (-b)) ^ c := by
  have ha_neg : a < 0 := lt_trans ha hb
  have ha_pos : 0 < -a := neg_pos.mpr ha_neg
  have hb_pos : 0 < -b := neg_pos.mpr hb
  have hpos : 0 < (-a) / (-b) := div_pos ha_pos hb_pos
  have hc_nonneg : 0 ≤ c := hc
  calc
    Real.exp (∫ s in a..b, c * (-s)⁻¹) = Real.exp (c * (∫ s in a..b, (-s)⁻¹)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = Real.exp (c * (Real.log (-a) - Real.log (-b))) := by rw [integral_inv_neg ha hb]
    _ = Real.exp (c * Real.log ((-a) / (-b))) := by
      rw [Real.log_div ha_pos.ne' hb_pos.ne']
    _ = Real.exp (Real.log ((-a) / (-b)) * c) := by ring_nf
    _ = ((-a) / (-b)) ^ c := by
      rw [Real.rpow_def_of_pos hpos c]

end CIV
