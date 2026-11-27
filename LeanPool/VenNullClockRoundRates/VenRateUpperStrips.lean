/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt module imports and source presentation. -/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Positive and negative strips for the two-layer discrepancy in Cartesian coordinates. -/

@[expose] public section

namespace VenRateUpper

/-- First-axis energy in upper-hemisphere disk coordinates. -/
noncomputable def chartEnergy (x : ℝ) : ℝ := (1 - x ^ 2) ^ 2

/-- Difference of the downstream exponential weights in the disk chart. -/
noncomputable def chartGap (θ b x y : ℝ) : ℝ :=
  Real.exp (b * chartEnergy (Real.cos θ * x + Real.sin θ * y)) -
    Real.exp (b * chartEnergy x)

private theorem chartEnergy_antitone {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 1) (h : u < v) :
    chartEnergy v < chartEnergy u := by
  have h₁ : u ^ 2 < v ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h) (show 0 < v + u by linarith)]
  have hu1 : u ≤ 1 := h.le.trans hv
  have h₂ : 0 ≤ 1 - v ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv) (show 0 ≤ 1 + v by linarith)]
  unfold chartEnergy
  apply (sq_lt_sq₀ h₂ (by linarith only [h₁, h₂])).2
  linarith only [h₁]

theorem opposite_chart_points {θ b : ℝ} (hθ : 0 < 1 - Real.cos θ ^ 2) (hb : 0 < b) :
    ∃ x yp ym : ℝ, x ∈ Set.Ioo 0 1 ∧ x ^ 2 + yp ^ 2 < 1 ∧ x ^ 2 + ym ^ 2 < 1 ∧
      0 < chartGap θ b x yp ∧ chartGap θ b x ym < 0 := by
  let s := Real.sin θ
  let c := Real.cos θ
  have trig : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hs : s ≠ 0 := by
    intro heq
    rw [heq] at trig
    change 0 < 1 - c ^ 2 at hθ
    nlinarith
  have hs2 : 0 < s ^ 2 := sq_pos_of_ne_zero hs
  have hs2' : s ^ 2 ≤ 1 := by nlinarith only [trig, sq_nonneg c]
  let k := (1 - c) / s
  have hk : s * k = 1 - c := by
    dsimp [k]
    rw [← mul_div_assoc, mul_comm s (1 - c), mul_div_cancel_right₀ _ hs]
  let x := 1 / (8 * (1+|k|))
  have hx : 0 < x := by dsimp [x]; positivity
  have hxmul : x * (8 * (1+|k|)) = 1 := by
    dsimp [x]
    exact div_mul_cancel₀ _ (by positivity)
  have hx8 : x ≤ 1 / 8 := by nlinarith only [hxmul, mul_nonneg hx.le (abs_nonneg k)]
  have hbase : |x * k| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_pos hx]
    nlinarith only [hxmul, hx]
  let δ := x / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδb : δ ≤ 1 / 32 := by dsimp [δ]; linarith only [hx8]
  have hss : |s| ≤ 1 := Real.abs_sin_le_one θ
  have hsd : |s * δ| ≤ 1 / 32 := by
    rw [abs_mul, abs_of_pos hδ]
    exact (mul_le_of_le_one_left hδ.le hss).trans hδb
  let yp := x * k - s * δ
  let ym := x * k + s * δ
  have hyp : |yp| ≤ 1 / 4 := by
    dsimp [yp]
    exact (abs_sub _ _).trans (by linarith only [hbase, hsd])
  have hym : |ym| ≤ 1 / 4 := by
    dsimp [ym]
    exact (abs_add_le _ _).trans (by linarith only [hbase, hsd])
  have disk (y : ℝ) (hy : |y| ≤ 1 / 4) : x ^ 2 + y ^ 2 < 1 := by
    have hxx : x ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ hx.le hx8 _
    have hyy : |y|^2 ≤ (1 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hy _
    rw [sq_abs] at hyy
    linarith only [hxx, hyy]
  have hpp : c * x + s * yp = x - s ^ 2 * δ := by
    dsimp [yp]
    calc
      _ = c * x + x * (s * k) - s ^ 2 * δ := by ring
      _ = _ := by rw [hk]; ring
  have hpm : c * x + s * ym = x + s ^ 2 * δ := by
    dsimp [ym]
    calc
      _ = c * x + x * (s * k) + s ^ 2 * δ := by ring
      _ = _ := by rw [hk]; ring
  have hvpos : 0 < s ^ 2 * δ := mul_pos hs2 hδ
  have hvbound : s ^ 2 * δ ≤ x / 4 := by
    exact mul_le_of_le_one_left hδ.le hs2'
  have hc₁ : chartEnergy x < chartEnergy (c * x + s * yp) := by
    rw [hpp]
    exact chartEnergy_antitone (by linarith only [hx, hvbound]) (by linarith only [hx8])
      (by linarith only [hvpos])
  have hc₂ : chartEnergy (c * x + s * ym) < chartEnergy x := by
    rw [hpm]
    exact chartEnergy_antitone hx.le (by linarith only [hx8, hvbound]) (by linarith only [hvpos])
  refine ⟨x, yp, ym,⟨hx, by linarith only [hx8]⟩, disk _ hyp, disk _ hym,?_⟩
  constructor
  · exact sub_pos.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hc₁ hb))
  · exact sub_neg.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hc₂ hb))

end VenRateUpper
