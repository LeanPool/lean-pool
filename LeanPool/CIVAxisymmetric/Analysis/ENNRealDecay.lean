/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# ENNReal Decay

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Filter Topology


noncomputable section

namespace CIV

/-- The limit of `C * |t|^(-kap)` as `t → -∞` is `0` in `ℝ≥0∞`, for any real `C` and
positive exponent `kap`. -/
theorem tendsto_ofReal_mul_abs_rpow_neg_atBot (C : ℝ) {kap : ℝ} (hkap : 0 < kap) :
    Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (C * |t| ^ (-kap))) Filter.atBot (nhds 0) := by
  have h_abs : Filter.Tendsto (fun t : ℝ => |t|) Filter.atBot Filter.atTop :=
    tendsto_abs_atBot_atTop
  have h_rpow : Filter.Tendsto (fun t : ℝ => |t| ^ (-kap)) Filter.atBot (nhds 0) :=
    (tendsto_rpow_neg_atTop hkap).comp h_abs
  have h_mul : Filter.Tendsto (fun t : ℝ => C * (|t| ^ (-kap))) Filter.atBot (nhds (C * 0)) :=
    Filter.Tendsto.const_mul C h_rpow
  have h_mul_zero : C * (0 : ℝ) = 0 := by ring
  rw [h_mul_zero] at h_mul
  have h_ofReal : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (C * (|t| ^ (-kap)))) Filter.atBot
      (nhds (ENNReal.ofReal 0)) :=
    ENNReal.tendsto_ofReal h_mul
  simpa [ENNReal.ofReal_zero] using h_ofReal

/-- If `a ≤ g n` for all `n` and `g n → 0`, then `a = 0` in `ℝ≥0∞`. -/
theorem eq_zero_of_le_of_tendsto_zero {a : ENNReal} {g : ℕ → ENNReal}
    (h : ∀ n, a ≤ g n) (hg : Filter.Tendsto g Filter.atTop (nhds 0)) : a = 0 := by
  have h_le : 0 ≤ a := bot_le (a := a)
  have h_ge : a ≤ 0 := ge_of_tendsto hg (Filter.Eventually.of_forall h)
  exact le_antisymm h_ge h_le

end CIV
