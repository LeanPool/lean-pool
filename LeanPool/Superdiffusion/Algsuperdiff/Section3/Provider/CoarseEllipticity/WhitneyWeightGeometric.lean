/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# WhitneyWeightGeometric

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

/-- The fixed geometric ratio left after paying the Whitney-layer growth. -/
noncomputable def whitneyDecayRatio : ℝ :=
  (3 : ℝ) ^ (-(1 / 8 : ℝ))

theorem whitneyDecayRatio_nonneg : 0 ≤ whitneyDecayRatio := by
  rw [whitneyDecayRatio]
  exact Real.rpow_nonneg (by norm_num) _

theorem whitneyDecayRatio_lt_one : whitneyDecayRatio < 1 := by
  rw [whitneyDecayRatio]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem norm_whitneyDecayRatio_lt_one : ‖whitneyDecayRatio‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg whitneyDecayRatio_nonneg]
  exact whitneyDecayRatio_lt_one

/-- If `b ≤ 1/64`, `gamma ≤ b`, and the layer gap is at most `2n+1`, then
the growing factor spends at most half of the available `3^{-n/4}` decay. -/
theorem weighted_whitney_layer_factor_le
    {b gamma : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 64)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ b)
    (n g : ℕ) (hgap : g ≤ 2 * n + 1) :
    (3 : ℝ) ^ (-(n : ℝ) / 4) *
        (3 : ℝ) ^ (2 * (b + gamma) * (g : ℝ)) ≤
      (3 : ℝ) ^ (1 / 16 : ℝ) * whitneyDecayRatio ^ n := by
  have hcoef0 : 0 ≤ 2 * (b + gamma) := by linarith
  have hcoef : 2 * (b + gamma) ≤ (1 / 16 : ℝ) := by linarith
  have hgapReal : (g : ℝ) ≤ 2 * (n : ℝ) + 1 := by
    exact_mod_cast hgap
  have hgrowth :
      2 * (b + gamma) * (g : ℝ) ≤
        (1 / 16 : ℝ) * (2 * (n : ℝ) + 1) := by
    calc
      2 * (b + gamma) * (g : ℝ) ≤
          2 * (b + gamma) * (2 * (n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hgapReal hcoef0
      _ ≤ (1 / 16 : ℝ) * (2 * (n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hexponent :
      -(n : ℝ) / 4 + 2 * (b + gamma) * (g : ℝ) ≤
        (1 / 16 : ℝ) + (-(1 / 8 : ℝ)) * (n : ℝ) := by
    linarith
  have hthree : (0 : ℝ) < 3 := by norm_num
  have hlhs :
      (3 : ℝ) ^ (-(n : ℝ) / 4) *
          (3 : ℝ) ^ (2 * (b + gamma) * (g : ℝ)) =
        (3 : ℝ) ^
          (-(n : ℝ) / 4 + 2 * (b + gamma) * (g : ℝ)) := by
    rw [← Real.rpow_add hthree]
  have hrhs :
      (3 : ℝ) ^ (1 / 16 : ℝ) * whitneyDecayRatio ^ n =
        (3 : ℝ) ^ ((1 / 16 : ℝ) + (-(1 / 8 : ℝ)) * (n : ℝ)) := by
    rw [whitneyDecayRatio, ← Real.rpow_natCast,
      ← Real.rpow_mul hthree.le, ← Real.rpow_add hthree]
  rw [hlhs, hrhs]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

/-- Polynomially weighted copies of the fixed layer ratio are summable. -/
theorem summable_succ_mul_whitneyDecayRatio :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * whitneyDecayRatio ^ n) := by
  have hpoly :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      norm_whitneyDecayRatio_lt_one
  have hgeom : Summable (fun n : ℕ => whitneyDecayRatio ^ n) :=
    summable_geometric_of_norm_lt_one norm_whitneyDecayRatio_lt_one
  simpa only [pow_one, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
    hpoly.add hgeom

/-- Exact geometric sum for the `(n+1)`-weighted layer ratio. -/
theorem hasSum_succ_mul_whitneyDecayRatio :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * whitneyDecayRatio ^ n)
      (1 / (1 - whitneyDecayRatio) ^ 2) := by
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, Nat.reduceAdd]
    using
      (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
        norm_whitneyDecayRatio_lt_one)

end Algsuperdiff.Section3.Provider.CoarseEllipticity
