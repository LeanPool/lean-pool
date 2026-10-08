/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Dyadic Gaussian decay

Any fixed polynomial factor in the dyadic index is dominated by the
normal Gaussian decay used in `lem:bu-small-time`.
-/

public section


open Filter
open scoped Topology

noncomputable section

namespace ESS

/-- A polynomial in the dyadic spatial scale times a normal Gaussian
tail is summable (`lem:bu-small-time`). -/
theorem bu_short_dyadic_gaussian_summable
    (N : ℕ) (c : ℝ) (hc : 0 < c) :
    Summable (fun k : ℕ => (2 : ℝ) ^ (N * k) *
      Real.exp (-(c * (2 : ℝ) ^ k))) := by
  let f : ℕ → ℝ := fun k => (2 : ℝ) ^ (N * k) *
    Real.exp (-(c * (2 : ℝ) ^ k))
  have hfpos (k : ℕ) : 0 < f k := by dsimp [f]; positivity
  have hratio (k : ℕ) : f (k + 1) / f k =
      (2 : ℝ) ^ N * Real.exp (-(c * (2 : ℝ) ^ k)) := by
    have hpow : (2 : ℝ) ^ (N * (k + 1)) =
        (2 : ℝ) ^ N * (2 : ℝ) ^ (N * k) := by
      have hnk : N * (k + 1) = N + N * k := by ring
      rw [hnk, pow_add]
    have hdouble : -(c * (2 : ℝ) ^ (k + 1)) =
        -(c * (2 : ℝ) ^ k) + -(c * (2 : ℝ) ^ k) := by
      rw [pow_succ]
      ring
    dsimp [f]
    rw [hpow, hdouble, Real.exp_add]
    field_simp [show (2 : ℝ) ^ (N * k) ≠ 0 by positivity,
      Real.exp_ne_zero]
  have hpowTop : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hnegBot : Tendsto (fun k : ℕ =>
      -(c * (2 : ℝ) ^ k)) atTop atBot := by
    simpa only [neg_mul] using
      hpowTop.const_mul_atTop_of_neg (neg_lt_zero.mpr hc)
  have hexp : Tendsto (fun k : ℕ =>
      Real.exp (-(c * (2 : ℝ) ^ k))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hnegBot
  have hratioTendsto : Tendsto (fun k : ℕ =>
      ‖f (k + 1)‖ / ‖f k‖) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ =>
        (2 : ℝ) ^ N * Real.exp (-(c * (2 : ℝ) ^ k)))
        atTop (𝓝 ((2 : ℝ) ^ N * 0)) :=
      tendsto_const_nhds.mul hexp
    convert h using 1
    · funext k
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (hfpos (k + 1)), abs_of_pos (hfpos k), hratio]
    · simp
  have hfne : ∀ᶠ k : ℕ in atTop, f k ≠ 0 :=
    Filter.Eventually.of_forall (fun k => ne_of_gt (hfpos k))
  exact summable_of_ratio_test_tendsto_lt_one
    (by norm_num : (0 : ℝ) < 1) hfne hratioTendsto

end ESS
