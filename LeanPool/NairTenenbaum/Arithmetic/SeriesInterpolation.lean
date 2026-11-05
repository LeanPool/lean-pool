/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Analysis.MeanInequalities

/-! # Interpolation of nonnegative convergent series -/

@[expose] public section

namespace NairTenenbaum

theorem summable_and_tsum_mul_rpow_le {ι : Type*} (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hsf : Summable f) (hsg : Summable g) {a : ℝ} (ha : 0 < a) (ha₁ : a < 1) :
    (Summable (fun i => f i ^ a * g i ^ (1 - a))) ∧
      (∑' i, f i ^ a * g i ^ (1 - a)) ≤ (∑' i, f i) ^ a * (∑' i, g i) ^ (1 - a) := by
  have hb : 0 < 1 - a := sub_pos.mpr ha₁
  have hf' (i : ι) : (f i ^ a) ^ a⁻¹ = f i := by
    rw [← Real.rpow_mul (hf i), mul_inv_cancel₀ ha.ne', Real.rpow_one]
  have hg' (i : ι) : (g i ^ (1 - a)) ^ (1 - a)⁻¹ = g i := by
    rw [← Real.rpow_mul (hg i), mul_inv_cancel₀ hb.ne', Real.rpow_one]
  have H := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (Real.HolderConjugate.inv_one_sub_inv ha ha₁)
    (fun i => Real.rpow_nonneg (hf i) a) (fun i => Real.rpow_nonneg (hg i) (1 - a))
    (by simpa only [hf'] using hsf) (by simpa only [hg'] using hsg)
  simpa only [hf', hg', one_div, inv_inv] using H

end NairTenenbaum
