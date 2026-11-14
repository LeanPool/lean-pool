/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Linarith

/-!
# Supporting lines on a finite moment domain

A local derivative at zero controls every point of a convex domain containing
zero. No finiteness of moments outside that domain is required.
-/

@[expose] public section

open Set

namespace EhrhardGaussian.GaussianConvexity

/-- The supporting-line inequality at zero restricted to the convex domain. -/
theorem supporting_line_at_zero_on {s : Set ℝ} {f : ℝ → ℝ} {d : ℝ}
    (hf : ConvexOn ℝ s f) (h0 : 0 ∈ s) (hd : HasDerivAt f d 0)
    {q : ℝ} (hq : q ∈ s) : f 0 + d * q ≤ f q := by
  rcases lt_trichotomy q 0 with hlt | rfl | hgt
  · have hs := hf.slope_le_of_hasDerivAt hq h0 hlt hd
    rw [slope_def_field] at hs
    have hs' := (div_le_iff₀ (sub_pos.mpr hlt)).mp hs
    linarith only [hs']
  · rw [mul_zero, add_zero]
  · have hs := hf.le_slope_of_hasDerivAt h0 hq hgt hd
    rw [slope_def_field] at hs
    have hs' := (le_div_iff₀ (sub_pos.mpr hgt)).mp hs
    linarith only [hs']

/-- The midpoint inequality at orders zero, one and two on the finite domain. -/
theorem neg_zero_le_two_on_of_one_eq_zero {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) (h0 : 0 ∈ s) (h2 : 2 ∈ s) (h1 : f 1 = 0) :
    -f 0 ≤ f 2 := by
  have h := hf.2 h0 h2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  norm_num only [smul_eq_mul, mul_zero, one_div, invOf_eq_inv,
    inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), zero_add] at h
  rw [h1] at h
  linarith only [h]

end EhrhardGaussian.GaussianConvexity
