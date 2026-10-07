/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPointwiseSplit

/-!
# Squared phase and shell error bound

The scalar heat error square is separated into a phase-gap density, a
spatial shell density, and the lower-time transition density.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

attribute [local instance] Classical.propDecidable

/-- A two-term scalar majorant gives a quadratic error bound with
separate square densities. -/
theorem bu_short_two_term_square
    {e a b x y : ℝ} (he0 : 0 ≤ e)
    (hbound : e ≤ a * (x + y) + b) :
    e ^ 2 ≤ 4 * a ^ 2 * (x ^ 2 + y ^ 2) + 2 * b ^ 2 := by
  have hsum0 : 0 ≤ a * (x + y) + b := he0.trans hbound
  have hsq := (sq_le_sq₀ he0 hsum0).2 hbound
  have hsum : (a * (x + y) + b) ^ 2 ≤
      2 * ((a * (x + y)) ^ 2 + b ^ 2) := by
    nlinarith only [sq_nonneg (a * (x + y) - b)]
  have hxy : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    nlinarith only [sq_nonneg (x - y)]
  have hA : (a * (x + y)) ^ 2 ≤
      2 * a ^ 2 * (x ^ 2 + y ^ 2) := by
    calc
      _ = a ^ 2 * (x + y) ^ 2 := by ring
      _ ≤ a ^ 2 * (2 * (x ^ 2 + y ^ 2)) :=
        mul_le_mul_of_nonneg_left hxy (sq_nonneg a)
      _ = _ := by ring
  nlinarith only [hsq, hsum, hA]

end ESS
