/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt

/-!
# Absorption of the normal phase

A fixed multiple of the three-halves power is bounded above by an
arbitrarily small quadratic term plus a constant.
-/

public section


noncomputable section

namespace ESS

/-- The three-halves power is the product of height and its square root
at nonnegative height. -/
theorem bu_short_rpow_three_halves_eq_mul_sqrt
    (y : ℝ) (hy : 0 ≤ y) :
    y ^ (3 / 2 : ℝ) = y * Real.sqrt y := by
  have hexp : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
  rw [hexp, Real.rpow_add_of_nonneg hy (by norm_num) (by norm_num)]
  simp only [Real.rpow_one, Real.sqrt_eq_rpow]

/-- Any fixed normal three-halves phase is absorbed by a positive
quadratic Gaussian, up to a finite constant (`lem:bu-small-time`). -/
theorem bu_short_subquadratic_bound
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : ℝ, 0 ≤ y → a * y ^ (3 / 2 : ℝ) ≤ b * y ^ 2 / 2 + C := by
  let T := 2 * a / b
  let R := max 1 (T ^ 2)
  let C := a * R ^ (3 / 2 : ℝ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hR : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hTR : T ^ 2 ≤ R := le_max_right _ _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro y hy
  by_cases hyR : y ≤ R
  · have hpow := Real.rpow_le_rpow hy hyR
        (by norm_num : (0 : ℝ) ≤ 3 / 2)
    have hmul := mul_le_mul_of_nonneg_left hpow ha
    have hquad : 0 ≤ b * y ^ 2 / 2 := by positivity
    exact hmul.trans (le_add_of_nonneg_left hquad)
  · have hRy : R < y := lt_of_not_ge hyR
    have hTysq : T ^ 2 ≤ y := hTR.trans hRy.le
    have hroot : T ≤ Real.sqrt y := by
      apply (sq_le_sq₀ hT (Real.sqrt_nonneg y)).1
      rw [Real.sq_sqrt hy]
      exact hTysq
    have hcoef : a ≤ b * Real.sqrt y / 2 := by
      have hmul := mul_le_mul_of_nonneg_right hroot
        (show 0 ≤ b / 2 by positivity)
      have hleft : T * (b / 2) = a := by
        dsimp [T]
        field_simp
      rw [hleft] at hmul
      nlinarith only [hmul]
    have hmul := mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg hy (Real.sqrt_nonneg y))
    have hrootSq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
    rw [bu_short_rpow_three_halves_eq_mul_sqrt y hy]
    have hident : b * Real.sqrt y / 2 * (y * Real.sqrt y) =
        b * y ^ 2 / 2 := by
      calc
        _ = (b * y / 2) * (Real.sqrt y) ^ 2 := by ring
        _ = b * y ^ 2 / 2 := by rw [hrootSq]; ring
    have hfinal : a * (y * Real.sqrt y) ≤ b * y ^ 2 / 2 :=
      hmul.trans_eq hident
    exact hfinal.trans (le_add_of_nonneg_right hC)

end ESS
