/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShiftedCellGeometry

/-!
# Tangential Gaussian on dyadic cells

The tangential Gaussian at any cell point is controlled by a slightly
weaker Gaussian at the spatial midpoint.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A dyadic cell's tangential Gaussian is bounded by its center
Gaussian with half the quadratic exponent (`lem:bu-small-time`). -/
theorem bu_short_tangential_cell_weight_le
    (k : ℤ) (hk : 0 ≤ k) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (z : ParabolicPoint) (hz : z ∈ buShortShiftedDyadicCell k m ell)
    (hs : z.2 ∈ Ioo (1 / 2 : ℝ) 1) :
    let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) ≤
      Real.exp 1 * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) := by
  dsimp
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  have h0 := bu_short_shifted_cell_coordinate_close k hk m ell z hz 0
  have h1 := bu_short_shifted_cell_coordinate_close k hk m ell z hz 1
  have h0sq : (z.1 0 - Y 0) ^ 2 ≤ (1 / 64 : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 64)).2 h0
  have h1sq : (z.1 1 - Y 1) ^ 2 ≤ (1 / 64 : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 64)).2 h1
  have hY0 : Y 0 ^ 2 ≤ 2 * z.1 0 ^ 2 + 2 * (z.1 0 - Y 0) ^ 2 := by
    nlinarith only [sq_nonneg (2 * z.1 0 - Y 0)]
  have hY1 : Y 1 ^ 2 ≤ 2 * z.1 1 ^ 2 + 2 * (z.1 1 - Y 1) ^ 2 := by
    nlinarith only [sq_nonneg (2 * z.1 1 - Y 1)]
  have hZ : (Y 0 ^ 2 + Y 1 ^ 2) / 2 - 1 ≤
      z.1 0 ^ 2 + z.1 1 ^ 2 := by
    nlinarith only [hY0, hY1, h0sq, h1sq]
  have hnum : 0 ≤ z.1 0 ^ 2 + z.1 1 ^ 2 := by positivity
  have hden : 0 < 4 * z.2 := by linarith only [hs.1]
  have hdiv : (z.1 0 ^ 2 + z.1 1 ^ 2) / 4 ≤
      (z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2) := by
    apply (le_div_iff₀ hden).2
    have hmul := mul_le_mul_of_nonneg_left hs.2.le hnum
    nlinarith only [hmul]
  have harg : -(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2) ≤
      1 - (Y 0 ^ 2 + Y 1 ^ 2) / 8 := by
    have hneg : -(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2) =
        -((z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) := by ring
    rw [hneg]
    linarith only [hZ, hdiv]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert harg using 1; ring

end ESS
