/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShiftedCellCover

/-!
# Distances inside a shifted dyadic cell

Time translation preserves the spatial distance from a cell's midpoint
and shifts its time distance by one half.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The spatial distance from a shifted cell point to its midpoint is
bounded by the cell side length (`lem:bu-small-time`). -/
theorem bu_short_shifted_cell_spatial_distance_le
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (z : ParabolicPoint)
    (hz : z ∈ buShortShiftedDyadicCell k m ell) :
    vec3EuclideanNorm
      (z.1 - (Foundation.buSmallTimeDyadicCellCenter k m ell).1) ≤
      Real.sqrt 3 * Foundation.buSmallTimeDyadicSide k := by
  rcases hz with ⟨q, hq, rfl⟩
  rw [bu_short_time_shift_point_eval]
  exact Foundation.buSmallTimeDyadicCell_spatial_distance_le k m ell q hq

/-- Each coordinate of a shifted cell point is within one sixty-fourth
of its spatial midpoint at nonnegative dyadic levels. -/
theorem bu_short_shifted_cell_coordinate_close
    (k : ℤ) (hk : 0 ≤ k) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (z : ParabolicPoint) (hz : z ∈ buShortShiftedDyadicCell k m ell)
    (i : Fin 3) :
    |z.1 i - (Foundation.buSmallTimeDyadicCellCenter k m ell).1 i| ≤
      1 / 64 := by
  let d := Foundation.buSmallTimeDyadicScale k
  have hdle : d ≤ 1 := by
    dsimp [d, Foundation.buSmallTimeDyadicScale]
    exact zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2)
      (neg_nonpos.mpr hk)
  have hroot : Real.sqrt d ≤ 1 := Real.sqrt_le_one.mpr hdle
  have hthree : Real.sqrt 3 ≤ 2 :=
    (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsmall : Real.sqrt 3 * Foundation.buSmallTimeDyadicSide k ≤
      1 / 64 := by
    change Real.sqrt 3 * (Real.sqrt d / 128) ≤ 1 / 64
    have hmul := mul_le_mul hthree hroot
      (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hmul, Real.sqrt_nonneg d]
  have hdist := bu_short_shifted_cell_spatial_distance_le k m ell z hz
  have hcoord := abs_apply_le_vec3EuclideanNorm
    (z.1 - (Foundation.buSmallTimeDyadicCellCenter k m ell).1) i
  have h := hcoord.trans (hdist.trans hsmall)
  simpa only [Pi.sub_apply] using h

/-- The normal square at a cell point is controlled by twice the
normal square at its midpoint. -/
theorem bu_short_shifted_cell_normal_square_le
    (k : ℤ) (hk : 0 ≤ k) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (z : ParabolicPoint) (hz : z ∈ buShortShiftedDyadicCell k m ell) :
    z.1 2 ^ 2 ≤
      2 * (Foundation.buSmallTimeDyadicCellCenter k m ell).1 2 ^ 2 + 1 := by
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  have hclose := bu_short_shifted_cell_coordinate_close k hk m ell z hz 2
  have hsq : (z.1 2 - Y 2) ^ 2 ≤ (1 / 64 : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 64)).2 hclose
  have hbasic : z.1 2 ^ 2 ≤ 2 * Y 2 ^ 2 +
      2 * (z.1 2 - Y 2) ^ 2 := by
    nlinarith only [sq_nonneg (z.1 2 - 2 * Y 2)]
  nlinarith only [hbasic, hsq]

end ESS
