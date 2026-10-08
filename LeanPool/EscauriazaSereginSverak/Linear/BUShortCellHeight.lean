/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortAverageGradient
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortSupportHeight

/-!
# Normal height of Gaussian cell centers

Cells meeting the high normal strip have centers far enough above the
boundary for their averaging balls to remain in the positive half-space.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A Euclidean ball stays above the boundary when its center height
exceeds its radius. -/
theorem bu_short_ball_subset_halfspace
    (X : Vec3) (R : ℝ) (hX : R < X 2) :
    vec3Ball X R ⊆ {x : Vec3 | 0 < x 2} := by
  intro y hy
  have hcoord := abs_apply_le_vec3EuclideanNorm (y - X) 2
  have hdist : vec3EuclideanNorm (y - X) < R := hy
  have hlow : -R < y 2 - X 2 := by
    have h1 : -(vec3EuclideanNorm (y - X)) ≤ y 2 - X 2 :=
      (neg_le_neg hcoord).trans (neg_abs_le _)
    exact (neg_lt_neg hdist).trans_le h1
  change 0 < y 2
  linarith only [hX, hlow]

/-- The center of a cell meeting the high normal strip has physical
height greater than two. -/
theorem bu_short_dyadic_center_height_gt_two
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (scale : ℝ) (hscale : 0 < scale)
    (hk : 0 ≤ k) (z : ParabolicPoint)
    (hz : z ∈ Foundation.buSmallTimeDyadicCell k m ell)
    (hheight : buShortYMinus scale ≤ z.1 2) :
    2 < (scale • (Foundation.buSmallTimeDyadicCellCenter k m ell).1) 2 := by
  let d := Foundation.buSmallTimeDyadicScale k
  have hd : 0 < d := Foundation.buSmallTimeDyadicScale_pos k
  have hdle : d ≤ 1 := by
    dsimp [d, Foundation.buSmallTimeDyadicScale]
    exact zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (neg_nonpos.mpr hk)
  have hdist := Foundation.buSmallTimeDyadicCell_spatial_distance_le k m ell z hz
  have hcoord := abs_apply_le_vec3EuclideanNorm
    (z.1 - (Foundation.buSmallTimeDyadicCellCenter k m ell).1) 2
  have hside : Foundation.buSmallTimeDyadicSide k = Real.sqrt d / 128 := rfl
  have hroot : Real.sqrt d ≤ 1 := Real.sqrt_le_one.mpr hdle
  have hthree : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hsmall : Real.sqrt 3 * Foundation.buSmallTimeDyadicSide k ≤ 1 / 64 := by
    rw [hside]
    calc
      _ ≤ 2 * (1 / 128 : ℝ) := by gcongr
      _ = 1 / 64 := by norm_num
  have hcenter : z.1 2 -
      (Foundation.buSmallTimeDyadicCellCenter k m ell).1 2 ≤ 1 / 64 := by
    have h := (le_abs_self _).trans (hcoord.trans (hdist.trans hsmall))
    simpa only [Pi.sub_apply] using h
  change 2 < scale * (Foundation.buSmallTimeDyadicCellCenter k m ell).1 2
  have hminus : 3 / scale + 1 ≤ z.1 2 := hheight
  have hscalePos : 0 < scale := hscale
  have hmul := mul_le_mul_of_nonneg_left hminus hscale.le
  field_simp at hmul
  nlinarith only [hmul, hcenter, hscale]

end ESS

noncomputable section

namespace ESS

/-- A cell meeting the high strip has an averaging center and ball
inside the positive half-space. -/
theorem bu_short_dyadic_center_average_geometry
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (scale : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hk : 1 ≤ k) (z : ParabolicPoint)
    (hz : z ∈ Foundation.buSmallTimeDyadicCell k m ell)
    (hheight : buShortYMinus scale ≤ z.1 2) :
    let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
    2 < (scale • Y) 2 ∧ δ < 1 / 2 ∧
      vec3Ball Y (Real.sqrt (3 * δ / 2)) ⊆ {x : Vec3 | 0 < x 2} ∧
      vec3Ball Y (2 * (Real.sqrt δ / 8)) ⊆ {x : Vec3 | 0 < x 2} := by
  dsimp
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
  let d := Foundation.buSmallTimeDyadicScale k
  have hcenter : 2 < (scale • Y) 2 :=
    bu_short_dyadic_center_height_gt_two k m ell scale hscale
      (by linarith only [hk]) z hz hheight
  have hdhalf : d ≤ 1 / 2 := by
    dsimp [d, Foundation.buSmallTimeDyadicScale]
    have hexp : -k ≤ (-1 : ℤ) := by omega
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
    simpa using h
  have hδhalf : δ < 1 / 2 :=
    (bu_short_dyadic_cell_center_time_bounds k m ell).2.trans_le hdhalf
  have hδpos : 0 < δ := by
    have h := (bu_short_dyadic_cell_center_time_bounds k m ell).1
    exact (half_pos (Foundation.buSmallTimeDyadicScale_pos k)).trans h
  have hYpos : 0 < Y 2 := by
    have hprod : 0 < scale * Y 2 := by
      simpa only [Pi.smul_apply, smul_eq_mul] using
        lt_trans (by norm_num : (0 : ℝ) < 2) hcenter
    exact (mul_pos_iff_of_pos_left hscale).mp hprod
  have hY : 2 < Y 2 := by
    have hprod : scale * Y 2 ≤ Y 2 :=
      mul_le_of_le_one_left hYpos.le hscale1
    exact hcenter.trans_le hprod
  have hrad : Real.sqrt (3 * δ / 2) < 1 := by
    have hsq : (Real.sqrt (3 * δ / 2)) ^ 2 < 1 ^ 2 := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 3 * δ / 2)]
      linarith only [hδhalf]
    exact (sq_lt_sq₀ (Real.sqrt_nonneg _) (by norm_num)).1 hsq
  have hAvgBall : vec3Ball Y (Real.sqrt (3 * δ / 2)) ⊆
      {x : Vec3 | 0 < x 2} :=
    bu_short_ball_subset_halfspace Y _ (hrad.trans ((by norm_num : (1 : ℝ) < 2).trans hY))
  have hOuterBall := (bu_short_caccioppoli_outer_space_subset Y δ hδpos).trans hAvgBall
  exact ⟨hcenter, hδhalf, hAvgBall, hOuterBall⟩

end ESS
