/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellCylinderTime
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Spatial nesting of dyadic and Gaussian cylinders

A rescaled dyadic cube lies in the inner Caccioppoli ball at its center,
and the outer ball lies inside the Gaussian averaging ball.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Spatial points of a dyadic cell map into the inner Caccioppoli ball
at the dyadic midpoint. -/
theorem bu_short_dyadic_cell_space_inner
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (scale : ℝ) (hscale : 0 < scale)
    (z : ParabolicPoint)
    (hz : z ∈ Foundation.buSmallTimeDyadicCell k m ell) :
    let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
    let X := scale • (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    let r := Real.sqrt (scale ^ 2 * δ) / 8
    scale • z.1 ∈ vec3Ball X r := by
  dsimp
  let d := Foundation.buSmallTimeDyadicScale k
  let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
  have hd : 0 < d := Foundation.buSmallTimeDyadicScale_pos k
  have hδ : d / 2 < δ :=
    (bu_short_dyadic_cell_center_time_bounds k m ell).1
  have hδ0 : 0 < δ := (half_pos hd).trans hδ
  have hDsq : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd.le
  have hδsq : (Real.sqrt δ) ^ 2 = δ := Real.sq_sqrt hδ0.le
  have hthree : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hSqrtD : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hSqrtDelta : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hSqrtThree : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hside : Foundation.buSmallTimeDyadicSide k = Real.sqrt d / 128 := rfl
  have hdist := Foundation.buSmallTimeDyadicCell_spatial_distance_le k m ell z hz
  rw [hside] at hdist
  have hsize : Real.sqrt 3 * (Real.sqrt d / 128) < Real.sqrt δ / 8 := by
    have hsq : (Real.sqrt 3 * Real.sqrt d) ^ 2 < (16 * Real.sqrt δ) ^ 2 := by
      rw [mul_pow, hthree, hDsq, mul_pow, hδsq]
      linarith only [hδ, hd]
    have hlt : Real.sqrt 3 * Real.sqrt d < 16 * Real.sqrt δ :=
      (sq_lt_sq₀ (mul_nonneg hSqrtThree hSqrtD) (by positivity)).1 hsq
    linarith only [hlt]
  have hτ : 0 ≤ scale ^ 2 * δ := by positivity
  have hroot : Real.sqrt (scale ^ 2 * δ) = scale * Real.sqrt δ := by
    rw [Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq_eq_abs,
      abs_of_pos hscale]
  change vec3EuclideanNorm (scale • z.1 -
      scale • (Foundation.buSmallTimeDyadicCellCenter k m ell).1) <
    Real.sqrt (scale ^ 2 * δ) / 8
  rw [← smul_sub, vec3EuclideanNorm_smul, abs_of_pos hscale, hroot]
  have hmul := mul_lt_mul_of_pos_left (hdist.trans_lt hsize) hscale
  exact (by nlinarith only [hmul] :
    scale * vec3EuclideanNorm
      (z.1 - (Foundation.buSmallTimeDyadicCellCenter k m ell).1) <
      scale * Real.sqrt δ / 8)

/-- The Caccioppoli outer ball is contained in the Gaussian averaging
ball at the same physical center. -/
theorem bu_short_caccioppoli_outer_space_subset
    (X : Vec3) (τ : ℝ) (hτ : 0 < τ) :
    let r := Real.sqrt τ / 8
    vec3Ball X (2 * r) ⊆ vec3Ball X (Real.sqrt (3 * τ / 2)) := by
  dsimp
  have hroot : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hmul : (2 * (Real.sqrt τ / 8)) ^ 2 <
      (Real.sqrt (3 * τ / 2)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 3 * τ / 2)]
    rw [mul_pow, div_pow, Real.sq_sqrt hτ.le]
    linarith only [hτ]
  have hrad : 2 * (Real.sqrt τ / 8) < Real.sqrt (3 * τ / 2) :=
    (sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg _)).1 hmul
  exact vec3Ball_mono hrad.le

end ESS
