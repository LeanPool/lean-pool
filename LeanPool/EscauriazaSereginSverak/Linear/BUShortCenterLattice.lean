/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCenterGaussian
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortLatticeProfile3D

/-!
# Cell-center Gaussians on the integer lattice

The dyadic spatial midpoint has a coordinate square proportional to
the dyadic scale and a half-integer square.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Squared coordinates of a dyadic spatial midpoint. -/
theorem bu_short_dyadic_center_coordinate_sq
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048) (i : Fin 3) :
    (Foundation.buSmallTimeDyadicCellCenter k m ell).1 i ^ 2 =
      Foundation.buSmallTimeDyadicScale k / 16384 *
        ((m i : ℝ) + 1 / 2) ^ 2 := by
  let d := Foundation.buSmallTimeDyadicScale k
  have hd : 0 ≤ d := (Foundation.buSmallTimeDyadicScale_pos k).le
  change (((m i : ℝ) + 1 / 2) * (Real.sqrt d / 128)) ^ 2 =
    d / 16384 * ((m i : ℝ) + 1 / 2) ^ 2
  rw [mul_pow, div_pow, Real.sq_sqrt hd]
  ring

/-- The remaining cell-center Gaussian is bounded by a fixed
summable lattice profile with two inverse dyadic powers. -/
theorem bu_short_center_gaussian_le_lattice_profile
    (β : ℝ) (hβ : 0 < β)
    (k : ℤ) (hk : 0 ≤ k) (m : Fin 3 → ℤ) (ell : Fin 2048) :
    let d := Foundation.buSmallTimeDyadicScale k
    let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    let a := (1 : ℝ) / (16 * 16384)
    let b := β / (48 * 16384)
    let K := (Real.exp (a / 4) * (a + 2) / a) ^ 2 *
      (Real.exp (b / 4) * (1 + 2 / b))
    Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 16) *
      Real.exp (-(β * Y 2 ^ 2 / (48 * d))) ≤
        K / d ^ 2 * buShortSpatialProfile m := by
  dsimp
  let d := Foundation.buSmallTimeDyadicScale k
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  let a : ℝ := 1 / (16 * 16384)
  let b : ℝ := β / (48 * 16384)
  let K : ℝ := (Real.exp (a / 4) * (a + 2) / a) ^ 2 *
    (Real.exp (b / 4) * (1 + 2 / b))
  have hd : 0 < d := Foundation.buSmallTimeDyadicScale_pos k
  have hd1 : d ≤ 1 := by
    dsimp [d, Foundation.buSmallTimeDyadicScale]
    exact zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2)
      (neg_nonpos.mpr hk)
  have ha : 0 < a := by dsimp [a]; norm_num
  have hb : 0 < b := by dsimp [b]; positivity
  have hcoord (i : Fin 3) : Y i ^ 2 =
      d / 16384 * ((m i : ℝ) + 1 / 2) ^ 2 :=
    bu_short_dyadic_center_coordinate_sq k m ell i
  have hT0 : -(Y 0 ^ 2 / 16) =
      -(a * d * ((m 0 : ℝ) + 1 / 2) ^ 2) := by
    rw [hcoord]
    dsimp [a]
    ring
  have hT1 : -(Y 1 ^ 2 / 16) =
      -(a * d * ((m 1 : ℝ) + 1 / 2) ^ 2) := by
    rw [hcoord]
    dsimp [a]
    ring
  have hN : -(β * Y 2 ^ 2 / (48 * d)) =
      -(b * ((m 2 : ℝ) + 1 / 2) ^ 2) := by
    rw [hcoord]
    dsimp [b]
    field_simp
  have hTang : Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 16) =
      Real.exp (-(a * d * ((m 0 : ℝ) + 1 / 2) ^ 2)) *
        Real.exp (-(a * d * ((m 1 : ℝ) + 1 / 2) ^ 2)) := by
    have heq : -(Y 0 ^ 2 + Y 1 ^ 2) / 16 =
        -(Y 0 ^ 2 / 16) + -(Y 1 ^ 2 / 16) := by ring
    rw [heq, Real.exp_add, hT0, hT1]
  have hLattice := bu_short_separable_gaussian_le_profile a b d
    ha hb hd hd1 m
  have hScale :
      (Real.exp (a / 4) * (a + 2) / (a * d)) ^ 2 *
        (Real.exp (b / 4) * (1 + 2 / b)) = K / d ^ 2 := by
    dsimp [K]
    field_simp
  rw [hTang, hN]
  calc
    _ = Real.exp (-(a * d * ((m 0 : ℝ) + 1 / 2) ^ 2)) *
        (Real.exp (-(a * d * ((m 1 : ℝ) + 1 / 2) ^ 2)) *
          Real.exp (-(b * ((m 2 : ℝ) + 1 / 2) ^ 2))) := by ring
    _ ≤ ((Real.exp (a / 4) * (a + 2) / (a * d)) ^ 2 *
        (Real.exp (b / 4) * (1 + 2 / b))) *
          buShortSpatialProfile m := hLattice
    _ = K / d ^ 2 * buShortSpatialProfile m := by rw [hScale]

end ESS
