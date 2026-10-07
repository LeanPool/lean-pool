/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCenterLattice

/-!
# Algebra of a weighted cell bound

The dyadic average volume offsets the local energy and lattice costs,
leaving one inverse dyadic factor and a normal Gaussian tail.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The center Gaussian and dyadic factors have a summable common
majorant (`lem:bu-small-time`). -/
theorem bu_short_cell_gaussian_algebra
    (β G b Cw Ce Cg : ℝ)
    (hβ : 0 < β) (hGtan : G ≤ 1 / 16)
    (hGnorm : G ≤ β / 48) (hbβ : b ≤ β / 48)
    (hCw : 0 ≤ Cw) (hCe : 0 ≤ Ce) (hCg : 0 ≤ Cg)
    (k : ℤ) (hk : 1 ≤ k) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (hY : 2 ≤ (Foundation.buSmallTimeDyadicCellCenter k m ell).1 2) :
    let d := Foundation.buSmallTimeDyadicScale k
    let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    let a := (1 : ℝ) / (16 * 16384)
    let b₀ := β / (48 * 16384)
    let K₀ := (Real.exp (a / 4) * (a + 2) / a) ^ 2 *
      (Real.exp (b₀ / 4) * (1 + 2 / b₀))
    (Cw * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
      Real.exp (b * Y 2 ^ 2)) *
      (Ce / d) *
      (Cg * d ^ 2 * Real.exp (G * (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
        Real.exp (-(β * Y 2 ^ 2 / (12 * d)))) ≤
      (Cw * Ce * Cg * K₀) / d *
        Real.exp (-(β / (12 * d))) * buShortSpatialProfile m := by
  dsimp
  let d := Foundation.buSmallTimeDyadicScale k
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  let a : ℝ := 1 / (16 * 16384)
  let b₀ : ℝ := β / (48 * 16384)
  let K₀ : ℝ := (Real.exp (a / 4) * (a + 2) / a) ^ 2 *
    (Real.exp (b₀ / 4) * (1 + 2 / b₀))
  have hd : 0 < d := Foundation.buSmallTimeDyadicScale_pos k
  have hdhalf : d ≤ 1 / 2 := by
    dsimp [d, Foundation.buSmallTimeDyadicScale]
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show -k ≤ (-1 : ℤ) by omega)
    simpa using h
  have hAbs := bu_short_center_gaussian_absorption G b β d Y
    hGtan hGnorm hbβ hβ hd hdhalf hY
  have hLat := bu_short_center_gaussian_le_lattice_profile β hβ k
    (by omega : 0 ≤ k) m ell
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀, a, b₀]; positivity
  have hP : 0 ≤ buShortSpatialProfile m := by
    dsimp [buShortSpatialProfile]
    exact mul_nonneg (bu_short_int_profile_nonneg _)
      (mul_nonneg (bu_short_int_profile_nonneg _)
        (bu_short_int_profile_nonneg _))
  have hLeftCoeff : 0 ≤ Cw * Ce * Cg * d := by positivity
  have hTail : 0 ≤ Real.exp (-(β / (12 * d))) := Real.exp_nonneg _
  have hcoeff : (Ce / d) * (Cg * d ^ 2) = Ce * Cg * d := by
    field_simp
  calc
    _ = (Cw * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
          Real.exp (b * Y 2 ^ 2)) *
        ((Ce / d) * (Cg * d ^ 2)) *
        Real.exp (G * (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
        Real.exp (-(β * Y 2 ^ 2 / (12 * d))) := by ring
    _ = (Cw * Ce * Cg * d) *
        (Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
          Real.exp (b * Y 2 ^ 2) *
          Real.exp (G * (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
          Real.exp (-(β * Y 2 ^ 2 / (12 * d)))) := by rw [hcoeff]; ring
    _ ≤ (Cw * Ce * Cg * d) *
        (Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 16) *
          Real.exp (-(β / (12 * d))) *
          Real.exp (-(β * Y 2 ^ 2 / (48 * d)))) :=
      mul_le_mul_of_nonneg_left hAbs hLeftCoeff
    _ = (Cw * Ce * Cg * d) *
        (Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 16) *
          Real.exp (-(β * Y 2 ^ 2 / (48 * d)))) *
          Real.exp (-(β / (12 * d))) := by ring
    _ ≤ (Cw * Ce * Cg * d) *
        (K₀ / d ^ 2 * buShortSpatialProfile m) *
          Real.exp (-(β / (12 * d))) := by
      gcongr
    _ = (Cw * Ce * Cg * K₀) / d *
          Real.exp (-(β / (12 * d))) * buShortSpatialProfile m := by
      field_simp

end ESS
