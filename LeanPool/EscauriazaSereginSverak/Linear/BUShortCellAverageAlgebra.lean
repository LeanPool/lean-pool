/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortDyadicScaleRewrite

/-!
# From Gaussian averages to summable cell bounds

The local energy estimate and Gaussian average produce the dyadic
normal tail required for summing all short-time cells.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A cell integral bounded by its Gaussian velocity average has a
summable lattice majorant (`lem:bu-small-time`). -/
theorem bu_short_cell_average_algebra
    (β G b Cw Ce Cg I Avg : ℝ)
    (hβ : 0 < β) (hGtan : G ≤ 1 / 16)
    (hGnorm : G ≤ β / 48) (hbβ : b ≤ β / 48)
    (hCw : 0 ≤ Cw) (hCe : 0 ≤ Ce) (hCg : 0 ≤ Cg)
    (k : ℤ) (hk : 1 ≤ k) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (hY : 2 ≤ (Foundation.buSmallTimeDyadicCellCenter k m ell).1 2)
    (hI : I ≤
      let d := Foundation.buSmallTimeDyadicScale k
      let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
      (Cw * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
        Real.exp (b * Y 2 ^ 2)) * (Ce / d) * Avg)
    (hAvg : Avg ≤
      let d := Foundation.buSmallTimeDyadicScale k
      let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
      Cg * d ^ 2 *
        Real.exp (G * (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
        Real.exp (-(β * Y 2 ^ 2 / (12 * d)))) :
    let d := Foundation.buSmallTimeDyadicScale k
    let a := (1 : ℝ) / (16 * 16384)
    let b₀ := β / (48 * 16384)
    let K₀ := (Real.exp (a / 4) * (a + 2) / a) ^ 2 *
      (Real.exp (b₀ / 4) * (1 + 2 / b₀))
    I ≤ (Cw * Ce * Cg * K₀) / d *
      Real.exp (-(β / (12 * d))) * buShortSpatialProfile m := by
  dsimp at hI hAvg ⊢
  let d := Foundation.buSmallTimeDyadicScale k
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  let a : ℝ := 1 / (16 * 16384)
  let b₀ : ℝ := β / (48 * 16384)
  let K₀ : ℝ := (Real.exp (a / 4) * (a + 2) / a) ^ 2 *
    (Real.exp (b₀ / 4) * (1 + 2 / b₀))
  have hd : 0 < d := Foundation.buSmallTimeDyadicScale_pos k
  have hCoeff : 0 ≤ (Cw * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
      Real.exp (b * Y 2 ^ 2)) * (Ce / d) := by positivity
  have hAlg := bu_short_cell_gaussian_algebra β G b Cw Ce Cg hβ
    hGtan hGnorm hbβ hCw hCe hCg k hk m ell hY
  calc
    I ≤ (Cw * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
        Real.exp (b * Y 2 ^ 2)) * (Ce / d) * Avg := hI
    _ ≤ (Cw * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
        Real.exp (b * Y 2 ^ 2)) * (Ce / d) *
        (Cg * d ^ 2 * Real.exp (G * (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
          Real.exp (-(β * Y 2 ^ 2 / (12 * d)))) :=
      mul_le_mul_of_nonneg_left hAvg hCoeff
    _ ≤ (Cw * Ce * Cg * K₀) / d *
        Real.exp (-(β / (12 * d))) * buShortSpatialProfile m := hAlg

end ESS
