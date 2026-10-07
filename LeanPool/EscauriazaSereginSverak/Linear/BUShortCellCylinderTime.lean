/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortDyadicGeometry

/-!
# Temporal nesting of dyadic and Gaussian cylinders

A short dyadic time cell lies in the inner Caccioppoli interval, while
the outer interval stays inside the Gaussian averaging interval.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The short dyadic time cell maps into a Caccioppoli inner interval
centered at its parabolic midpoint. -/
theorem bu_short_dyadic_cell_time_inner
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (scale : ℝ) (hscale : 0 < scale)
    (z : ParabolicPoint)
    (hz : z ∈ Foundation.buSmallTimeDyadicCell k m ell) :
    let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
    let τ := scale ^ 2 * δ
    let r := Real.sqrt τ / 8
    scale ^ 2 * z.2 ∈
      Ioo (τ - r ^ 2 / 2) (τ + r ^ 2 / 2) := by
  dsimp
  let d := Foundation.buSmallTimeDyadicScale k
  let h := Foundation.buSmallTimeDyadicTimeLength k
  let s := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
  let δ := s
  let τ := scale ^ 2 * δ
  let r := Real.sqrt τ / 8
  have hd : 0 < d := Foundation.buSmallTimeDyadicScale_pos k
  have hδ : d / 2 < δ :=
    (bu_short_dyadic_cell_center_time_bounds k m ell).1
  have hδ0 : 0 < δ := (half_pos hd).trans hδ
  have hτ : 0 < τ := mul_pos (sq_pos_of_pos hscale) hδ0
  have hrSq : r ^ 2 = τ / 64 := by
    dsimp [r]
    rw [div_pow, Real.sq_sqrt hτ.le]
    ring
  have hclose := bu_short_dyadic_cell_time_distance_le k m ell z hz
  have hlength : h = d / 4096 := rfl
  have hhalf : h / 2 = d / 8192 := by
    dsimp [h, d, Foundation.buSmallTimeDyadicTimeLength]
    ring
  have hbound : |z.2 - s| ≤ d / 8192 :=
    hclose.trans_eq hhalf
  have hlo : -(d / 8192) ≤ z.2 - s := (abs_le.mp hbound).1
  have hhi : z.2 - s ≤ d / 8192 := (abs_le.mp hbound).2
  have hcoeff : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hgeom : d / 8192 < δ / 128 := by linarith only [hδ, hd]
  change τ - r ^ 2 / 2 < scale ^ 2 * z.2 ∧
    scale ^ 2 * z.2 < τ + r ^ 2 / 2
  rw [hrSq]
  constructor
  · have hsmall : -(δ / 128) < z.2 - s := by
      linarith only [hlo, hgeom]
    have hprod := mul_lt_mul_of_pos_left hsmall hcoeff
    dsimp [τ, δ] at *
    nlinarith only [hprod]
  · have hsmall : z.2 - s < δ / 128 := by
      linarith only [hhi, hgeom]
    have hprod := mul_lt_mul_of_pos_left hsmall hcoeff
    dsimp [τ, δ] at *
    nlinarith only [hprod]

/-- The Caccioppoli outer interval fits the Gaussian time average. -/
theorem bu_short_caccioppoli_outer_time_subset
    (τ : ℝ) (hτ : 0 < τ) :
    let r := Real.sqrt τ / 8
    Ioo (τ - r ^ 2 / 2) (τ - r ^ 2 / 2 + 4 * r ^ 2) ⊆
      Ioo (τ / 2) (5 * τ / 4) := by
  dsimp
  have hrSq : (Real.sqrt τ / 8) ^ 2 = τ / 64 := by
    rw [div_pow, Real.sq_sqrt hτ.le]
    ring
  rw [hrSq]
  intro t ht
  constructor
  · linarith only [ht.1, hτ]
  · linarith only [ht.2, hτ]

end ESS
