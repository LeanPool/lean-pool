/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellCylinderSpace
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Normalized dyadic cells

The shifted dyadic cell lies inside the local energy cylinder for the
rescaled field.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A shifted short-time dyadic cell lies inside the inner local energy
cylinder at its midpoint (`lem:bu-small-time`). -/
theorem bu_short_dyadic_cell_normalized_inner
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (z : ParabolicPoint)
    (hz : z ∈ Foundation.buSmallTimeDyadicCell k m ell) :
    let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
    let r := Real.sqrt δ / 8
    (z.1, 1 / 2 + z.2) ∈
      spaceTimeSet (vec3Ball Y r)
        (Ioo (1 / 2 + δ - r ^ 2 / 2)
          (1 / 2 + δ - r ^ 2 / 2 + r ^ 2)) := by
  dsimp
  have hs := bu_short_dyadic_cell_space_inner k m ell 1
    (by norm_num) z hz
  have ht := bu_short_dyadic_cell_time_inner k m ell 1
    (by norm_num) z hz
  constructor
  · simpa only [one_smul, one_pow, one_mul] using hs
  · simp only [one_pow, one_mul] at ht
    constructor <;> nlinarith only [ht.1, ht.2]

end ESS
