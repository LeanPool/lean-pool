/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShiftedCells

/-!
# Dyadic cells in Gaussian averaging boxes

The Gaussian averaging box at each dyadic midpoint contains the
corresponding shifted space-time cell.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The shifted dyadic cell is contained in the Gaussian averaging box
at its center (`lem:bu-small-time`). -/
theorem bu_short_shifted_dyadic_cell_average
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048) :
    let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
    buShortShiftedDyadicCell k m ell ⊆
      spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
        (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4)) := by
  dsimp
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
  let r := Real.sqrt δ / 8
  have hd : 0 < Foundation.buSmallTimeDyadicScale k :=
    Foundation.buSmallTimeDyadicScale_pos k
  have hδ : 0 < δ :=
    (half_pos hd).trans (bu_short_dyadic_cell_center_time_bounds k m ell).1
  have hr : 0 < r := by dsimp [r]; positivity
  have hinner := bu_short_shifted_dyadic_cell_inner k m ell
  have hinnerOuter :
      spaceTimeSet (vec3Ball Y r)
        (Ioo (1 / 2 + δ - r ^ 2 / 2)
          (1 / 2 + δ - r ^ 2 / 2 + r ^ 2)) ⊆
      spaceTimeSet (vec3Ball Y (2 * r))
        (Ioo (1 / 2 + δ - r ^ 2 / 2)
          (1 / 2 + δ - r ^ 2 / 2 + 4 * r ^ 2)) := by
    intro z hz
    refine ⟨(vec3Ball_mono (by linarith only [hr] : r ≤ 2 * r)) hz.1,
      ⟨hz.2.1, ?_⟩⟩
    nlinarith only [hz.2.2, sq_nonneg r]
  have htranslated :
      spaceTimeSet (vec3Ball Y (2 * r))
        (Ioo (1 / 2 + δ - r ^ 2 / 2)
          (1 / 2 + δ - r ^ 2 / 2 + 4 * r ^ 2)) ⊆
      spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
        (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4)) := by
    intro z hz
    have hspace := (bu_short_caccioppoli_outer_space_subset Y δ hδ) hz.1
    have htime := (bu_short_caccioppoli_outer_time_subset δ hδ)
      (show z.2 - 1 / 2 ∈ Ioo (δ - r ^ 2 / 2)
        (δ - r ^ 2 / 2 + 4 * r ^ 2) by
        constructor <;> linarith only [hz.2.1, hz.2.2])
    exact ⟨hspace,
      ⟨by linarith only [htime.1], by linarith only [htime.2]⟩⟩
  exact hinner.trans (hinnerOuter.trans htranslated)

end ESS
