/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellHeight
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShiftedCells
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellDensityIntegrable

/-!
# Geometry of a high-strip dyadic cell

A shifted cell meeting the high normal strip has an averaging center
above the boundary and has time below the Gaussian threshold.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A high-strip cell has an averaging ball contained in the positive
half-space, and its midpoint lies at normal height above two
(`lem:bu-small-time`). -/
theorem bu_short_high_cell_geometry
    (scale : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (k : ℤ) (hk : 1 ≤ k) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (z : ParabolicPoint)
    (hz : z ∈ buShortShiftedDyadicCell k m ell ∩ buShortHighStrip scale) :
    let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
    2 < (scale • Y) 2 ∧ δ < 1 / 2 ∧
      vec3Ball Y (Real.sqrt (3 * δ / 2)) ⊆ {x : Vec3 | 0 < x 2} ∧
      vec3Ball Y (2 * (Real.sqrt δ / 8)) ⊆ {x : Vec3 | 0 < x 2} := by
  rcases hz.1 with ⟨q, hq, rfl⟩
  have hqheight : buShortYMinus scale ≤ q.1 2 := by
    simpa only [bu_short_time_shift_point_eval] using hz.2.1
  exact bu_short_dyadic_center_average_geometry k m ell scale hscale
    hscale1 hk q hq hqheight

end ESS
