/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitGeometry
public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitFluxVolume
public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitFluxPlane

/-!
# Unconditional integrability on the actual Voronoi exteriors and faces

The literal half nearest-other ball is contained in the open cell.

The positive-height exclusion applies to the actual nuclear configuration.
-/

public section

open Set MeasureTheory Metric
open scoped ENNReal

namespace LiebThirring

/-- The literal half nearest-other ball is contained in the open cell. -/
theorem ball_nearestOther_half_subset_voronoiCell {M : ℕ} (R : Fin M → Position)
    (hM : 2 ≤ M) (k : Fin M) :
    ball (R k) ((nearestOtherNucleusDistance R k).toReal / 2) ⊆ voronoiCell R k := by
  obtain ⟨l, hl, hmin⟩ := exists_nearest_other_nucleus R hM k
  rw [nearestOtherNucleusDistance_eq_of_nearest R hl hmin,
    ENNReal.toReal_ofReal (norm_nonneg _)]
  apply ball_subset_voronoiCell_of_bound
  intro p hp
  rw [dist_eq_norm]
  linarith only [hmin p hp]

/-- The positive-height exclusion applies to the actual nuclear configuration. -/
theorem integrableOn_inverse_fourth_voronoiExterior {M : ℕ}
    (R : Fin M → Position) (hR : Function.Injective R) (hM : 2 ≤ M) (k : Fin M) :
    IntegrableOn (fun x : Position => 1 / ‖x - R k‖ ^ 4) (voronoiCell R k)ᶜ :=
  integrableOn_inverse_fourth_exterior_of_ball_subset R k _
    (half_pos (nearestOtherNucleusDistance_toReal_pos R hR hM k))
    (ball_nearestOther_half_subset_voronoiCell R hM k)

/-- The inverse-fourth flux density is integrable on the whole bisector plane. -/
theorem integrable_bisector_inverse_fourth_flux {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k l : Fin M) (hkl : k ≠ l) :
    Integrable (fun y : Position => nuclearHalfDistance R k l / ‖y - R k‖ ^ 4)
      (bisectorSurfaceMeasure R hR k l hkl) := by
  have hh := planeHeight_bisector R hR hkl
  have hi := integrable_plane_inverse_fourth_flux (bisectorNormal R k l)
    (midpoint ℝ (R k) (R l)) (R k) (norm_bisectorNormal R hR hkl)
    (bisectorSurfaceFrame R hR k l hkl) (hh.symm ▸ nuclearHalfDistance_pos R hR hkl)
  simpa only [hh, bisectorSurfaceMeasure] using hi

/-- In particular the actual, potentially unbounded genuine face is integrable. -/
theorem integrableOn_voronoiFace_inverse_fourth_flux {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k l : Fin M) (hkl : k ≠ l) :
    IntegrableOn (fun y : Position => nuclearHalfDistance R k l / ‖y - R k‖ ^ 4)
      (voronoiFace R k l) (bisectorSurfaceMeasure R hR k l hkl) :=
  (integrable_bisector_inverse_fourth_flux R hR k l hkl).restrict

end LiebThirring

end
