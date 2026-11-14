/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitIntegrability
public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitFluxCutoff

/-!
# The actual Voronoi volume and boundary cutoff limits

The principal exterior volume term converges on the actual exterior.

The radial derivative error tends to zero on the actual exterior.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace LiebThirring

/-- The principal exterior volume term converges on the actual exterior. -/
theorem tendsto_integral_cutoff_voronoiExterior {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (hM : 2 ≤ M) (k : Fin M) :
    Tendsto (fun T : ℝ => ∫ x in (voronoiCell R k)ᶜ,
      exteriorFluxCutoff (R k) T x * (1 / ‖x - R k‖ ^ 4)) atTop
        (𝓝 (∫ x in (voronoiCell R k)ᶜ, 1 / ‖x - R k‖ ^ 4)) :=
  tendsto_integral_exteriorFluxCutoff _ (R k) _
    (integrableOn_inverse_fourth_voronoiExterior R hR hM k)

/-- The radial derivative error tends to zero on the actual exterior. -/
theorem tendsto_integral_defect_voronoiExterior {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (hM : 2 ≤ M) (k : Fin M) :
    Tendsto (fun T : ℝ => ∫ x in (voronoiCell R k)ᶜ,
      exteriorFluxDefect (T⁻¹ • (x - R k)) * (1 / ‖x - R k‖ ^ 4)) atTop (𝓝 0) :=
  tendsto_integral_exteriorFluxDefect _ (R k) _
    (integrableOn_inverse_fourth_voronoiExterior R hR hM k)

/-- Every actual boundary term converges, including on unbounded genuine faces. -/
theorem tendsto_integral_cutoff_voronoiFace {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k l : Fin M) (hkl : k ≠ l) :
    Tendsto (fun T : ℝ => ∫ y in voronoiFace R k l,
      exteriorFluxCutoff (R k) T y * (nuclearHalfDistance R k l / ‖y - R k‖ ^ 4)
        ∂bisectorSurfaceMeasure R hR k l hkl) atTop
      (𝓝 (∫ y in voronoiFace R k l, nuclearHalfDistance R k l / ‖y - R k‖ ^ 4
        ∂bisectorSurfaceMeasure R hR k l hkl)) :=
  tendsto_integral_exteriorFluxCutoff _ (R k) _
    (integrableOn_voronoiFace_inverse_fourth_flux R hR k l hkl)

end LiebThirring

end
