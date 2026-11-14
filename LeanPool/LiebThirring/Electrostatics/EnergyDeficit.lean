/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitBoundary
public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitLowerBound
public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitTrivial
public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitFlux
import LeanPool.LiebThirring.Electrostatics.SlicingDivergence

/-!
# Assembly of the energy deficit from the potential and exterior-flux identities

The exterior flux identity, cutoff passage, geometric lower bound, and charge
coefficients combine with the screened-potential identity to give the energy deficit.
-/

public section

open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace LiebThirring

/-- The exact exterior expression once the potential identity and the exterior flux
calculation are supplied. This is a conditional assembly helper. -/
theorem half_energy_add_exterior_integrals_eq_repulsion_of_potential_eq_and_exterior_flux
    {M : ℕ} (hM : 1 ≤ M) (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (hPhi : ∀ x, screenedPotential Z R x =
      coulombPotential (voronoiFaceMeasure R hR (Z : ℝ)) x)
    (hFlux : ∀ k : Fin M,
      (∫⁻ x in (voronoiCell R k)ᶜ, ENNReal.ofReal ((‖x - R k‖ ^ 4)⁻¹)) =
        ∑ l : {l : Fin M // l ≠ k}, ∫⁻ y in voronoiFace R k l.val,
          ENNReal.ofReal (nuclearHalfDistance R k l.val / ‖y - R k‖ ^ 4)
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm) :
    coulombEnergy (voronoiFaceMeasure R hR (Z : ℝ)) (voronoiFaceMeasure R hR (Z : ℝ)) / 2 +
      ENNReal.ofReal ((Z : ℝ) ^ 2 / (8 * Real.pi)) *
        (∑ k : Fin M, ∫⁻ x in (voronoiCell R k)ᶜ, ENNReal.ofReal ((‖x - R k‖ ^ 4)⁻¹)) =
      nuclearRepulsion (fun _ => Z) R := by
  simp_rw [hFlux]
  exact half_energy_add_directed_boundary_eq_repulsion_of_potential_eq hM Z R hR hPhi

/-- The exact square-completion input conditional on the potential and exterior-flux identities.
The extra exterior-flux premise is displayed in the name and statement. -/
theorem energyDeficit_of_potential_eq_and_exterior_flux {M : ℕ}
    (hM : 1 ≤ M) (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (hPhi : ∀ x, screenedPotential Z R x =
      coulombPotential (voronoiFaceMeasure R hR (Z : ℝ)) x)
    (hFlux : 2 ≤ M → ∀ k : Fin M,
      (∫⁻ x in (voronoiCell R k)ᶜ, ENNReal.ofReal ((‖x - R k‖ ^ 4)⁻¹)) =
        ∑ l : {l : Fin M // l ≠ k}, ∫⁻ y in voronoiFace R k l.val,
          ENNReal.ofReal (nuclearHalfDistance R k l.val / ‖y - R k‖ ^ 4)
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm) :
    coulombEnergy (voronoiFaceMeasure R hR (Z : ℝ)) (voronoiFaceMeasure R hR (Z : ℝ)) / 2 +
      baxterCorrection Z R ≤ nuclearRepulsion (fun _ => Z) R := by
  by_cases hM2 : 2 ≤ M
  · calc
      _ ≤ coulombEnergy (voronoiFaceMeasure R hR (Z : ℝ)) (voronoiFaceMeasure R hR (Z : ℝ)) / 2 +
          ENNReal.ofReal ((Z : ℝ) ^ 2 / (8 * Real.pi)) *
            (∑ k : Fin M, ∫⁻ x in (voronoiCell R k)ᶜ, ENNReal.ofReal ((‖x - R k‖ ^ 4)⁻¹)) :=
        add_le_add le_rfl (baxterCorrection_le_exterior_integrals hM2 Z R hR)
      _ = _ := half_energy_add_exterior_integrals_eq_repulsion_of_potential_eq_and_exterior_flux
        hM Z R hR hPhi (hFlux hM2)
  · have he : M = 1 := le_antisymm (Nat.lt_succ_iff.mp (lt_of_not_ge hM2)) hM
    subst M
    exact energyDeficit_one Z R hR

/-- A reusable assembly of the square-completion input from potential equality
and a compact-field flux identity. -/
theorem energyDeficit_of_potential_eq_and_compact_flux {M : ℕ}
    (hM : 1 ≤ M) (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (hPhi : ∀ x, screenedPotential Z R x =
      coulombPotential (voronoiFaceMeasure R hR (Z : ℝ)) x)
    (hCompactFlux : ∀ (k : Fin M) (V : Position → Position),
      ContDiff ℝ 1 V → HasCompactSupport V →
      (∫ x in (voronoiCell R k)ᶜ, positionDivergence V x) =
        -(∑ l : {l : Fin M // l ≠ k},
          ∫ y in voronoiFace R k l.val, inner ℝ (bisectorNormal R k l.val) (V y)
            ∂bisectorSurfaceMeasure R hR k l.val l.property.symm)) :
    coulombEnergy (voronoiFaceMeasure R hR (Z : ℝ)) (voronoiFaceMeasure R hR (Z : ℝ)) / 2 +
      baxterCorrection Z R ≤ nuclearRepulsion (fun _ => Z) R :=
  energyDeficit_of_potential_eq_and_exterior_flux hM Z R hR hPhi
    (fun hM2 k => lintegral_voronoiExterior_inverse_fourth_of_compact_flux
      R hR hM2 k (hCompactFlux k))

/-- The nearest-nucleus energy deficit used in square completion.
The potential identity is the only analytic hypothesis; compact-field flux,
the cutoff limit and the half-space lower bound are supplied by proved theorems.
The one-nucleus case is included. -/
theorem energyDeficit_of_potential_eq {M : ℕ}
    (hM : 1 ≤ M) (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (hPhi : ∀ x, screenedPotential Z R x =
      coulombPotential (voronoiFaceMeasure R hR (Z : ℝ)) x) :
    coulombEnergy (voronoiFaceMeasure R hR (Z : ℝ)) (voronoiFaceMeasure R hR (Z : ℝ)) / 2 +
      baxterCorrection Z R ≤ nuclearRepulsion (fun _ => Z) R :=
  energyDeficit_of_potential_eq_and_compact_flux hM Z R hR hPhi
    (voronoiExterior_compact_flux R hR)

end LiebThirring

end
