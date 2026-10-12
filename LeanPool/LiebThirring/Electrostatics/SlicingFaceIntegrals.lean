/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.FaceMeasureDirected
public import LeanPool.LiebThirring.Electrostatics.FaceMeasureMass
public import LeanPool.LiebThirring.Electrostatics.PlaneFormula
import all LeanPool.LiebThirring.Electrostatics.FaceMeasureBasic
import all LeanPool.LiebThirring.Electrostatics.FaceMeasureGeometry

/-!
# Surface charge and coordinate graph integrals

Integration against one face charge, with the literal face charge density.

The literal unordered-face surface integral form of the `ν`.
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace LiebThirring

/-- Integration against one face charge, with the literal face charge density. -/
theorem integral_nuclearFaceMeasure_density {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z)
    (k l : Fin M) (hkl : k ≠ l) (f : Position → ℝ) :
    (∫ x, f x ∂nuclearFaceMeasure R hR Z k l hkl) =
      ∫ x in voronoiFace R k l, nuclearFaceDensity R Z k l x * f x
        ∂bisectorSurfaceMeasure R hR k l hkl := by
  rw [integral_nuclearFaceMeasure_flux R hR hZ k l hkl f, ← integral_const_mul]
  apply setIntegral_congr_fun (measurableSet_voronoiFace R k l)
  intro x hx
  change (Z / (2 * Real.pi)) * (f x * nuclearFaceFlux R k l x) =
    nuclearFaceDensity R Z k l x * f x
  rw [nuclearFaceDensity_eq_flux R hR Z hx]
  ring

/-- The literal unordered-face surface integral form of the landed `ν`. -/
theorem integral_voronoiFaceMeasure_density {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z)
    (f : Position → ℝ) (hf : Integrable f (voronoiFaceMeasure R hR Z)) :
    (∫ x, f x ∂voronoiFaceMeasure R hR Z) =
      ∑ p : NuclearPair M, ∫ x in voronoiFace R p.val.1 p.val.2,
        nuclearFaceDensity R Z p.val.1 p.val.2 x * f x
          ∂bisectorSurfaceMeasure R hR p.val.1 p.val.2 (ne_of_lt p.property) := by
  rw [voronoiFaceMeasure] at hf ⊢
  rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hf)]
  exact Finset.sum_congr rfl (fun p _ => integral_nuclearFaceMeasure_density R hR hZ _ _ _ f)

theorem integrable_compact_voronoiFaceMeasure {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z)
    {f : Position → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable f (voronoiFaceMeasure R hR Z) := by
  let := isFiniteMeasure_voronoiFaceMeasure R hR hZ
  exact hf.integrable_of_hasCompactSupport hfc

end LiebThirring

end
