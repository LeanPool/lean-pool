/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.FaceMeasureBasic
public import LeanPool.LiebThirring.Electrostatics.FaceMeasurePlaneMass

/-!
# Finite mass of the Voronoi face measure

Integrating the displayed density on the full bisector plane gives `Z`.

Restricting the whole-plane charge to the genuine face decreases its mass.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace LiebThirring

variable {M : ℕ}

/-- Integrating the displayed density on the full bisector plane gives `Z`. -/
theorem lintegral_bisector_nuclearFaceDensity (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z)
    (k l : Fin M) (hkl : k ≠ l) :
    (∫⁻ y, ENNReal.ofReal (nuclearFaceDensity R Z k l y)
      ∂bisectorSurfaceMeasure R hR k l hkl) = ENNReal.ofReal Z := by
  have hh := planeHeight_bisector R hR hkl
  have hm := lintegral_plane_faceDensity_mass (bisectorNormal R k l)
    (midpoint ℝ (R k) (R l)) (R k) (norm_bisectorNormal R hR hkl)
    (bisectorSurfaceFrame R hR k l hkl) Z hZ
    (hh.symm ▸ nuclearHalfDistance_pos R hR hkl)
  simpa only [hh, nuclearFaceDensity, bisectorSurfaceMeasure] using hm

/-- Restricting the whole-plane charge to the genuine face decreases its mass. -/
theorem nuclearFaceMeasure_mass_le (R : Fin M → Position) (hR : Function.Injective R)
    {Z : ℝ} (hZ : 0 ≤ Z) (k l : Fin M) (hkl : k ≠ l) :
    nuclearFaceMeasure R hR Z k l hkl univ ≤ ENNReal.ofReal Z := by
  rw [nuclearFaceMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  apply le_trans (lintegral_mono (fun y => ?_))
    (le_of_eq (lintegral_bisector_nuclearFaceDensity R hR hZ k l hkl))
  exact indicator_le_self _ _ y

theorem card_nuclearPair (M : ℕ) : Fintype.card (NuclearPair M) = M.choose 2 := by
  classical
  rw [Fintype.card_subtype]
  simpa only [Finset.univ_product_univ, Fintype.card_fin, Finset.card_univ] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin M))))

/-- The preliminary mass bound in face charge; exact mass belongs to the potential identity. -/
theorem voronoiFaceMeasure_mass_le (R : Fin M → Position) (hR : Function.Injective R)
    {Z : ℝ} (hZ : 0 ≤ Z) :
    voronoiFaceMeasure R hR Z univ ≤ (M.choose 2 : ℝ≥0∞) * ENNReal.ofReal Z := by
  rw [voronoiFaceMeasure, Measure.finsetSum_apply]
  calc
    _ ≤ ∑ _p : NuclearPair M, ENNReal.ofReal Z :=
      Finset.sum_le_sum fun p _ => nuclearFaceMeasure_mass_le R hR hZ _ _ _
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_nuclearPair]

theorem voronoiFaceMeasure_mass_lt_top (R : Fin M → Position) (hR : Function.Injective R)
    {Z : ℝ} (hZ : 0 ≤ Z) : voronoiFaceMeasure R hR Z univ < ⊤ :=
  (voronoiFaceMeasure_mass_le R hR hZ).trans_lt (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)

/-- Finiteness is proved from the explicit density, without a potential identity. -/
theorem isFiniteMeasure_voronoiFaceMeasure (R : Fin M → Position) (hR : Function.Injective R)
    {Z : ℝ} (hZ : 0 ≤ Z) : IsFiniteMeasure (voronoiFaceMeasure R hR Z) :=
  ⟨voronoiFaceMeasure_mass_lt_top R hR hZ⟩

end LiebThirring

end
