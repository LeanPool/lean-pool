/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import LeanPool.LiebThirring.Electrostatics.FaceMeasureDirectedPairs

/-!
# The directed Voronoi boundary formula

The outward normal Coulomb flux on a nuclear face.

The normal component equals the half separation on the literal bisector plane.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace LiebThirring

variable {M : ℕ}

/-- The outward normal Coulomb flux on a nuclear face. -/
noncomputable def nuclearFaceFlux (R : Fin M → Position) (k l : Fin M) (y : Position) : ℝ :=
  inner ℝ (bisectorNormal R k l) (y - R k) / ‖y - R k‖ ^ 3

/-- The normal component equals the half separation on the literal bisector plane. -/
theorem nuclearFaceFlux_on_face (R : Fin M → Position) (hR : Function.Injective R)
    {k l : Fin M} {y : Position} (hy : y ∈ voronoiFace R k l) :
    nuclearFaceFlux R k l y = nuclearHalfDistance R k l / ‖y - R k‖ ^ 3 := by
  rw [nuclearFaceFlux, (mem_bisectorPlane_iff_normal R hR hy.1 y).mp hy.2.1]
  rfl

/-- The normal flux is the same in the two face orientations. -/
theorem nuclearFaceFlux_comm_on_face (R : Fin M → Position) (hR : Function.Injective R)
    {k l : Fin M} {y : Position} (hy : y ∈ voronoiFace R k l) :
    nuclearFaceFlux R k l y = nuclearFaceFlux R l k y := by
  have hy' : y ∈ voronoiFace R l k := by rw [← voronoiFace_comm]; exact hy
  have hd : ‖y - R k‖ = ‖y - R l‖ := by
    simpa only [dist_eq_norm] using (mem_bisectorPlane R k l y).mp hy.2.1
  rw [nuclearFaceFlux_on_face R hR hy, nuclearFaceFlux_on_face R hR hy',
    nuclearHalfDistance_comm R k l, hd]

/-- Orientation does not change Euclidean surface measure on a bisector. -/
theorem bisectorSurfaceMeasure_comm (R : Fin M → Position) (hR : Function.Injective R)
    (k l : Fin M) (hkl : k ≠ l) :
    bisectorSurfaceMeasure R hR k l hkl = bisectorSurfaceMeasure R hR l k hkl.symm := by
  unfold bisectorSurfaceMeasure
  apply planeMeasure_eq_of_plane_eq
  calc
    _ = bisectorPlane R k l := (bisectorPlane_eq_affinePlane R hR hkl).symm
    _ = bisectorPlane R l k := bisectorPlane_comm R k l
    _ = _ := bisectorPlane_eq_affinePlane R hR hkl.symm

/-- The density is exactly the normal flux times `Z/(2π)` on the face. -/
theorem nuclearFaceDensity_eq_flux (R : Fin M → Position) (hR : Function.Injective R)
    (Z : ℝ) {k l : Fin M} {y : Position} (hy : y ∈ voronoiFace R k l) :
    nuclearFaceDensity R Z k l y = (Z / (2 * Real.pi)) * nuclearFaceFlux R k l y := by
  rw [nuclearFaceFlux_on_face R hR hy, nuclearFaceDensity]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Nonnegative single-face integration in outward-normal form. -/
theorem lintegral_nuclearFaceMeasure_flux (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z)
    (k l : Fin M) (hkl : k ≠ l) (h : Position → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ y, h y ∂nuclearFaceMeasure R hR Z k l hkl) = ENNReal.ofReal (Z / (2 * Real.pi)) *
      ∫⁻ y in voronoiFace R k l, h y * ENNReal.ofReal (nuclearFaceFlux R k l y)
        ∂bisectorSurfaceMeasure R hR k l hkl := by
  rw [lintegral_nuclearFaceMeasure R hR Z k l hkl h hh]
  have hc : 0 ≤ Z / (2 * Real.pi) := by positivity
  have hflux : Measurable (nuclearFaceFlux R k l) :=
    (by
      unfold nuclearFaceFlux
      exact (continuous_const.inner (continuous_id.sub continuous_const)).measurable |>.div
        ((measurable_id.sub measurable_const).norm.pow_const 3))
  have hm : Measurable (fun y => h y * ENNReal.ofReal (nuclearFaceFlux R k l y)) :=
    hh.mul hflux.ennreal_ofReal
  rw [← lintegral_const_mul _ hm]
  apply setLIntegral_congr_fun (measurableSet_voronoiFace R k l)
  intro y hy
  change ENNReal.ofReal (nuclearFaceDensity R Z k l y) * h y =
    ENNReal.ofReal (Z / (2 * Real.pi)) * (h y * ENNReal.ofReal (nuclearFaceFlux R k l y))
  rw [nuclearFaceDensity_eq_flux R hR Z hy, ENNReal.ofReal_mul hc]
  ac_rfl

/-- The flux integral is invariant under swapping the nuclei, in the extended setting. -/
theorem lintegral_nuclearFaceFlux_comm (R : Fin M → Position) (hR : Function.Injective R)
    (k l : Fin M) (hkl : k ≠ l) (h : Position → ℝ≥0∞) :
    (∫⁻ y in voronoiFace R k l, h y * ENNReal.ofReal (nuclearFaceFlux R k l y)
      ∂bisectorSurfaceMeasure R hR k l hkl) =
    ∫⁻ y in voronoiFace R l k, h y * ENNReal.ofReal (nuclearFaceFlux R l k y)
      ∂bisectorSurfaceMeasure R hR l k hkl.symm := by
  rw [voronoiFace_comm R k l, bisectorSurfaceMeasure_comm R hR k l hkl]
  apply setLIntegral_congr_fun (measurableSet_voronoiFace R l k)
  intro y hy
  change h y * ENNReal.ofReal (nuclearFaceFlux R k l y) =
    h y * ENNReal.ofReal (nuclearFaceFlux R l k y)
  rw [nuclearFaceFlux_comm_on_face R hR hy]

/-- The factor `Z/(2π)` splits into the two directed factors `Z/(4π)`. -/
theorem face_coefficient_eq_two_directed (Z : ℝ) :
    Z / (2 * Real.pi) = Z / (4 * Real.pi) + Z / (4 * Real.pi) := by
  field_simp
  ring

/-- Equation (6.3) tested against any nonnegative Borel function. -/
theorem lintegral_voronoiFaceMeasure_directed (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z)
    (h : Position → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ y, h y ∂voronoiFaceMeasure R hR Z) = ENNReal.ofReal (Z / (4 * Real.pi)) *
      ∑ k : Fin M, ∑ l : {l : Fin M // l ≠ k},
        ∫⁻ y in voronoiFace R k l.val,
          h y * ENNReal.ofReal (inner ℝ (bisectorNormal R k l.val) (y - R k) / ‖y - R k‖ ^ 3)
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm := by
  let f : ∀ k l : Fin M, k ≠ l → ℝ≥0∞ := fun k l hkl =>
    ∫⁻ y in voronoiFace R k l, h y * ENNReal.ofReal (nuclearFaceFlux R k l y)
      ∂bisectorSurfaceMeasure R hR k l hkl
  have hs := sum_directedNuclearPairs f (fun k l hkl => lintegral_nuclearFaceFlux_comm R hR k l hkl
    h)
  change (∫⁻ y, h y ∂voronoiFaceMeasure R hR Z) =
    ENNReal.ofReal (Z / (4 * Real.pi)) * ∑ k, ∑ l : {l : Fin M // l ≠ k}, f k l l.property.symm
  rw [voronoiFaceMeasure, lintegral_finsetSum_measure]
  have hp : (∑ p : NuclearPair M, ∫⁻ y, h y ∂nuclearFaceMeasure R hR Z
      p.val.1 p.val.2 (ne_of_lt p.property)) =
      ENNReal.ofReal (Z / (2 * Real.pi)) * ∑ p : NuclearPair M,
        f p.val.1 p.val.2 (ne_of_lt p.property) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ =>
      lintegral_nuclearFaceMeasure_flux R hR hZ _ _ _ h hh
  rw [hp, hs]
  have h4 : 0 ≤ Z / (4 * Real.pi) := by positivity
  have hc : ENNReal.ofReal (Z / (2 * Real.pi)) =
      ENNReal.ofReal (Z / (4 * Real.pi)) + ENNReal.ofReal (Z / (4 * Real.pi)) := by
    rw [face_coefficient_eq_two_directed, ENNReal.ofReal_add h4 h4]
  rw [hc, add_mul, mul_add]

/-- Every face density is finite, including its zero extension. -/
theorem voronoiFaceDensity_lt_top (R : Fin M → Position) (Z : ℝ)
    (k l : Fin M) (y : Position) : voronoiFaceDensity R Z k l y < ⊤ := by
  by_cases hy : y ∈ voronoiFace R k l
  · rw [voronoiFaceDensity, indicator_of_mem hy]
    exact ENNReal.ofReal_lt_top
  · rw [voronoiFaceDensity, indicator_of_notMem hy]
    exact ENNReal.zero_lt_top

/-- A real face-charge integral is the weighted real surface integral, without a
separate global measurability premise on the function. -/
theorem integral_nuclearFaceMeasure_flux (R : Fin M → Position)
    (hR : Function.Injective R) {Z : ℝ} (hZ : 0 ≤ Z)
    (k l : Fin M) (hkl : k ≠ l) (h : Position → ℝ) :
    (∫ y, h y ∂nuclearFaceMeasure R hR Z k l hkl) = (Z / (2 * Real.pi)) *
      ∫ y in voronoiFace R k l, h y * nuclearFaceFlux R k l y
        ∂bisectorSurfaceMeasure R hR k l hkl := by
  rw [nuclearFaceMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_voronoiFaceDensity R Z k l)
    (Filter.Eventually.of_forall (voronoiFaceDensity_lt_top R Z k l))]
  have he : (fun y => (voronoiFaceDensity R Z k l y).toReal • h y) =
      (voronoiFace R k l).indicator (fun y => nuclearFaceDensity R Z k l y * h y) := by
    funext y
    by_cases hy : y ∈ voronoiFace R k l
    · rw [voronoiFaceDensity, indicator_of_mem hy, indicator_of_mem hy,
        ENNReal.toReal_ofReal (nuclearFaceDensity_nonneg R hZ k l y), smul_eq_mul]
    · rw [voronoiFaceDensity, indicator_of_notMem hy, indicator_of_notMem hy,
        ENNReal.toReal_zero, zero_smul]
  rw [he, integral_indicator (measurableSet_voronoiFace R k l), ← integral_const_mul]
  apply setIntegral_congr_fun (measurableSet_voronoiFace R k l)
  intro y hy
  change nuclearFaceDensity R Z k l y * h y =
    (Z / (2 * Real.pi)) * (h y * nuclearFaceFlux R k l y)
  rw [nuclearFaceDensity_eq_flux R hR Z hy]
  ring

end LiebThirring

end
