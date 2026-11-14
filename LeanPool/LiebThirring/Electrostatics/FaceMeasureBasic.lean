/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Measure.WithDensity
public import LeanPool.LiebThirring.Electrostatics.FaceMeasureGeometry

/-!
# The positive measure of genuine Voronoi faces

Unordered nuclear pairs, represented by their increasing ordering.

The real density on a bisector plane, as prescribed in.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace LiebThirring

variable {M : ℕ}

/-- Unordered nuclear pairs, represented by their increasing ordering. -/
abbrev NuclearPair (M : ℕ) := {p : Fin M × Fin M // p.1 < p.2}

/-- The real density on a bisector plane, as prescribed in (6.1). -/
noncomputable def nuclearFaceDensity (R : Fin M → Position) (Z : ℝ)
    (k l : Fin M) (y : Position) : ℝ :=
  Z * nuclearHalfDistance R k l / (2 * Real.pi * ‖y - R k‖ ^ 3)

/-- Extend the nonnegative density by zero off the genuine face. -/
noncomputable def voronoiFaceDensity (R : Fin M → Position) (Z : ℝ)
    (k l : Fin M) : Position → ℝ≥0∞ :=
  (voronoiFace R k l).indicator (fun y => ENNReal.ofReal (nuclearFaceDensity R Z k l y))

/-- One genuine face, equipped with its surface charge. -/
noncomputable def nuclearFaceMeasure (R : Fin M → Position) (hR : Function.Injective R)
    (Z : ℝ) (k l : Fin M) (hkl : k ≠ l) : Measure Position :=
  (bisectorSurfaceMeasure R hR k l hkl).withDensity (voronoiFaceDensity R Z k l)

/-- The positive measure `ν` of (6.1); each genuine face occurs once. -/
noncomputable def voronoiFaceMeasure (R : Fin M → Position) (hR : Function.Injective R)
    (Z : ℝ) : Measure Position :=
  ∑ p : NuclearPair M, nuclearFaceMeasure R hR Z p.val.1 p.val.2 (ne_of_lt p.property)

theorem measurable_nuclearFaceDensity (R : Fin M → Position) (Z : ℝ) (k l : Fin M) :
    Measurable (nuclearFaceDensity R Z k l) := by
  unfold nuclearFaceDensity
  exact measurable_const.div (measurable_const.mul ((measurable_id.sub
    measurable_const).norm.pow_const 3))

theorem measurable_voronoiFaceDensity (R : Fin M → Position) (Z : ℝ) (k l : Fin M) :
    Measurable (voronoiFaceDensity R Z k l) :=
  (measurable_nuclearFaceDensity R Z k l).ennreal_ofReal.indicator
    (measurableSet_voronoiFace R k l)

theorem nuclearFaceDensity_nonneg (R : Fin M → Position) {Z : ℝ} (hZ : 0 ≤ Z)
    (k l : Fin M) (y : Position) : 0 ≤ nuclearFaceDensity R Z k l y := by
  unfold nuclearFaceDensity nuclearHalfDistance
  positivity

/-- The defining nonnegative Borel integral formula, with explicit face restriction. -/
theorem lintegral_nuclearFaceMeasure (R : Fin M → Position) (hR : Function.Injective R)
    (Z : ℝ) (k l : Fin M) (hkl : k ≠ l) (h : Position → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ y, h y ∂nuclearFaceMeasure R hR Z k l hkl) =
      ∫⁻ y in voronoiFace R k l,
        ENNReal.ofReal (nuclearFaceDensity R Z k l y) * h y
        ∂bisectorSurfaceMeasure R hR k l hkl := by
  rw [nuclearFaceMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_voronoiFaceDensity R Z k l) hh]
  rw [← lintegral_indicator (measurableSet_voronoiFace R k l)]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ voronoiFace R k l <;> simp [voronoiFaceDensity, hy]

@[simp] theorem voronoiFaceMeasure_one (R : Fin 1 → Position) (hR : Function.Injective R)
    (Z : ℝ) : voronoiFaceMeasure R hR Z = 0 := by
  have : IsEmpty (NuclearPair 1) := ⟨fun p => by
    have he : p.val.1 = p.val.2 := Subsingleton.elim _ _
    exact (ne_of_lt p.property) he⟩
  simp [voronoiFaceMeasure]

end LiebThirring

end
