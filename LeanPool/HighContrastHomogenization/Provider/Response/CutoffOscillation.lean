/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffDerivatives
public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffCoefficient
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.CutoffOscillation
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.CutoffProduct.Geometry

/-!
# High-contrast homogenization: Provider.Response.CutoffOscillation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Oscillation on an adapted child cell

The reference-coordinate gradient estimate controls the variation of the
physical cutoff between the images of two points in any scale-`s` child cube.
This is the form consumed by the cutoff-energy estimate.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open Book.Ch05.Section53.JUpperBoundWeakNorms

/-- On a scale-`s` reference child, the physical cutoff pulled through `q`
oscillates by at most the common cutoff constant times `3⁻ᴴ`. -/
theorem adaptedPreYoungCutoff_pullback_oscillation {d : ℕ} [NeZero d]
    {q : Mat d} (hq : q.PosDef) {R : TriadicCube d} {s t H : ℤ}
    (hR : R.scale = s) (hH : H = t - s) {x y : Vec d}
    (hx : x ∈ cubeSet R) (hy : y ∈ cubeSet R) :
    ‖adaptedPreYoungCutoff q hq t (matVecMul q x) -
        adaptedPreYoungCutoff q hq t (matVecMul q y)‖ ≤
      1024 * (d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2 *
        (3 : ℝ) ^ (-H) := by
  let u : Vec d → ℝ :=
    fun z => adaptedPreYoungCutoff q hq t (matVecMul q z)
  let Cd : ℝ := 1024 * (d : ℝ) ^ 4 *
    (max 1 (max smoothTransitionProfile.derivBound
      smoothTransitionProfile.secondDerivBound)) ^ 2
  have hlinear : ContDiff ℝ (⊤ : ℕ∞) (matVecMul q) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin q)).contDiff
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    simpa only [u, Function.comp_def] using
      (adaptedPreYoungCutoff_smooth hq t).comp hlinear
  have hB : 0 ≤ Cd * (3 : ℝ) ^ (-t) := by
    dsimp [Cd]
    positivity
  have hderiv : ∀ z ∈ cubeSet R,
      ‖fderiv ℝ u z‖ ≤ Cd * (3 : ℝ) ^ (-t) := by
    intro z _hz
    simpa only [u, Cd] using
      adaptedPreYoungCutoff_pullback_fderiv_bound hq t z
  have hosc := norm_sub_le_cubeScaleFactor_mul_of_contDiff_bound
    R hu hB hderiv hx hy
  calc
    ‖adaptedPreYoungCutoff q hq t (matVecMul q x) -
        adaptedPreYoungCutoff q hq t (matVecMul q y)‖ ≤
        cubeScaleFactor R * (Cd * (3 : ℝ) ^ (-t)) := by
      simpa only [u] using hosc
    _ = Cd * (3 : ℝ) ^ s * ((3 : ℝ) ^ (-t) * 1) := by
      rw [show cubeScaleFactor R = (3 : ℝ) ^ s by
        unfold cubeScaleFactor
        rw [hR]]
      ring
    _ = Cd * (3 : ℝ) ^ (-H) * 1 :=
      cutoff_energy_coefficient (Cd := Cd) (J := 1) hH
    _ = 1024 * (d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2 *
        (3 : ℝ) ^ (-H) := by
      dsimp [Cd]
      ring

/-- The child average differs from the cutoff by the same scale-gap bound at
every point of the reference child. -/
theorem adaptedPreYoungCutoff_pullback_sub_cubeAverage {d : ℕ} [NeZero d]
    {q : Mat d} (hq : q.PosDef) {R : TriadicCube d} {s t H : ℤ}
    (hR : R.scale = s) (hH : H = t - s) {x : Vec d}
    (hx : x ∈ cubeSet R) :
    |cubeAverage R (fun z => adaptedPreYoungCutoff q hq t (matVecMul q z)) -
        adaptedPreYoungCutoff q hq t (matVecMul q x)| ≤
      1024 * (d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2 *
        (3 : ℝ) ^ (-H) := by
  let u : Vec d → ℝ :=
    fun z => adaptedPreYoungCutoff q hq t (matVecMul q z)
  let C : ℝ := 1024 * (d : ℝ) ^ 4 *
    (max 1 (max smoothTransitionProfile.derivBound
      smoothTransitionProfile.secondDerivBound)) ^ 2 *
    (3 : ℝ) ^ (-H)
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u := by
    have hlinear : ContDiff ℝ (⊤ : ℕ∞) (matVecMul q) :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin q)).contDiff
    simpa only [u, Function.comp_def] using
      (adaptedPreYoungCutoff_smooth hq t).comp hlinear
  have hu_bound : ∀ z, ‖u z‖ ≤ 2 := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact adaptedPreYoungCutoff_le_two hq t (matVecMul q z)
    · exact adaptedPreYoungCutoff_nonneg hq t (matVecMul q z)
  have hu_mem : MeasureTheory.MemLp u (⊤ : ENNReal) (normalizedCubeMeasure R) :=
    MeasureTheory.memLp_top_of_bound hu_smooth.continuous.aestronglyMeasurable 2
      (Filter.Eventually.of_forall hu_bound)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have havg :
      ‖u x - cubeAverage R u‖ ≤
        cubeLpNorm R (⊤ : ENNReal) (fun y => u y - u x) :=
    norm_sub_cubeAverage_le_cubeLpNorm_infty_sub_const R u x hu_mem
  have hlinfty :
      cubeLpNorm R (⊤ : ENNReal) (fun y => u y - u x) ≤ C := by
    apply cubeLpNorm_infty_le_of_bound_on_cubeSet R
    · exact hC
    · intro y hy
      simpa only [u, C, norm_sub_rev] using
        adaptedPreYoungCutoff_pullback_oscillation hq hR hH hy hx
  have hnorm : ‖u x - cubeAverage R u‖ ≤ C := havg.trans hlinfty
  simpa only [u, C, Real.norm_eq_abs, abs_sub_comm] using hnorm

end

end Response
end HighContrast
end HCPolySupport
