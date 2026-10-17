/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepThreeShallow

/-!
# HomSpineCarrierBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: the two carrier bridges

## What is still open

`HomStepThreeShallow` proved the analytic core of route (a): the normalized
average over a cube is the AVERAGE of the normalized averages over its
depth-`j` descendants, hence at most their maximum, so the deep-range bound
transfers to the shallow range with NO loss.  Its module docstring named two
purely mechanical identifications as the remaining plug-in, and this module
supplies exactly those two:

1. **the real / `ℝ≥0∞` average bridge** — the abstract family
   `F j z = ν^{1/2}‖∇u‖_{L²(z+□_j)}` is built from the REAL
   `Homogenization.volumeAverage` (`CoarseGraining`'s `normalizedSetAverage` is that
   abbreviation), while `cubeAverage_le_of_descendants` speaks about
   `∫⁻ · ∂normalizedCubeMeasure R`.  `volumeAverage_eq_toReal_lintegral` and its
   two one-sided corollaries identify them for a nonnegative integrable
   density;
2. **the indexing bridge** — `descendantsAtDepth Q j` versus the manuscript's
   `{z + □_{j₀}: z ∈ 3^{j₀}ℤ^d ∩ □_m}` at `j₀ = Q.scale - j`.
   `latticeTranslate_of_mem_descendantsAtDepth` produces, for each descendant,
   its scale, its lattice centre (`z ∈ 3^{j₀}ℤ^d`, the integer vector
   displayed), the identification `□_R = z + □_{j₀}` in the translate spelling
   the main statements use, and `z ∈ □_m`.

With these two, route (a) plugs into the `hence_holds_on_deep_range` with
nothing left over.

## Disposition of

Unchanged, and this module does not change it: the correction records a GAP IN
THE MANUSCRIPT'S JUSTIFICATION (the word "Hence" in the paper), not a false
display.  Route (a) is sound, the printed constant `3^{(1-α)X}3^{(1-α)(m-j)}` is
in fact generous, and route (a) does not need the author.  -/

open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. Bridge one: the real average versus the `ℝ≥0∞` cube integral -/

private theorem volume_openCubeSet_eq_ofReal (R : TriadicCube d) :
    volume (openCubeSet R) = ENNReal.ofReal (cubeVolume R) := by
  rw [volume_openCubeSet_eq_volume_cubeSet, ← cubeMeasure_apply_univ R]
  exact cubeMeasure_apply_univ_eq R

private theorem toReal_volume_openCubeSet (R : TriadicCube d) :
    (volume (openCubeSet R)).toReal = cubeVolume R := by
  rw [volume_openCubeSet_eq_ofReal R]
  exact ENNReal.toReal_ofReal (le_of_lt (cubeVolume_pos R))

/-- **Bridge one.**  For a nonnegative density integrable on the cube, the
manuscript's real normalized average and `CoarseGraining`'s `ℝ≥0∞` normalized cube integral
are the same number. -/
theorem volumeAverage_eq_toReal_lintegral (R : TriadicCube d) {f : Vec d → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hint : IntegrableOn f (openCubeSet R) volume) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂normalizedCubeMeasure R) =
      ENNReal.ofReal (volumeAverage (openCubeSet R) f) := by
  have hvolpos : 0 < cubeVolume R := cubeVolume_pos R
  have hrestrict : volume.restrict (cubeSet R) = volume.restrict (openCubeSet R) :=
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R
  have hae : 0 ≤ᵐ[volume.restrict (openCubeSet R)] f :=
    Filter.Eventually.of_forall hf0
  have hbase : (∫⁻ x, ENNReal.ofReal (f x) ∂(volume.restrict (openCubeSet R))) =
      ENNReal.ofReal (∫ x in openCubeSet R, f x ∂volume) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hae).symm
  rw [normalizedCubeMeasure, cubeMeasure, hrestrict, MeasureTheory.lintegral_smul_measure,
    hbase, smul_eq_mul, ← ENNReal.ofReal_mul (by
      exact le_of_lt (inv_pos.mpr hvolpos))]
  rw [volumeAverage, toReal_volume_openCubeSet R]

/-! ## 2. Bridge two: descendants versus the manuscript's lattice translates -/

/-- The triadic shift of a cube is its centre. -/
theorem triadicCubeShift_eq_cubeCenter (R : TriadicCube d) :
    triadicCubeShift R = cubeCenter R := rfl

/-- The centre of a triadic cube lies on the lattice `3^{scale} ℤ^d` — the
manuscript's `z ∈ 3^{j₀}ℤ^d`. -/
theorem triadicCubeShift_mem_lattice (R : TriadicCube d) :
    ∀ i, triadicCubeShift R i = ((R.index i : ℤ) : ℝ) * (3 : ℝ) ^ R.scale := by
  intro i
  rw [triadicCubeShift, cubeScaleFactor]

/-- **Bridge two.**  Each depth-`j` descendant of `Q` is exactly one of the
manuscript's lattice translates `z + □_{j₀}` at `j₀ = Q.scale - j`, with
`z ∈ 3^{j₀}ℤ^d ∩ □_{Q.scale}`.

The four conjuncts are the four things a consumer of route (a) needs: the
scale, the translate spelling that the main statements' windows use (`(fun y =>
z + y) '' openCubeSet (originCube d j₀)`), the lattice membership of the
centre, and its membership in the ambient cube. -/
theorem latticeTranslate_of_mem_descendantsAtDepth {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    R.scale = Q.scale - (j : ℤ) ∧
      openCubeSet R =
        (fun y => triadicCubeShift R + y) '' openCubeSet (originCube d R.scale) ∧
      (∀ i, triadicCubeShift R i = ((R.index i : ℤ) : ℝ) * (3 : ℝ) ^ R.scale) ∧
      triadicCubeShift R ∈ openCubeSet Q := by
  refine ⟨scale_eq_sub_of_mem_descendantsAtDepth hR, ?_,
    triadicCubeShift_mem_lattice R, ?_⟩
  · rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R]
    exact (Algsuperdiff.Section4.Provider.ExcessDecay.image_add_eq_translateSet
      (triadicCubeShift R) (openCubeSet (originCube d R.scale))).symm
  · refine openCubeSet_subset_of_mem_descendantsAtDepth hR ?_
    rw [triadicCubeShift_eq_cubeCenter, ← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos R)

end

end Algsuperdiff.Section4.Provider.Homogenization
