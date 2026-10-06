/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakGradient

/-!
# High-contrast homogenization: Analytic.AffineH10Norm

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Norm convergence under an affine pullback

The determinant change of variables rescales scalar `L²` seminorms by a
finite constant.  Coordinatewise convergence therefore remains convergence
after applying a fixed finite matrix.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The scalar `L²` seminorm acquires the square root of the inverse Jacobian
under an invertible affine pullback. -/
theorem eLpNorm_affinePullback {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict U)) :
    eLpNorm (fun y ↦ f (matVecMul L y)) 2
        (volume.restrict (matImage L⁻¹ U)) =
      ENNReal.ofReal (|L.det|⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
        eLpNorm f 2 (volume.restrict U) := by
  let T : Vec d → Vec d := matVecMul L
  have hmap := map_restrict_volume_affinePullback hL hU
  have hfmap : AEStronglyMeasurable f
      (Measure.map T (volume.restrict (matImage L⁻¹ U))) := by
    rw [hmap]
    exact hf.mono_ac Measure.smul_absolutelyContinuous
  have heq : eLpNorm f 2
        (Measure.map T (volume.restrict (matImage L⁻¹ U))) =
      eLpNorm (fun y ↦ f (T y)) 2
        (volume.restrict (matImage L⁻¹ U)) :=
    eLpNorm_map_measure (p := 2) (g := f) (f := T) hfmap
      (continuous_matVecMul L).aemeasurable
  rw [hmap, eLpNorm_smul_measure_of_ne_zero] at heq
  · exact heq.symm
  · exact ENNReal.ofReal_ne_zero_iff.mpr
      (inv_pos.mpr (abs_pos.mpr hL.ne_zero))

/-- A finite sum of measurable scalar fields converges in `L²` when each
summand does. -/
theorem tendsto_eLpNorm_finset_sum_zero {ι : Type*} [Fintype ι]
    (f : ℕ → ι → Vec d → ℝ) (mu : Measure (Vec d))
    (_hmeas : ∀ n i, AEStronglyMeasurable (f n i) mu)
    (htend : ∀ i, Filter.Tendsto (fun n ↦ eLpNorm (f n i) 2 mu)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ eLpNorm (∑ i, f n i) 2 mu)
      Filter.atTop (nhds 0) := by
  classical
  have hupper : ∀ n,
      eLpNorm (∑ i, f n i) 2 mu ≤ ∑ i, eLpNorm (f n i) 2 mu := by
    intro n
    exact eLpNorm_sum_le (p := 2) (by norm_num)
  have hsum : Filter.Tendsto (fun n ↦ ∑ i, eLpNorm (f n i) 2 mu)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ ↦ htend i)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hsum) ε hε] with n hn
  exact (hupper n).trans hn

end

end HighContrast
end HCPolySupport
