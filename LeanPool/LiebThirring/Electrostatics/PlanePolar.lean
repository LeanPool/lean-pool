/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import LeanPool.LiebThirring.Electrostatics.Plane

/-!
# Polar integration on the Euclidean plane

Planar polar integration for the singular Coulomb kernel.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring

/-- Nonnegative radial integration on the Euclidean plane, with angular mass `2π`. -/
theorem lintegral_planar_norm (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ q : Planar, g ‖q‖ = ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * g r := by
  let e := Complex.orthonormalBasisOneI.repr
  calc
    (∫⁻ q : Planar, g ‖q‖) = ∫⁻ z : ℂ, g ‖z‖ := by
      simpa only [Function.comp_def, e.norm_map] using
        (e.measurePreserving.lintegral_comp_emb e.toHomeomorph.measurableEmbedding
          (fun q : Planar => g ‖q‖)).symm
    _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 * g p.1 := by
      rw [← Complex.lintegral_comp_polarCoord_symm]
      apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      simp only [Complex.norm_polarCoord_symm, abs_of_pos hp.1, smul_eq_mul]
    _ = _ := by
      change (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * g p.1 ∂(volume.prod volume)) = _
      rw [← Measure.prod_restrict]
      have hf : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * g p.1) :=
        measurable_fst.ennreal_ofReal.mul (hg.comp measurable_fst)
      rw [lintegral_prod _ hf.aemeasurable]
      simp only [lintegral_const, Measure.restrict_apply_univ]
      rw [Real.volume_Ioo]
      have hπ : Real.pi - -Real.pi = 2 * Real.pi := by ring
      have hrg : Measurable (fun r : ℝ => ENNReal.ofReal r * g r) :=
        measurable_id.ennreal_ofReal.mul hg
      rw [hπ, lintegral_mul_const _ hrg]
      exact mul_comm _ _

end LiebThirring

end
