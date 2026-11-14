/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.Sphere

/-!
# Radial integration on the Euclidean carrier

Radial integration in physical Euclidean three-space, for nonnegative Borel functions.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LiebThirring

/-- Radial integration in physical Euclidean three-space, for nonnegative Borel functions. -/
theorem lintegral_norm (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x : Position, g ‖x‖ = ENNReal.ofReal (4 * Real.pi) *
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * g r := by
  calc
    _ = ∫⁻ x : ({(0 : Position)}ᶜ : Set Position), g ‖x.1‖
        ∂((volume : Measure Position).comap Subtype.val) := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl (fun x : Position => g ‖x‖),
        restrict_compl_singleton]
    _ = ∫⁻ x, g x.2 ∂(volume : Measure Position).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ Position - 1)) := by
      simpa only [Function.comp_def, homeomorphUnitSphereProd_apply_snd_coe] using
        (volume : Measure Position).measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
          (Homeomorph.measurableEmbedding _) (g ∘ Subtype.val ∘ Prod.snd)
    _ = _ := by
      rw [lintegral_prod (fun x : sphere (0 : Position) 1 × Ioi (0 : ℝ) => g x.2)
        (hg.comp (measurable_subtype_coe.comp measurable_snd)).aemeasurable]
      simp only [lintegral_const]
      rw [sphere_area, mul_comm]
      congr 1
      simp only [Position, finrank_euclideanSpace_fin, Nat.reduceSub,
        Measure.volumeIoiPow]
      rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
        (show Measurable (fun r : Ioi (0 : ℝ) => g r) from
          hg.comp measurable_subtype_coe)]
      simp only [Pi.mul_apply]
      rw [lintegral_subtype_comap measurableSet_Ioi (fun r : ℝ => ENNReal.ofReal (r ^ 2) * g r)]

end LiebThirring

end
