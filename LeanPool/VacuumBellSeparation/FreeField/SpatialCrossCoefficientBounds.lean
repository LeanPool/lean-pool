/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialCrossMomentIndex
public import LeanPool.VacuumBellSeparation.Gaussian.SpatialWeightedCoefficientSeries

/-!
# Full coefficient bounds for both literal spatial kernels

The vector estimates remain the weighted-moment interface. The complete
coefficient sum, including both field and momentum sectors, is proved.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F]

theorem spatialCross_weighted_vector_series {μ s B Af Ap Cf Cp : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hB : 0 < B)
    (hAf : 0 ≤ Af) (hAp : 0 ≤ Ap)
    (hsep : 16 * Real.sqrt 3 * B ≤ s)
    (u : SpatialCrossIndex → E) (v : SpatialCrossIndex → F)
    (huf : ∀ k, ‖u (.inl k)‖ ≤ Af * B ^ (∑ j, k.1 j))
    (hup : ∀ k, ‖u (.inr k)‖ ≤ Ap * B ^ (∑ j, k.1 j))
    (hvf : ∀ k, ‖v (.inl k)‖ ≤ Cf * B ^ (∑ j, k.2 j))
    (hvp : ∀ k, ‖v (.inr k)‖ ≤ Cp * B ^ (∑ j, k.2 j)) :
    Summable (fun i => ‖(spatialCrossCoefficient μ s (2 * B) i : ℂ) • u i‖ * ‖v i‖) ∧
      (∑' i, ‖(spatialCrossCoefficient μ s (2 * B) i : ℂ) • u i‖ * ‖v i‖) ≤
        64 * spatialFieldPolydiscBound μ s (2 * B) * Af * Cf +
        64 * spatialMomentumPolydiscBound μ s (2 * B) * Ap * Cp := by
  let f : SpatialMomentIndex → ℝ := fun k =>
    ‖((spatialFieldMultiCoefficient μ s (2 * B) k.1 k.2).re : ℂ) • u (.inl k)‖ * ‖v (.inl k)‖
  let g : SpatialMomentIndex → ℝ := fun k =>
    ‖((spatialMomentumMultiCoefficient μ s (2 * B) k.1 k.2).re : ℂ) • u (.inr k)‖ * ‖v (.inr k)‖
  have hfbound (k : SpatialMomentIndex) : f k ≤
      (spatialFieldPolydiscBound μ s (2 * B) * Af * Cf) *
        (1 / 2 : ℝ) ^ ((∑ j, k.1 j) + ∑ j, k.2 j) := by
    apply coefficient_weighted_vector_product_le hB
      (by unfold spatialFieldPolydiscBound; positivity) hAf k.1 k.2 _ _ _ _ (huf k) (hvf k)
    apply (show ‖((spatialFieldMultiCoefficient μ s (2 * B) k.1 k.2).re : ℂ)‖ ≤
        ‖spatialFieldMultiCoefficient μ s (2 * B) k.1 k.2‖ by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Complex.abs_re_le_norm
        (spatialFieldMultiCoefficient μ s (2 * B) k.1 k.2)).trans
    exact spatialFieldMultiCoefficient_norm_le hμ hs (by positivity) (by nlinarith) _ _
  have hgbound (k : SpatialMomentIndex) : g k ≤
      (spatialMomentumPolydiscBound μ s (2 * B) * Ap * Cp) *
        (1 / 2 : ℝ) ^ ((∑ j, k.1 j) + ∑ j, k.2 j) := by
    apply coefficient_weighted_vector_product_le hB
      (by unfold spatialMomentumPolydiscBound; positivity) hAp k.1 k.2 _ _ _ _ (hup k) (hvp k)
    apply (show ‖((spatialMomentumMultiCoefficient μ s (2 * B) k.1 k.2).re : ℂ)‖ ≤
        ‖spatialMomentumMultiCoefficient μ s (2 * B) k.1 k.2‖ by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Complex.abs_re_le_norm
        (spatialMomentumMultiCoefficient μ s (2 * B) k.1 k.2)).trans
    exact spatialMomentumMultiCoefficient_norm_le hμ hs (by positivity) (by nlinarith) _ _
  have hmf := hasSum_six_moment_geometric.mul_left
    (spatialFieldPolydiscBound μ s (2 * B) * Af * Cf)
  have hmp := hasSum_six_moment_geometric.mul_left
    (spatialMomentumPolydiscBound μ s (2 * B) * Ap * Cp)
  have hf : Summable f := hmf.summable.of_nonneg_of_le
    (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hfbound
  have hg : Summable g := hmp.summable.of_nonneg_of_le
    (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hgbound
  have hj : HasSum (fun i => ‖(spatialCrossCoefficient μ s (2 * B) i : ℂ) • u i‖ * ‖v i‖)
      ((∑' k, f k) + ∑' k, g k) := hf.hasSum.sum hg.hasSum
  refine ⟨hj.summable, hj.tsum_eq.trans_le ?_⟩
  apply (add_le_add (hf.tsum_le_tsum hfbound hmf.summable)
    (hg.tsum_le_tsum hgbound hmp.summable)).trans_eq
  rw [hmf.tsum_eq, hmp.tsum_eq]
  ring

end VacuumBellSeparation
