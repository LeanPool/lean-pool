/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialKernelMultiIndex
public import LeanPool.VacuumBellSeparation.Gaussian.SpatialSeriesConstants

/-!
# Exact summation of the actual kernel coefficients against weighted vectors

The vector bounds are explicit inputs to this interface. The coefficient
decay is the proved bound on the literal Bessel contour coefficients,
and its complete six-index geometric sum is derived here.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped BigOperators ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F]

theorem coefficient_weighted_vector_product_le {B M A C : ℝ}
    (hB : 0 < B) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (α β : Fin 3 → ℕ) (c : ℂ)
    (hc : ‖c‖ ≤ M * (2 * B)⁻¹ ^ ((∑ j, α j) + ∑ j, β j))
    (u : E) (v : F) (hu : ‖u‖ ≤ A * B ^ (∑ j, α j))
    (hv : ‖v‖ ≤ C * B ^ (∑ j, β j)) :
    ‖c • u‖ * ‖v‖ ≤ (M * A * C) * (1 / 2 : ℝ) ^ ((∑ j, α j) + ∑ j, β j) := by
  rw [norm_smul]
  calc
    _ ≤ (M * (2 * B)⁻¹ ^ ((∑ j, α j) + ∑ j, β j)) *
        (A * B ^ (∑ j, α j)) * (C * B ^ (∑ j, β j)) :=
      mul_le_mul (mul_le_mul hc hu (norm_nonneg _) (by positivity)) hv (norm_nonneg _)
        (by positivity)
    _ = (M * A * C) * (1 / 2 : ℝ) ^ ((∑ j, α j) + ∑ j, β j) := by
      rw [show (M * (2 * B)⁻¹ ^ ((∑ j, α j) + ∑ j, β j)) *
          (A * B ^ (∑ j, α j)) * (C * B ^ (∑ j, β j)) =
          (M * A * C) * ((2 * B)⁻¹ ^ ((∑ j, α j) + ∑ j, β j) *
            (B ^ (∑ j, α j) * B ^ (∑ j, β j))) by ring,
        ← pow_add, ← mul_pow]
      rw [show (2 * B)⁻¹ * B = (1 / 2 : ℝ) by field_simp [ne_of_gt hB]]

theorem coefficient_weighted_vector_series {B M A C : ℝ}
    (hB : 0 < B) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (c : (Fin 3 → ℕ) × (Fin 3 → ℕ) → ℂ)
    (hc : ∀ k, ‖c k‖ ≤ M * (2 * B)⁻¹ ^ ((∑ j, k.1 j) + ∑ j, k.2 j))
    (u : (Fin 3 → ℕ) → E) (v : (Fin 3 → ℕ) → F)
    (hu : ∀ α, ‖u α‖ ≤ A * B ^ (∑ j, α j))
    (hv : ∀ β, ‖v β‖ ≤ C * B ^ (∑ j, β j)) :
    Summable (fun k => ‖c k • u k.1‖ * ‖v k.2‖) ∧
      (∑' k, ‖c k • u k.1‖ * ‖v k.2‖) ≤ 64 * M * A * C := by
  have hg := hasSum_six_moment_geometric.mul_left (M * A * C)
  have hb (k) := coefficient_weighted_vector_product_le hB hM hA k.1 k.2
    (c k) (hc k) (u k.1) (v k.2) (hu k.1) (hv k.2)
  have hs := hg.summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hb
  refine ⟨hs, (Summable.tsum_le_tsum hb hs hg.summable).trans_eq ?_⟩
  rw [hg.tsum_eq]
  ring

theorem spatialField_weighted_vector_series {μ s B A C : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hB : 0 < B) (hA : 0 ≤ A)
    (hsep : 16 * Real.sqrt 3 * B ≤ s)
    (u : (Fin 3 → ℕ) → E) (v : (Fin 3 → ℕ) → F)
    (hu : ∀ α, ‖u α‖ ≤ A * B ^ (∑ j, α j))
    (hv : ∀ β, ‖v β‖ ≤ C * B ^ (∑ j, β j)) :
    Summable (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      ‖spatialFieldMultiCoefficient μ s (2 * B) k.1 k.2 • u k.1‖ * ‖v k.2‖) ∧
      (∑' k : (Fin 3 → ℕ) × (Fin 3 → ℕ),
        ‖spatialFieldMultiCoefficient μ s (2 * B) k.1 k.2 • u k.1‖ * ‖v k.2‖) ≤
        64 * spatialFieldPolydiscBound μ s (2 * B) * A * C :=
  coefficient_weighted_vector_series hB
    (by unfold spatialFieldPolydiscBound; positivity) hA
    (fun k => spatialFieldMultiCoefficient μ s (2 * B) k.1 k.2)
    (fun k => spatialFieldMultiCoefficient_norm_le hμ hs (by positivity)
      (by nlinarith) k.1 k.2) u v hu hv

theorem spatialMomentum_weighted_vector_series {μ s B A C : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hB : 0 < B) (hA : 0 ≤ A)
    (hsep : 16 * Real.sqrt 3 * B ≤ s)
    (u : (Fin 3 → ℕ) → E) (v : (Fin 3 → ℕ) → F)
    (hu : ∀ α, ‖u α‖ ≤ A * B ^ (∑ j, α j))
    (hv : ∀ β, ‖v β‖ ≤ C * B ^ (∑ j, β j)) :
    Summable (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      ‖spatialMomentumMultiCoefficient μ s (2 * B) k.1 k.2 • u k.1‖ * ‖v k.2‖) ∧
      (∑' k : (Fin 3 → ℕ) × (Fin 3 → ℕ),
        ‖spatialMomentumMultiCoefficient μ s (2 * B) k.1 k.2 • u k.1‖ * ‖v k.2‖) ≤
        64 * spatialMomentumPolydiscBound μ s (2 * B) * A * C :=
  coefficient_weighted_vector_series hB
    (by unfold spatialMomentumPolydiscBound; positivity) hA
    (fun k => spatialMomentumMultiCoefficient μ s (2 * B) k.1 k.2)
    (fun k => spatialMomentumMultiCoefficient_norm_le hμ hs (by positivity)
      (by nlinarith) k.1 k.2) u v hu hv

end VacuumBellSeparation.Gaussian
