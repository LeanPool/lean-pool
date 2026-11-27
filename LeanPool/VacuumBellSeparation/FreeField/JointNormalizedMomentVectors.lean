/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CenteredWeightedSourceMoments

/-!
# Actual normalized centered moments with reserve weights

The factors s to minus the degree multiply the original Riesz vectors.
The source region, reserve, and centered test moments are unchanged.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification
open scoped InnerProductSpace

/-- Normalized centered source moment given by `s⁻¹ ^ (∑ j, α j) * centeredSpatialTestMoment a f
α`. -/
def normalizedCenteredSourceMoment (a : EuclideanSpace ℝ (Fin 3)) (s : ℝ)
    (f : SpatialTestFunction) (α : Fin 3 → ℕ) : ℝ :=
  s⁻¹ ^ (∑ j, α j) * centeredSpatialTestMoment a f α

theorem exists_normalized_centered_weighted_source_moments {b : ℝ}
    (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (μ : ℝ) (hμ : 0 < μ) (T s : ℝ) (_ : 0 < T) (_ : 0 < s)
        (a : EuclideanSpace ℝ (Fin 3)) (U : Set (EuclideanSpace ℝ (Fin 3))),
        U ⊆ Metric.ball a T → ∀ α : Fin 3 → ℕ,
          ∃ u v : ComplexSourceHilbert hμ U,
            ‖u‖ ≤ C * T / (1 + μ * T) * Real.exp (sourceMomentLambda b * μ * T) *
              (sourceMomentBase b * T / s) ^ (∑ j, α j) ∧
            ‖v‖ ≤ C * T ^ 2 / (1 + μ * T) ^ 2 * Real.exp (sourceMomentLambda b * μ * T) *
              (sourceMomentBase b * T / s) ^ (∑ j, α j) ∧
            (∀ x : SourceTestSpace hμ U,
              inner ℂ (ofReal (x : SourceHilbert hμ U)) ((sourceReserve hμ U ^ b) u) =
                (normalizedCenteredSourceMoment a s x.1.1 α : ℂ)) ∧
            (∀ x : SourceTestSpace hμ U,
              inner ℂ (ofReal (x : SourceHilbert hμ U)) ((sourceReserve hμ U ^ b) v) =
                (normalizedCenteredSourceMoment a s x.1.2 α : ℂ)) := by
  obtain ⟨C, hC, h⟩ := exists_centered_weightedSource_moment_vectors hb hb1
  refine ⟨C, hC, ?_⟩
  intro μ hμ T s hT hs a U hU α
  obtain ⟨u, v, hu, hv, hueq, hveq⟩ := h μ hμ T hT a U hU α
  let c : ℝ := s⁻¹ ^ (∑ j, α j)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hn (A B : ℝ) : c * (A * B ^ (∑ j, α j)) = A * (B / s) ^ (∑ j, α j) := by
    dsimp only [c]
    rw [div_eq_mul_inv, mul_pow]
    ring
  refine ⟨c • u, c • v, ?_, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left hu hc).trans_eq (hn _ _)
  · rw [norm_smul, Real.norm_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left hv hc).trans_eq (hn _ _)
  · intro x
    rw [LinearMapClass.map_smul_of_tower, inner_smul_right_eq_smul, hueq]
    simp only [normalizedCenteredSourceMoment, c, Complex.real_smul, Complex.ofReal_mul]
  · intro x
    rw [LinearMapClass.map_smul_of_tower, inner_smul_right_eq_smul, hveq]
    simp only [normalizedCenteredSourceMoment, c, Complex.real_smul, Complex.ofReal_mul]

end VacuumBellSeparation
