/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialKernelTaylorReal

/-!
# Literal polynomial moments of the original compact spatial tests
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory
open scoped BigOperators

/-- Spatial monomial given by `∏ j, (x j : ℂ) ^ α j`. -/
noncomputable def spatialMonomial (α : Fin 3 → ℕ) (x : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ∏ j, (x j : ℂ) ^ α j

/-- Spatial test moment given by `∫ x, spatialMonomial α x * (f.1 x : ℂ)`. -/
noncomputable def spatialTestMoment (f : SpatialTestFunction) (α : Fin 3 → ℕ) : ℂ :=
  ∫ x, spatialMonomial α x * (f.1 x : ℂ)

theorem continuous_spatialMonomial (α : Fin 3 → ℕ) : Continuous (spatialMonomial α) := by
  unfold spatialMonomial
  fun_prop

theorem integrable_spatialTestMoment (f : SpatialTestFunction) (α : Fin 3 → ℕ) :
    Integrable (fun x => spatialMonomial α x * (f.1 x : ℂ)) := by
  have hc := (continuous_spatialMonomial α).mul (Complex.continuous_ofReal.comp f.2.1.continuous)
  apply hc.integrable_of_hasCompactSupport
  exact (f.2.2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).mul_left

theorem spatialMonomial_norm_le {a : ℝ} (α : Fin 3 → ℕ)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : ∀ j, ‖x j‖ ≤ a) :
    ‖spatialMonomial α x‖ ≤ a ^ (∑ j, α j) := by
  simp only [spatialMonomial, norm_prod, norm_pow, Complex.norm_real]
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
    (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hx j) _)

theorem spatialTestMoment_norm_le {a : ℝ}
    (f : SpatialTestFunction) (hf : ∀ x, f.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ a)
    (α : Fin 3 → ℕ) :
    ‖spatialTestMoment f α‖ ≤ a ^ (∑ j, α j) * ∫ x, ‖f.1 x‖ := by
  have hint : Integrable f.1 := f.2.1.continuous.integrable_of_hasCompactSupport f.2.2
  have hb (x : EuclideanSpace ℝ (Fin 3)) :
      ‖spatialMonomial α x * (f.1 x : ℂ)‖ ≤ a ^ (∑ j, α j) * ‖f.1 x‖ := by
    by_cases hx : f.1 x = 0
    · simp [hx]
    · rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (spatialMonomial_norm_le α x (hf x hx)) (norm_nonneg _)
  apply (norm_integral_le_of_norm_le (hint.norm.const_mul _)
    (Filter.Eventually.of_forall hb)).trans_eq
  exact integral_const_mul _ _

theorem spatialMonomial_pair_half_bound {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (α β : Fin 3 → ℕ) (c : ℂ)
    (hc : ‖c‖ ≤ M * R⁻¹ ^ ((∑ j, α j) + ∑ j, β j))
    (x y : EuclideanSpace ℝ (Fin 3))
    (hx : ∀ j, ‖x j‖ ≤ R / 2) (hy : ∀ j, ‖y j‖ ≤ R / 2) :
    ‖c * spatialMonomial α x * spatialMonomial β y‖ ≤
      M * (1 / 2 : ℝ) ^ ((∑ j, α j) + ∑ j, β j) := by
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (M * R⁻¹ ^ ((∑ j, α j) + ∑ j, β j)) *
        (R / 2) ^ (∑ j, α j) * (R / 2) ^ (∑ j, β j) := by
      exact mul_le_mul
        (mul_le_mul hc (spatialMonomial_norm_le α x hx)
          (norm_nonneg _) (by positivity))
        (spatialMonomial_norm_le β y hy) (norm_nonneg _) (by positivity)
    _ = M * (1 / 2 : ℝ) ^ ((∑ j, α j) + ∑ j, β j) := by
      rw [show (M * R⁻¹ ^ ((∑ j, α j) + ∑ j, β j)) *
          (R / 2) ^ (∑ j, α j) * (R / 2) ^ (∑ j, β j) =
          M * (R⁻¹ ^ ((∑ j, α j) + ∑ j, β j) *
            ((R / 2) ^ (∑ j, α j) * (R / 2) ^ (∑ j, β j))) by ring,
        ← pow_add, ← mul_pow]
      congr 2
      field_simp

end VacuumBellSeparation
