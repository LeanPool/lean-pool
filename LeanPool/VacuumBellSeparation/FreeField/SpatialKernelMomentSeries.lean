/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialTestMoments

/-!
# Actual termwise integration of a separated spatial kernel series

The full six-index geometric majorant has sum 64. The compact test
factors are kept in the dominating function, so the product spatial
measure need not be finite. Pointwise reconstruction is used only where
both tests are nonzero, before any half-polydisc domain argument.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory
open scoped BigOperators

theorem hasSum_spatialKernelMoments {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (c : (Fin 3 → ℕ) × (Fin 3 → ℕ) → ℂ)
    (K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hc : ∀ k, ‖c k‖ ≤ M * R⁻¹ ^ ((∑ j, k.1 j) + ∑ j, k.2 j))
    (hseries : ∀ x y, (∀ j, ‖x j‖ < R) → (∀ j, ‖y j‖ < R) →
      HasSum (fun k => c k * spatialMonomial k.1 x * spatialMonomial k.2 y) (K x y))
    (f g : SpatialTestFunction)
    (hf : ∀ x, f.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hg : ∀ y, g.1 y ≠ 0 → ∀ j, ‖y j‖ ≤ R / 2) :
    HasSum (fun k => c k * spatialTestMoment f k.1 * spatialTestMoment g k.2)
      (∫ xy, K xy.1 xy.2 * (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ) ∂volume.prod volume) := by
  let F := fun (k : (Fin 3 → ℕ) × (Fin 3 → ℕ))
      (xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
    c k * spatialMonomial k.1 xy.1 * spatialMonomial k.2 xy.2 *
      (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ)
  let b := fun (k : (Fin 3 → ℕ) × (Fin 3 → ℕ))
      (xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
    M * (1 / 2 : ℝ) ^ ((∑ j, k.1 j) + ∑ j, k.2 j) * ‖f.1 xy.1‖ * ‖g.1 xy.2‖
  have hfn : Integrable f.1 := f.2.1.continuous.integrable_of_hasCompactSupport f.2.2
  have hgn : Integrable g.1 := g.2.1.continuous.integrable_of_hasCompactSupport g.2.2
  have hb (k) (xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
      ‖F k xy‖ ≤ b k xy := by
    by_cases hfx : f.1 xy.1 = 0
    · simp [F, b, hfx]
    by_cases hgy : g.1 xy.2 = 0
    · simp [F, b, hgy]
    dsimp only [F, b]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (spatialMonomial_pair_half_bound hR hM k.1 k.2 (c k)
        (hc k) xy.1 xy.2 (hf xy.1 hfx) (hg xy.2 hgy)) (norm_nonneg _)) (norm_nonneg _)
  have hbs (xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
      HasSum (fun k => b k xy) (M * 64 * ‖f.1 xy.1‖ * ‖g.1 xy.2‖) :=
    ((hasSum_six_moment_geometric.mul_left M).mul_right ‖f.1 xy.1‖).mul_right ‖g.1 xy.2‖
  have hbint : Integrable (fun xy => ∑' k, b k xy) (volume.prod volume) := by
    simp_rw [(hbs _).tsum_eq]
    convert (hfn.norm.mul_prod hgn.norm).const_mul (M * 64) using 1
    funext xy
    ring
  have hsum := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.prod volume)
    (f := fun xy => K xy.1 xy.2 * (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ)) b
    (fun k => (show Continuous (F k) by
      have hfc := f.2.1.continuous
      have hgc := g.2.1.continuous
      have hα := continuous_spatialMonomial k.1
      have hβ := continuous_spatialMonomial k.2
      dsimp only [F]
      fun_prop).aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall (hb k))
    (Filter.Eventually.of_forall (fun xy => (hbs xy).summable)) hbint
    (Filter.Eventually.of_forall (fun xy => by
      by_cases hfx : f.1 xy.1 = 0
      · simp [F, hfx]
      by_cases hgy : g.1 xy.2 = 0
      · simp [F, hgy]
      exact ((hseries xy.1 xy.2
        (fun j => (hf xy.1 hfx j).trans_lt (by linarith))
        (fun j => (hg xy.2 hgy j).trans_lt (by linarith))).mul_right
          (f.1 xy.1 : ℂ)).mul_right (g.1 xy.2 : ℂ)))
  have hi (k : (Fin 3 → ℕ) × (Fin 3 → ℕ)) :
      (∫ xy, F k xy ∂volume.prod volume) =
        c k * spatialTestMoment f k.1 * spatialTestMoment g k.2 := by
    have heq (xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
        F k xy = c k * ((spatialMonomial k.1 xy.1 * (f.1 xy.1 : ℂ)) *
          (spatialMonomial k.2 xy.2 * (g.1 xy.2 : ℂ))) := by dsimp only [F]; ring
    simp_rw [heq]
    rw [integral_const_mul, integral_prod_mul
      (fun x => spatialMonomial k.1 x * (f.1 x : ℂ))
      (fun y => spatialMonomial k.2 y * (g.1 y : ℂ))]
    change c k * (spatialTestMoment f k.1 * spatialTestMoment g k.2) =
      c k * spatialTestMoment f k.1 * spatialTestMoment g k.2
    exact (mul_assoc _ _ _).symm
  simpa only [hi] using hsum

end VacuumBellSeparation
