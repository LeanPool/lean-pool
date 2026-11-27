/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CompactPolydiscCoefficientIntegral

/-!
# Additivity of actual contour coefficients on continuous functions

Continuity on the compact coordinate ball supplies the actual angular
integrability required by the Bochner additivity theorem.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Metric Set
open scoped BigOperators

theorem integrable_angularCoefficient_of_continuous (n : ℕ) {R : ℝ} (hR : 0 < R)
    (F : (Fin n → ℂ) → ℂ) (hF : Continuous F) (k : Fin n → ℕ) :
    Integrable (fun θ => F (polydiscBoundaryPoint n R θ) *
      ∏ j, (polydiscBoundaryPoint n R θ j)⁻¹ ^ k j) (polydiscAngleMeasure n) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Fin n → ℂ) R).exists_bound_of_continuousOn
    hF.continuousOn
  apply (integrable_const (max M 0 * ∏ j, R⁻¹ ^ k j)).mono'
    (continuous_boundary_coefficient_weight n hR F
      (hF.comp (continuous_polydiscBoundaryPoint n R)) k).aestronglyMeasurable
  refine Filter.Eventually.of_forall fun θ => ?_
  have hz : polydiscBoundaryPoint n R θ ∈ closedBall (0 : Fin n → ℂ) R := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR.le]
    exact fun j => (norm_polydiscBoundaryPoint n hR.le θ j).le
  simp only [norm_mul, norm_prod, norm_pow, norm_inv, norm_polydiscBoundaryPoint n hR.le]
  exact mul_le_mul_of_nonneg_right ((hM _ hz).trans (le_max_left _ _)) (by positivity)

theorem polydiscCoefficient_add_of_continuous (n : ℕ) {R : ℝ} (hR : 0 < R)
    (F G : (Fin n → ℂ) → ℂ) (hF : Continuous F) (hG : Continuous G)
    (k : Fin n → ℕ) :
    polydiscCoefficient n R (fun z => F z + G z) k =
      polydiscCoefficient n R F k + polydiscCoefficient n R G k := by
  rw [polydiscCoefficient_eq_angular_of_continuous n hR (fun z => F z + G z)
      (show Continuous (fun z => F z + G z) from hF.add hG),
    polydiscCoefficient_eq_angular_of_continuous n hR _ hF,
    polydiscCoefficient_eq_angular_of_continuous n hR _ hG]
  simp only [angularPolydiscCoefficient, polydiscAngularIntegral, add_mul]
  rw [integral_add (integrable_angularCoefficient_of_continuous n hR F hF k)
    (integrable_angularCoefficient_of_continuous n hR G hG k), mul_add]

end VacuumBellSeparation.Gaussian
