/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsOperatorIntegratedBochner
public import LeanPool.CutoffRigidity.GibbsSobolevConstants

/-! # Genuine cutoff limits for actual operator eigenvectors -/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integral_norm_sq_L2_vector {μ : Measure E} (G : E →₂[μ] E) :
    (∫ x, ‖G x‖ ^ 2 ∂μ) = ‖G‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => (real_inner_self_eq_norm_sq (G x)).symm)

theorem L2_vector_cutoff_boundary_bound {μ : Measure E} (G : E →₂[μ] E)
    {η : E → ℝ} (hη : ContDiff ℝ 2 η) (M : ℝ) (hM : 0 ≤ M)
    (hgrad : ∀ x, ‖gradient η x‖ ≤ M) :
    Integrable (fun x => ‖gradient η x‖ ^ 2 * ‖G x‖ ^ 2) μ ∧
      (∫ x, ‖gradient η x‖ ^ 2 * ‖G x‖ ^ 2 ∂μ) ≤ M ^ 2 * ‖G‖ ^ 2 := by
  have hnorm := (Lp.memLp G).norm.integrable_sq
  have hc := continuous_gradient_of_c1 (hη.of_le (by norm_num))
  have hpoint (x : E) : ‖gradient η x‖ ^ 2 * ‖G x‖ ^ 2 ≤ M ^ 2 * ‖G x‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) hM).mpr (hgrad x)) (sq_nonneg _)
  have hi : Integrable (fun x => ‖gradient η x‖ ^ 2 * ‖G x‖ ^ 2) μ := by
    apply (hnorm.const_mul (M ^ 2)).mono' (by fun_prop)
    filter_upwards with x
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hpoint x
  refine ⟨hi, ?_⟩
  have he := integral_mono hi (hnorm.const_mul (M ^ 2)) hpoint
  rw [integral_const_mul, integral_norm_sq_L2_vector] at he
  exact he

theorem L2_vector_cutoff_square_tendsto {μ : Measure E} (G : E →₂[μ] E)
    (η : ℕ → E → ℝ) (hη : ∀ n, Measurable (η n))
    (hηbounds : ∀ n x, 0 ≤ η n x ∧ η n x ≤ 1)
    (hηone : ∀ x, ∀ᶠ n : ℕ in atTop, η n x = 1) :
    Tendsto (fun n => ∫ x, η n x ^ 2 * ‖G x‖ ^ 2 ∂μ) atTop (𝓝 (‖G‖ ^ 2)) := by
  simpa only [integral_norm_sq_L2_vector] using
    cutoff_square_integral_tendsto (Lp.memLp G).norm.integrable_sq
      (fun x => sq_nonneg ‖G x‖) η hη hηbounds hηone

/-- Genuine ordinary-volume local integrability of every coordinate of
an actual Gibbs L² vector field. -/
theorem gibbsVector_coordinate_locallyIntegrable_volume {V : E → ℝ}
    (hV : Continuous V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (G : E →₂[gibbsMeasure volume V] E) (i : Fin d) :
    LocallyIntegrable (fun x => (G x) i) volume := by
  have he := (EuclideanSpace.proj i : E →L[ℝ] ℝ).coeFn_compLp G
  exact (gibbsLp_locallyIntegrable_volume hV hp
    ((EuclideanSpace.proj i : E →L[ℝ] ℝ).compLp G)).congr
      ((gibbsMeasure_ae_eq_iff volume hV.measurable).mp he)

end CutoffRigidity
