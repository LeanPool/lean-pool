/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsConstants

/-!
# Contractivity of the genuine variational Gibbs resolvent

The graph norm makes the actual Sobolev inclusion a contraction. Its adjoint
and the resulting L² resolvent are contractions as well. Constants are fixed
by this actual resolvent, with no stochastic invariance assertion.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem norm_gibbsSobolevInclusion_apply_le {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : gibbsSobolevGraph hV hprob) :
    ‖gibbsSobolevInclusion hV hprob u‖ ≤ ‖u‖ := by
  have hn := gibbsSobolev_norm_sq hV hprob u
  have he := gibbsDirichletEnergy_nonneg hV hprob u
  nlinarith [norm_nonneg u, norm_nonneg (gibbsSobolevInclusion hV hprob u)]

theorem norm_gibbsSobolevInclusion_le_one {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    ‖gibbsSobolevInclusion hV hprob‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (gibbsSobolevInclusion hV hprob) (by norm_num)
  intro u
  simpa only [one_mul] using norm_gibbsSobolevInclusion_apply_le hV hprob u

theorem norm_gibbsWeakResolvent_le_one {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    ‖gibbsWeakResolvent hV hprob‖ ≤ 1 := by
  change ‖(gibbsSobolevInclusion hV hprob).adjoint‖ ≤ 1
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact norm_gibbsSobolevInclusion_le_one hV hprob

theorem norm_gibbsL2Resolvent_le_one {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    ‖gibbsL2Resolvent hV hprob‖ ≤ 1 := by
  change ‖(gibbsSobolevInclusion hV hprob).comp (gibbsWeakResolvent hV hprob)‖ ≤ 1
  have hJ := norm_gibbsSobolevInclusion_le_one hV hprob
  have hR := norm_gibbsWeakResolvent_le_one hV hprob
  exact ContinuousLinearMap.opNorm_comp_le _ _ |>.trans
    (by nlinarith [norm_nonneg (gibbsSobolevInclusion hV hprob),
      norm_nonneg (gibbsWeakResolvent hV hprob)])

/-- The actual variational L² resolvent fixes every constant. -/
theorem gibbsL2Resolvent_constant {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (c : ℝ) :
    gibbsL2Resolvent hV hprob (gibbsConstantLp hprob c) = gibbsConstantLp hprob c := by
  have hg := gibbsConstantLp_graph_mem hV hprob c
  change (gibbsConstantLp hprob c, 0) ∈
    (positiveResolventOperator (gibbsL2Resolvent hV hprob)).graph at hg
  rw [positiveResolventOperator_graph _ (gibbsL2Resolvent_injective hV hprob),
    mem_positiveResolventGraph] at hg
  obtain ⟨f, hf, hzero⟩ := hg
  have heq : f = gibbsConstantLp hprob c := by rw [sub_eq_zero] at hzero; exact hzero.trans hf
  simpa only [heq] using hf

end CutoffRigidity
