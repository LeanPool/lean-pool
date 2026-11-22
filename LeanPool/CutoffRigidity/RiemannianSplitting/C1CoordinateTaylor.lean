/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.Linarith

/-! # Uniform first-order Taylor control for actual C¹ coordinate fields -/

@[expose] public section
namespace CutoffRigidity
open Set Filter Metric
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Compact path tubes make the C¹ Taylor remainder uniform in the base point. -/
theorem uniform_c1_taylor_remainder_closedBall {F : E → E}
    (hf : ContDiff ℝ 1 F) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ closedBall (0 : E) R, ∀ h : E, ‖h‖ ≤ δ →
      ‖F (a + h) - F a - fderiv ℝ (F) a h‖ ≤ ε * ‖h‖ := by
  have hG := hf
  have hUC := (isCompact_closedBall (0 : E) (R + 1)).uniformContinuousOn_of_continuous
    (hG.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨η, hη, hηbound⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  let δ := min 1 (η / 2)
  have hδ : 0 < δ := lt_min zero_lt_one (half_pos hη)
  refine ⟨δ, hδ, ?_⟩
  intro a ha h hh
  have haR : ‖a‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using ha
  have haS : a ∈ closedBall (0 : E) (R + 1) := by
    rw [mem_closedBall, dist_zero_right]
    linarith
  let Remainder := fun z => F z - F a - fderiv ℝ (F) a (z - a)
  have hD (z : E) : HasFDerivAt Remainder (fderiv ℝ (F) z - fderiv ℝ (F) a) z := by
    have hh := ((hG.differentiable one_ne_zero z).hasFDerivAt.sub_const (F a)).sub
      ((fderiv ℝ (F) a).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const a))
    convert! hh using 1
  have hbound (z : E) (hz : z ∈ closedBall a δ) :
      ‖fderiv ℝ (F) z - fderiv ℝ (F) a‖ ≤ ε := by
    have hza : ‖z - a‖ ≤ δ := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hzS : z ∈ closedBall (0 : E) (R + 1) := by
      rw [mem_closedBall, dist_zero_right]
      have hn := norm_le_norm_sub_add z a
      have hd1 : δ ≤ 1 := min_le_left _ _
      linarith
    have hdist : dist z a < η := by
      rw [dist_eq_norm]
      have hdη : δ ≤ η / 2 := min_le_right _ _
      linarith
    simpa only [dist_eq_norm] using (hηbound z hzS a haS hdist).le
  have hbase : a ∈ closedBall a δ := mem_closedBall_self hδ.le
  have hhpoint : a + h ∈ closedBall a δ := by simpa only [mem_closedBall, dist_eq_norm,
    add_sub_cancel_left] using hh
  have hm := (convex_closedBall a δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hD z).hasFDerivWithinAt) hbound hbase hhpoint
  simpa only [Remainder, sub_self, map_zero, sub_zero, add_sub_cancel_left] using hm

end CutoffRigidity
