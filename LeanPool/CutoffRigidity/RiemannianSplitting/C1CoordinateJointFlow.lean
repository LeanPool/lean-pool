/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.LinearVariationJointContinuity
public import LeanPool.CutoffRigidity.RiemannianSplitting.CoordinateFlowTangentEvolution
public import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! # Genuine joint `C¹` regularity of actual coordinate flow families -/

@[expose] public section
open Set Filter Metric Function
open scoped Topology NNReal

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Actual linear variations, their proved joint continuity, and the actual
time ODE give joint `C¹` flow regularity. No partial or total differentiability
of the initial-point solution map is assumed. -/
theorem contDiffOn_coordinateFlow_joint_short_of_bound
    {F : E → E} (hF : ContDiff ℝ 1 F) {α : E → ℝ → E}
    (x₀ : E) {r T : ℝ} (_hr : 0 < r) (hT : 0 < T)
    (hαzero : ∀ y ∈ closedBall x₀ r, α y 0 = y)
    (hαD : ∀ y ∈ closedBall x₀ r, ∀ s ∈ Icc (-T) T,
      HasDerivAt (α y) (F (α y s)) s)
    {L : ℝ≥0} (hαLip : ∀ s ∈ Icc (-T) T,
      LipschitzOnWith L (fun y ↦ α y s) (closedBall x₀ r))
    (hαC : ContinuousOn (uncurry α) (closedBall x₀ r ×ˢ Icc (-T) T))
    {M : ℝ≥0} (hM : ∀ y ∈ closedBall x₀ r, ∀ s ∈ Icc (-T) T,
      ‖fderiv ℝ F (α y s)‖ ≤ M)
    (hshort : 2 * (M : ℝ) * T ≤ 1) :
    ContDiffOn ℝ 1 (uncurry α) (ball x₀ r ×ˢ Ioo (-(T / 2)) (T / 2)) := by
  classical
  let S := closedBall x₀ r
  have hex (p : E) (hp : p ∈ S) : ∃ J : ℝ → E →L[ℝ] E,
      J 0 = ContinuousLinearMap.id ℝ E ∧ ContinuousOn J (Icc (-T) T) ∧
      ∀ s ∈ Icc (-T) T, HasDerivWithinAt J
        ((fderiv ℝ F (α p s)).comp (J s)) (Icc (-T) T) s := by
    apply exists_linear_variation_short_interval hT.le _ (hM p hp) hshort
    exact (hF.continuous_fderiv one_ne_zero).comp_continuousOn
      (fun s hs ↦ (hαD p hp s hs).continuousAt.continuousWithinAt)
  choose J hJzero hJC hJD using hex
  let j : E → ℝ → E →L[ℝ] E := fun p ↦
    if hp : p ∈ S then J p hp else fun _ ↦ ContinuousLinearMap.id ℝ E
  have hjzero (p : E) (hp : p ∈ S) : j p 0 = ContinuousLinearMap.id ℝ E := by
    simpa only [j, dite_eq_left hp] using hJzero p hp
  have hsub : Icc (-(T / 2)) (T / 2) ⊆ Icc (-T) T := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hjD (p : E) (hp : p ∈ S) (s : ℝ) (hs : s ∈ Icc (-(T / 2)) (T / 2)) :
      HasDerivAt (j p) ((fderiv ℝ F (α p s)).comp (j p s)) s := by
    have hsT : s ∈ Ioo (-T) T := by constructor <;> linarith [hs.1, hs.2]
    simpa only [j, dite_eq_left hp] using
      (hJD p hp s (hsub hs)).hasDerivAt (Icc_mem_nhds hsT.1 hsT.2)
  have hJA := (hF.continuous_fderiv one_ne_zero).comp_continuousOn
    (hαC.mono (Set.prod_mono Subset.rfl hsub))
  have hjcont : ContinuousOn (uncurry j) (S ×ˢ Icc (-(T / 2)) (T / 2)) :=
    continuousOn_linearVariation_joint_symmetric (isCompact_closedBall x₀ r) (half_pos hT).le
      hJA hjzero hjD (fun p hp s hs ↦ hM p hp s (hsub hs))
  have hspace (p : E) (hp : p ∈ ball x₀ r) (t : ℝ)
      (ht : t ∈ Icc (-(T / 2)) (T / 2)) :
      HasFDerivAt (fun y ↦ α y t) (j p t) p := by
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hp)
    have hδS : ball p δ ⊆ S := hδsub.trans ball_subset_closedBall
    apply hasFDerivAt_coordinateFlow_of_symmetric_variation hF p hδ (half_pos hT)
      (fun y hy ↦ hαzero y (hδS hy))
      (fun y hy s hs ↦ hαD y (hδS hy) s (hsub hs))
      (fun s hs ↦ (hαLip s (hsub hs)).mono hδS)
      (hjzero p (ball_subset_closedBall hp))
      (hjD p (ball_subset_closedBall hp)) ht
  let U := ball x₀ r ×ˢ Ioo (-(T / 2)) (T / 2)
  have hU : IsOpen U := isOpen_ball.prod isOpen_Ioo
  have hUS : U ⊆ S ×ˢ Icc (-(T / 2)) (T / 2) :=
    Set.prod_mono ball_subset_closedBall Ioo_subset_Icc_self
  let B := fun p : E × ℝ ↦ (1 : ℝ →L[ℝ] ℝ).smulRight (F (α p.1 p.2))
  have hB : ContinuousOn B U :=
    (((ContinuousLinearMap.smulRightL ℝ ℝ E) 1).continuous).comp_continuousOn
      (hF.continuous.comp_continuousOn ((hαC.mono (Set.prod_mono Subset.rfl hsub)).mono hUS))
  let D := fun p : E × ℝ ↦ (j p.1 p.2).coprod (B p)
  have hDcont : ContinuousOn D U := (hjcont.mono hUS).continuousLinearMapCoprod hB
  have hD (p : E × ℝ) (hp : p ∈ U) : HasFDerivAt (uncurry α) (D p) p := by
    apply (hasStrictFDerivAt_uncurry_coprod (f := α) (f₁ := j)
      (f₂ := fun y t ↦ B (y, t)) (u := p) ?_ ?_ ?_ ?_).hasFDerivAt
    · filter_upwards [hU.mem_nhds hp] with q hq
      exact hspace q.1 hq.1 q.2 (Ioo_subset_Icc_self hq.2)
    · filter_upwards [hU.mem_nhds hp] with q hq
      exact (hαD q.1 (ball_subset_closedBall hq.1) q.2
        (hsub (Ioo_subset_Icc_self hq.2))).hasFDerivAt
    · exact (hjcont.mono hUS).continuousAt (hU.mem_nhds hp)
    · exact hB.continuousAt (hU.mem_nhds hp)
  intro p hp
  have hc : ContDiffAt ℝ 1 (uncurry α) p := by
    apply (contDiffAt_succ_iff_hasFDerivAt (n := 0)).mpr
    refine ⟨D, ⟨U, hU.mem_nhds hp, hD⟩, ?_⟩
    exact contDiffAt_zero.mpr ⟨U, hU.mem_nhds hp, hDcont⟩
  exact hc.contDiffWithinAt

end CutoffRigidity
