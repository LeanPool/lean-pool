/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortAverageMetric

/-!
# Geometry of the metric Gaussian cylinder

At the Gaussian time threshold, the averaging cylinder is bounded and
lies strictly inside the positive half-space time slab.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The metric Gaussian averaging cylinder lies in the positive
half-space slab when its center is above height two and its time is
small (`lem:bu-small-time`). -/
theorem bu_short_metric_average_subset_half_cylinder
    (X : Vec3) (t : ℝ) (hX : 2 < X 2)
    (ht : 0 < t) (htsmall : t < 1 / 12) :
    spaceTimeSet (Metric.ball X (Real.sqrt (3 * t)))
      (Ioo t (5 * t / 2)) ⊆
        spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) := by
  have hR : Real.sqrt (3 * t) < 1 := by
    have hsq : Real.sqrt (3 * t) ^ 2 = 3 * t :=
      Real.sq_sqrt (by positivity)
    have hroot : 0 ≤ Real.sqrt (3 * t) := Real.sqrt_nonneg _
    nlinarith only [hsq, hroot, htsmall]
  intro z hz
  have hdist : ‖z.1 - X‖ < Real.sqrt (3 * t) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz.1
  have hcoord : |z.1 2 - X 2| ≤ ‖z.1 - X‖ := by
    have h := norm_le_pi_norm (z.1 - X) 2
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using h
  have hheight : 0 < z.1 2 := by
    have hlow : -‖z.1 - X‖ ≤ z.1 2 - X 2 :=
      (neg_le_neg hcoord).trans (neg_abs_le _)
    nlinarith only [hX, hR, hdist, hcoord, hlow]
  have htime : z.2 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact ht.trans hz.2.1
    · have hupper : 5 * t / 2 < 1 := by linarith only [htsmall]
      exact hz.2.2.trans hupper
  exact ⟨hheight, htime⟩

/-- The metric Gaussian averaging cylinder is bounded in parabolic
space-time (`lem:bu-small-time`). -/
theorem bu_short_metric_average_bounded
    (X : Vec3) (t : ℝ) :
    Bornology.IsBounded
      (spaceTimeSet (Metric.ball X (Real.sqrt (3 * t)))
        (Ioo t (5 * t / 2))) := by
  let R := Real.sqrt (3 * t)
  let K : Set ParabolicPoint := parabolicHomeomorph.symm ''
    (Metric.closedBall X R ×ˢ Icc t (5 * t / 2))
  have hKcompact : IsCompact K := by
    exact ((isCompact_closedBall X R).prod isCompact_Icc).image
      parabolicHomeomorph.symm.continuous
  apply hKcompact.isBounded.subset
  intro z hz
  refine ⟨(z.1, z.2), ⟨?_, ?_⟩, ?_⟩
  · exact Metric.ball_subset_closedBall hz.1
  · exact ⟨hz.2.1.le, hz.2.2.le⟩
  · apply parabolicHomeomorph.injective
    rw [parabolicHomeomorph.apply_symm_apply]
    rfl

end ESS
