/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPhysicalCylinder

/-!
# Passing from metric to Euclidean averaging balls

The Euclidean ball is contained in the ambient metric ball used by the
Gaussian average estimate, so its nonnegative velocity integral obeys
the same bound.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A Gaussian bound over the ambient metric ball also bounds the
Euclidean averaging cylinder (`lem:bu-small-time`). -/
theorem bu_short_euclidean_average_le_metric
    (X : Vec3) (t : ℝ) (ht : 0 < t)
    (w : ParabolicPoint → Vec3)
    (hMetricInt : IntegrableOn
      (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (Metric.ball X (Real.sqrt (3 * t)))
        (Ioo t (5 * t / 2))) volume) :
    Real.rpow t (-(5 / 2 : ℝ)) *
      (∫ z in spaceTimeSet (vec3Ball X (Real.sqrt (3 * t)))
        (Ioo t (5 * t / 2)),
        vec3EuclideanNorm (w z) ^ 2
          ∂(volume : Measure ParabolicPoint)) ≤
    Real.rpow t (-(5 / 2 : ℝ)) *
      (∫ z in spaceTimeSet (Metric.ball X (Real.sqrt (3 * t)))
        (Ioo t (5 * t / 2)),
        vec3EuclideanNorm (w z) ^ 2
          ∂(volume : Measure ParabolicPoint)) := by
  have hSub : spaceTimeSet (vec3Ball X (Real.sqrt (3 * t)))
      (Ioo t (5 * t / 2)) ⊆
      spaceTimeSet (Metric.ball X (Real.sqrt (3 * t)))
        (Ioo t (5 * t / 2)) := by
    intro z hz
    exact ⟨CKN.vec3Ball_subset_ball X _ hz.1, hz.2⟩
  have hLe := setIntegral_mono_set hMetricInt
    (Filter.Eventually.of_forall (fun z => sq_nonneg _))
    (ae_of_all _ hSub)
  exact mul_le_mul_of_nonneg_left hLe
    (Real.rpow_pos_of_pos ht _).le

end ESS
