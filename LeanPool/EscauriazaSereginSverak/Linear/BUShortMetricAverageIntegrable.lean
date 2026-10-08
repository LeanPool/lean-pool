/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortMetricCylinderGeometry
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianData
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCaccioppoli
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortUCSpatialRestriction

/-!
# Integrability on the physical Gaussian cylinder

Weak derivatives and quadratic growth give finite velocity energy on
every bounded averaging cylinder inside the positive half-space.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The velocity square is integrable on the physical metric Gaussian
averaging cylinder (`lem:bu-small-time`). -/
theorem bu_short_metric_average_integrable
    (M : ℝ)
    (X : Vec3) (t : ℝ) (hX : 2 < X 2)
    (ht : 0 < t) (htsmall : t < 1 / 12)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
      (Ioo 0 1) w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2)) :
    IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (Metric.ball X (Real.sqrt (3 * t)))
        (Ioo t (5 * t / 2))) volume := by
  let B := Metric.ball X (Real.sqrt (3 * t))
  let I := Ioo t (5 * t / 2)
  let S := spaceTimeSet B I
  have hSsub : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo (0 : ℝ) 1) :=
    bu_short_metric_average_subset_half_cylinder X t hX ht htsmall
  have hSb : Bornology.IsBounded S :=
    bu_short_metric_average_bounded X t
  have hI : I ⊆ Ioo (0 : ℝ) 1 := by
    intro s hs
    have hz : (show ParabolicPoint from (X, s)) ∈ S := by
      exact ⟨Metric.mem_ball_self (by positivity), hs⟩
    exact (hSsub hz).2
  have hB : B ⊆ {x : Vec3 | 0 < x 2} := by
    intro y hy
    have hs : 3 * t / 2 ∈ I := by
      dsimp [I]
      constructor <;> nlinarith only [ht]
    have hz : (show ParabolicPoint from (y, 3 * t / 2)) ∈ S :=
      ⟨hy, hs⟩
    exact (hSsub hz).1
  have hweakTime := bu_weak_restrict_time hI w Dw D2w Dtw hweak
  have hweakS := bu_weak_restrict_space_interval measurableSet_Ioo hB
    w Dw D2w Dtw hweakTime
  have hFull := buGaussian_local_quadratic_l2 M w Dw D2w Dtw
    hweak hL2 hgrowth S hSsub hSb
  exact (buGaussian_local_energy_integrable hweakS hFull).1

end ESS
