/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortUCAffineL2
public import LeanPool.EscauriazaSereginSverak.Linear.UCRadiusIteration

/-!
# Propagation from a zero neighborhood

The origin is infinitely flat when the field vanishes on a one-sided
space-time neighborhood. Unique continuation then fills the spatial ball.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- A local zero region at the initial time propagates to the whole ball
under the weak heat inequality (`thm:uc`). -/
theorem bu_short_uc_propagate_local_zero
    (R T c₁ : ℝ) (hR : 0 < R) (hT : 0 < T) (hc₁ : 0 < c₁)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w (vec3Ball 0 R ×ˢ Ico 0 T))
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 R) (Ioo 0 T)
      w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball 0 R) (Ioo 0 T),
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 R) (Ioo 0 T))),
      vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
        c₁ * (vec3EuclideanNorm (w z) +
          Real.sqrt (spatialGradientSq w Dw z)))
    (hzero : w (0, 0) = 0)
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hlocal : ∀ z ∈ spaceTimeSet (vec3Ball 0 r₀) (Ioo 0 (r₀ ^ 2)),
      w z = 0) :
    ∀ y ∈ vec3Ball 0 R, w (y, 0) = 0 := by
  have hflat : UCIntegralFlatness 0 R (min T 1) w := by
    intro m
    refine ⟨1, r₀, by norm_num, hr₀, ?_⟩
    intro r hr hrbound
    have hrr₀ : r < r₀ :=
      hrbound.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hpow : r ^ 2 < r₀ ^ 2 :=
      (sq_lt_sq₀ hr.le hr₀.le).2 hrr₀
    let S := spaceTimeSet (vec3Ball 0 r) (Ioo 0 (r ^ 2))
    have hSmeas : MeasurableSet S := by
      change MeasurableSet (vec3Ball 0 r ×ˢ Ioo 0 (r ^ 2))
      exact (vec3Ball_measurable _ _).prod measurableSet_Ioo
    have hSsub : S ⊆ spaceTimeSet (vec3Ball 0 r₀)
        (Ioo 0 (r₀ ^ 2)) := by
      intro z hz
      exact ⟨(vec3Ball_mono hrr₀.le) hz.1,
        ⟨hz.2.1, hz.2.2.trans hpow⟩⟩
    have hzeroAE : (fun z => vec3EuclideanNorm (w z) ^ 2) =ᵐ[
        (volume : Measure ParabolicPoint).restrict S] 0 := by
      filter_upwards [ae_restrict_mem hSmeas] with z hz
      simp only [hlocal z (hSsub hz), vec3EuclideanNorm_zero,
        zero_pow (by norm_num : 2 ≠ 0), Pi.zero_apply]
    have hInt : (∫ z in S, vec3EuclideanNorm (w z) ^ 2) = 0 :=
      integral_eq_zero_of_ae hzeroAE
    rw [show (∫ z in S, vec3EuclideanNorm (w z) ^ 2) = 0 from hInt]
    exact mul_nonneg (by norm_num) (pow_nonneg hr.le _)
  exact uc_radius_iteration R T c₁ hR hT hc₁ w Dw D2w Dtw
    hcont hweak hL2 hineq hzero hflat

end ESS
