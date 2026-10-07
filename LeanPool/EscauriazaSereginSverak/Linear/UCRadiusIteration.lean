/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCStepPropagation

/-!
# Radius iteration for unique continuation

Successive Gaussian steps cover the full source ball while preserving
integral flatness at each new center.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The Gaussian propagation step reaches every point of the original
spatial ball (`thm:uc`). -/
theorem uc_radius_iteration
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
    (hflat : UCIntegralFlatness 0 R (min T 1) w) :
    ∀ y ∈ vec3Ball 0 R, w (y, 0) = 0 := by
  have h0ball : (0 : Vec3) ∈ vec3Ball 0 R := by
    simpa only [mem_vec3Ball, sub_zero, vec3EuclideanNorm_zero] using hR
  have hzeroFlat : UCIntegralFlatness 0
      (R - vec3EuclideanNorm (0 : Vec3)) (min T 1) w := by
    simpa only [vec3EuclideanNorm_zero, sub_zero] using hflat
  have hbase := uc_one_center_propagation R T c₁ hT hc₁
    0 h0ball w Dw D2w Dtw hcont hweak hL2 hineq hzero hzeroFlat
  have hreach (n : ℕ) :
      ∀ y ∈ vec3Ball 0 (ucRadius R n),
        w (y, 0) = 0 ∧
        UCIntegralFlatness y (R - vec3EuclideanNorm y) (min T 1) w := by
    induction n with
    | zero =>
        intro y hy
        have hybase : y ∈ vec3Ball 0
            (ucRadiusFraction * (R - vec3EuclideanNorm (0 : Vec3))) := by
          simpa only [ucRadius_zero, vec3EuclideanNorm_zero, sub_zero]
            using hy
        obtain ⟨hyzero, hyflat⟩ := hbase y hybase
        have hrad : R - vec3EuclideanNorm y ≤ R := by
          have hnn := vec3EuclideanNorm_nonneg y
          linarith only [hnn]
        exact ⟨hyzero,
          uc_integral_flatness_mono y R (R - vec3EuclideanNorm y)
            (min T 1) (min T 1) hrad le_rfl w
            (by simpa only [vec3EuclideanNorm_zero, sub_zero] using hyflat)⟩
    | succ n ih =>
        intro y hy
        by_cases hinner : y ∈ vec3Ball 0 (ucRadius R n)
        · exact ih y hinner
        have hnorm : ucRadius R n ≤ vec3EuclideanNorm y := by
          have hnot := (mem_vec3Ball).not.mp hinner
          exact le_of_not_gt (by simpa only [sub_zero] using hnot)
        obtain ⟨x₀, hx₀inner, hx₀R, hyx₀⟩ :=
          uc_radius_step_center R hR n y hnorm
            (by simpa only [mem_vec3Ball, sub_zero] using hy)
        obtain ⟨hx₀zero, hx₀flat⟩ := ih x₀ hx₀inner
        have hstep := uc_one_center_propagation R T c₁ hT hc₁
          x₀ hx₀R w Dw D2w Dtw hcont hweak hL2 hineq
          hx₀zero hx₀flat y hyx₀
        obtain ⟨hyzero, hyflat⟩ := hstep
        have hnormx₀ : vec3EuclideanNorm x₀ < ucRadius R n := by
          simpa only [mem_vec3Ball, sub_zero] using hx₀inner
        have hrad : R - vec3EuclideanNorm y ≤
            R - vec3EuclideanNorm x₀ := by
          linarith only [hnorm, hnormx₀]
        exact ⟨hyzero,
          uc_integral_flatness_mono y
            (R - vec3EuclideanNorm x₀) (R - vec3EuclideanNorm y)
            (min T 1) (min T 1) hrad le_rfl w hyflat⟩
  intro y hy
  have hyd : vec3EuclideanNorm y < R := by
    simpa only [mem_vec3Ball, sub_zero] using hy
  obtain ⟨n, hn⟩ := ucRadius_eventually_covers R
    (vec3EuclideanNorm y) hR hyd
  exact (hreach n y (by simpa only [mem_vec3Ball, sub_zero] using hn)).1

end ESS
