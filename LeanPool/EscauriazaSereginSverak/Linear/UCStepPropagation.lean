/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCenterRestriction
public import LeanPool.EscauriazaSereginSverak.Linear.UCInitialPropagation
public import LeanPool.EscauriazaSereginSverak.Linear.UCFlatnessTransfer

/-!
# One unique-continuation step

At an interior center with integral flatness and zero initial trace, the
Gaussian estimate propagates both properties through its output ball.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Integral flatness and the zero trace propagate through one Gaussian
spatial reach. -/
theorem uc_one_center_propagation
    (R T c₁ : ℝ) (hT : 0 < T) (hc₁ : 0 < c₁)
    (x₀ : Vec3) (hx₀ : x₀ ∈ vec3Ball 0 R)
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
    (hzero : w (x₀, 0) = 0)
    (hflat : UCIntegralFlatness x₀
      (R - vec3EuclideanNorm x₀) (min T 1) w) :
    ∀ y ∈ vec3Ball x₀
      (ucRadiusFraction * (R - vec3EuclideanNorm x₀)),
      w (y, 0) = 0 ∧
      UCIntegralFlatness y
        (R - vec3EuclideanNorm x₀) (min T 1) w := by
  let R₀ : ℝ := R - vec3EuclideanNorm x₀
  let T₀ : ℝ := min T 1
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    have hx := (mem_vec3Ball).mp hx₀
    simpa only [sub_zero] using sub_pos.mpr hx
  have hT₀ : 0 < T₀ := lt_min hT (by norm_num)
  have hT₀1 : T₀ ≤ 1 := min_le_right _ _
  obtain ⟨hcont₀, hweak₀, hL2₀, hineq₀⟩ :=
    uc_data_at_center R T c₁ x₀
      w Dw D2w Dtw hcont hweak hL2 hineq
  have hgauss := uc_gaussian_box_estimate R₀ T₀ c₁
    hR₀ hT₀ hT₀1 hc₁ x₀ w Dw D2w Dtw
    hcont₀ hweak₀ hL2₀ hineq₀ hflat
  have hL2w : (∫⁻ z in spaceTimeSet (vec3Ball x₀ R₀) (Ioo 0 T₀),
      ‖w z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    calc
      _ ≤ ∫⁻ z in spaceTimeSet (vec3Ball x₀ R₀) (Ioo 0 T₀),
        ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
          ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ) := by
            apply lintegral_mono
            intro z
            exact le_add_of_nonneg_right (by positivity) |>.trans
              (le_add_of_nonneg_right (by positivity) |>.trans
                (le_add_of_nonneg_right (by positivity)))
      _ < ⊤ := hL2₀
  have hInt : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (vec3Ball x₀ R₀) (Ioo 0 T₀)) volume :=
    uc_squared_norm_integrable_on_subset _ _ w hweak₀.1 hL2w Subset.rfl
  have htrace := uc_initial_ball_vanishing R₀ T₀ hR₀ hT₀
    x₀ w Dw D2w Dtw hcont₀ hweak₀ hL2₀ hzero hgauss
  intro y hy
  exact ⟨htrace y hy,
    uc_move_center_integral_flatness x₀ y R₀ T₀ hR₀ hT₀
      w Dw hInt hflat hgauss hy⟩

end ESS
