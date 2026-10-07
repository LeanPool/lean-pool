/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCMoveCenter
public import LeanPool.EscauriazaSereginSverak.Linear.UCRestriction

/-!
# Weak solution data around an interior center

Every ball whose radius is the distance to the original boundary inherits
the weak derivative data and continuity from the original cylinder.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The maximal ball centered at an interior point remains inside the
original source ball. -/
theorem uc_center_ball_subset
    (R : ℝ) (x₀ : Vec3) :
    vec3Ball x₀ (R - vec3EuclideanNorm x₀) ⊆ vec3Ball 0 R := by
  intro y hy
  have htri := vec3EuclideanNorm_add_le (y - x₀) x₀
  have heq : y - x₀ + x₀ = y := by abel
  rw [heq] at htri
  have hy' : vec3EuclideanNorm (y - x₀) < R - vec3EuclideanNorm x₀ :=
    (mem_vec3Ball).mp hy
  apply (mem_vec3Ball).mpr
  simpa only [sub_zero] using (lt_of_le_of_lt htri (by
    linarith only [hy']))

/-- Continuity, weak derivatives, quadratic data, and the differential
inequality restrict to an interior centered cylinder. -/
theorem uc_data_at_center
    (R T c₁ : ℝ)
    (x₀ : Vec3)
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
          Real.sqrt (spatialGradientSq w Dw z))) :
    let R₀ := R - vec3EuclideanNorm x₀
    let T₀ := min T 1
    ContinuousOn w (vec3Ball x₀ R₀ ×ˢ Ico 0 T₀) ∧
      HasSpaceTimeWeakDerivs (vec3Ball x₀ R₀) (Ioo 0 T₀)
        w Dw D2w Dtw ∧
      (∫⁻ z in spaceTimeSet (vec3Ball x₀ R₀) (Ioo 0 T₀),
        ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
          ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
      (∀ᵐ z ∂(volume.restrict
        (spaceTimeSet (vec3Ball x₀ R₀) (Ioo 0 T₀))),
        vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
          c₁ * (vec3EuclideanNorm (w z) +
            Real.sqrt (spatialGradientSq w Dw z))) := by
  dsimp
  let R₀ : ℝ := R - vec3EuclideanNorm x₀
  let T₀ : ℝ := min T 1
  have hΩ : vec3Ball x₀ R₀ ⊆ vec3Ball 0 R :=
    uc_center_ball_subset R x₀
  have hI : Ioo 0 T₀ ⊆ Ioo 0 T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
  have hIco : Ico 0 T₀ ⊆ Ico 0 T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
  have hcontOpen : ContinuousOn w (vec3Ball 0 R ×ˢ Ioo 0 T) :=
    hcont.mono (fun _ hz => ⟨hz.1, ⟨hz.2.1.le, hz.2.2⟩⟩)
  obtain ⟨_, hweak₀, hL2₀, hineq₀⟩ :=
    uc_restrict_data c₁ (vec3Ball x₀ R₀) (vec3Ball 0 R)
      (Ioo 0 T₀) (Ioo 0 T) w Dw D2w Dtw
      (isOpen_vec3Ball _ _) isOpen_Ioo hΩ hI hcontOpen
      hweak hL2 hineq
  refine ⟨?_, hweak₀, hL2₀, hineq₀⟩
  exact hcont.mono (fun _ hz => ⟨hΩ hz.1, hIco hz.2⟩)

end ESS
