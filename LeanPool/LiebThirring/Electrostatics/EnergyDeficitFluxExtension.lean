/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitFluxField

/-!
# Compact smooth extension of the exterior cutoff field

A smooth inner cutoff eliminates the nucleus singularity inside the cell.
The resulting field is globally smooth and compactly supported; outside
radius `a/2` it agrees with the original outer-cutoff field.
-/

@[expose] public section

open Filter Set Metric
open scoped Topology ContDiff

namespace LiebThirring

/-- A smooth inner bump whose transition is confined inside radius `a/2`. -/
noncomputable def exteriorFluxInnerBump (c : Position) (a : ℝ) (ha : 0 < a) : ContDiffBump c :=
  ⟨a / 4, a / 2, by positivity, by linarith⟩

/-- Compact smooth extension of the outer-cutoff inverse-square field. -/
noncomputable def exteriorFluxExtendedField (c : Position) (a T : ℝ) (ha : 0 < a)
    (x : Position) : Position :=
  (exteriorFluxCutoff c T x * (1 - exteriorFluxInnerBump c a ha x)) •
    exteriorInverseSquareField c x

/-- The inverse-square field is smooth off its singular centre. -/
theorem contDiffAt_exteriorInverseSquareField (c x : Position) (hx : x ≠ c) :
    ContDiffAt ℝ ∞ (exteriorInverseSquareField c) x := by
  have hs : ContDiffAt ℝ ∞ (fun y : Position => ‖y - c‖ ^ 2) x :=
    ((contDiff_id : ContDiff ℝ ∞ (fun y : Position => y)).sub
      (contDiff_const : ContDiff ℝ ∞ (fun _ : Position => c))).norm_sq (𝕜 := ℝ) |>.contDiffAt
  have hn : ‖x - c‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))
  exact ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Position => (-2 : ℝ)) x).mul
    ((hs.inv hn).pow 2)).smul
    (((contDiff_id : ContDiff ℝ ∞ (fun y : Position => y)).sub
      (contDiff_const : ContDiff ℝ ∞ (fun _ : Position => c))).contDiffAt)

/-- Global smoothness of the extended field. -/
theorem contDiff_exteriorFluxExtendedField (c : Position) (a T : ℝ) (ha : 0 < a) :
    ContDiff ℝ ∞ (exteriorFluxExtendedField c a T ha) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = c
  · subst x
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Position => (0 : Position))
      c).congr_of_eventuallyEq
    filter_upwards [(exteriorFluxInnerBump c a ha).eventuallyEq_one] with x hx
    simp only [exteriorFluxExtendedField, hx, Pi.one_apply, sub_self, mul_zero, zero_smul]
  · exact ((contDiff_exteriorFluxCutoff c T).contDiffAt.mul
      (contDiffAt_const.sub (exteriorFluxInnerBump c a ha).contDiffAt)).smul
      (contDiffAt_exteriorInverseSquareField c x hx)

/-- The scaled cutoff is a standard compactly supported bump at positive scale. -/
theorem exteriorFluxCutoff_eq_bump (c : Position) (T : ℝ) (hT : 0 < T) :
    exteriorFluxCutoff c T = (⟨T, 2 * T, hT, by linarith⟩ : ContDiffBump c) := by
  funext x
  rw [exteriorFluxCutoff, exteriorFluxBump, ContDiffBump.apply, ContDiffBump.apply]
  simp only [inv_one, one_smul, sub_zero, div_one]
  rw [mul_div_cancel_right₀ _ (ne_of_gt hT)]

/-- Compact support of the expanding cutoff. -/
theorem hasCompactSupport_exteriorFluxCutoff (c : Position) (T : ℝ) (hT : 0 < T) :
    HasCompactSupport (exteriorFluxCutoff c T) := by
  rw [exteriorFluxCutoff_eq_bump c T hT]
  exact ContDiffBump.hasCompactSupport _

/-- Compact support of the extended smooth field. -/
theorem hasCompactSupport_exteriorFluxExtendedField (c : Position) (a T : ℝ)
    (ha : 0 < a) (hT : 0 < T) :
    HasCompactSupport (exteriorFluxExtendedField c a T ha) :=
  ((hasCompactSupport_exteriorFluxCutoff c T hT).mul_right).smul_right

/-- The inner extension equals the original field outside its transition ball. -/
theorem exteriorFluxExtendedField_eq (c x : Position) (a T : ℝ) (ha : 0 < a)
    (hx : a / 2 ≤ ‖x - c‖) :
    exteriorFluxExtendedField c a T ha x =
      exteriorFluxCutoff c T x • exteriorInverseSquareField c x := by
  have hb : exteriorFluxInnerBump c a ha x = 0 :=
    (exteriorFluxInnerBump c a ha).zero_of_le_dist (by simpa only [exteriorFluxInnerBump,
      dist_eq_norm] using hx)
  simp only [exteriorFluxExtendedField, hb, sub_zero, mul_one]

/-- The inner extension is locally invisible outside the transition ball. -/
theorem eventuallyEq_exteriorFluxExtendedField (c x : Position) (a T : ℝ) (ha : 0 < a)
    (hx : a / 2 < ‖x - c‖) :
    exteriorFluxExtendedField c a T ha =ᶠ[𝓝 x]
      (fun y => exteriorFluxCutoff c T y • exteriorInverseSquareField c y) := by
  have hn : ∀ᶠ y in 𝓝 x, a / 2 < ‖y - c‖ :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hx
  filter_upwards [hn] with y hy
  exact exteriorFluxExtendedField_eq c y a T ha hy.le

/-- Exact divergence of the globally smooth extension outside its transition ball. -/
theorem positionDivergence_exteriorFluxExtendedField (c x : Position) (a T : ℝ)
    (ha : 0 < a) (hx : a / 2 < ‖x - c‖) :
    positionDivergence (exteriorFluxExtendedField c a T ha) x =
      exteriorFluxCutoff c T x * (2 / ‖x - c‖ ^ 4) -
        exteriorFluxDefect (T⁻¹ • (x - c)) * (2 / ‖x - c‖ ^ 4) := by
  have he := (eventuallyEq_exteriorFluxExtendedField c x a T ha hx).fderiv_eq (𝕜 := ℝ)
  have hxc : x ≠ c := by
    intro h
    subst x
    simp only [sub_self, norm_zero] at hx
    linarith
  unfold positionDivergence
  rw [he]
  exact positionDivergence_cutoff_field c x T hxc

end LiebThirring

end
