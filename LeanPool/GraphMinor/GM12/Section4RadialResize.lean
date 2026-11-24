/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.PushOff

/-!
# A radial change of disc radius with bounded support

The disc motion in XII (4.3), claim (7), page 251, needs to shrink
and enlarge discs inside their collars. Apply the piecewise linear
tent map to the radius, keeping each ray fixed. Its inverse is the
tent map with the two radii exchanged. Outside the outer radius
both maps are the identity.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric

private theorem tentMap_pos {l w t r : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (_hwt : w < t) (hr : 0 < r) : 0 < tentMap 0 l w t r := by
  by_cases hrl : r ≤ l
  · rw [tentMap, tent_left hl hlt hr.le hrl]
    simp only [sub_zero]
    have heq : r + (w - l) * (r / l) = w * r / l := by field_simp; ring
    rw [heq]
    exact div_pos (mul_pos hw hr) hl
  · by_cases hrt : r ≤ t
    · rw [tentMap, tent_right hl hlt (le_of_not_ge hrl) hrt]
      have heq : r + (w - l) * ((t - r) / (t - l)) =
          w * ((t - r) / (t - l)) + t * ((r - l) / (t - l)) := by
        field_simp [sub_ne_zero.mpr hlt.ne']; ring
      rw [heq]
      have h1 := mul_nonneg hw.le (div_nonneg (sub_nonneg.mpr hrt) (sub_pos.mpr hlt).le)
      have h2 := mul_pos (hl.trans hlt) (div_pos (sub_pos.mpr (lt_of_not_ge hrl)) (sub_pos.mpr hlt))
      exact add_pos_of_nonneg_of_pos h1 h2
    · rw [tentMap, tent_high hl hlt (le_of_not_ge hrt), mul_zero, add_zero]
      exact hr

private noncomputable def radialFactor (l w t r : ℝ) : ℝ :=
  tentMap 0 l w t (max l r) / max l r

private theorem radialFactor_pos {l w t : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (hwt : w < t) (r : ℝ) : 0 < radialFactor l w t r :=
  div_pos (tentMap_pos hl hlt hw hwt (hl.trans_le (le_max_left _ _)))
    (hl.trans_le (le_max_left _ _))

private theorem radialFactor_mul {l w t r : ℝ} (hl : 0 < l) (hlt : l < t)
    (hr : 0 ≤ r) : radialFactor l w t r * r = tentMap 0 l w t r := by
  by_cases hrl : r ≤ l
  · simp only [radialFactor, max_eq_left hrl]
    rw [tentMap, tent_left hl hlt hl.le le_rfl]
    simp only [sub_zero, div_self hl.ne', mul_one]
    rw [tentMap, tent_left hl hlt hr hrl]
    simp only [sub_zero]
    field_simp
  · simp only [radialFactor, max_eq_right (le_of_not_ge hrl)]
    exact div_mul_cancel₀ _ (hl.trans (lt_of_not_ge hrl)).ne'

private theorem radialFactor_continuous {l w t : ℝ} (hl : 0 < l) (_hlt : l < t) :
    Continuous (radialFactor l w t) := by
  unfold radialFactor tentMap tent
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro r
    exact (hl.trans_le (le_max_left _ _)).ne'

private noncomputable def radialMap (l w t : ℝ) (z : ℂ) : ℂ :=
  radialFactor l w t ‖z‖ • z

private theorem radialMap_norm {l w t : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (hwt : w < t) (z : ℂ) :
    ‖radialMap l w t z‖ = tentMap 0 l w t ‖z‖ := by
  rw [radialMap, norm_smul, Real.norm_eq_abs,
    abs_of_pos (radialFactor_pos hl hlt hw hwt _)]
  exact radialFactor_mul hl hlt (norm_nonneg z)

private theorem radialMap_inverse {l w t : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (hwt : w < t) (z : ℂ) :
    radialMap w l t (radialMap l w t z) = z := by
  by_cases hz : z = 0
  · simp [hz, radialMap]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have heq : radialFactor w l t (tentMap 0 l w t ‖z‖) * radialFactor l w t ‖z‖ = 1 := by
    apply mul_right_cancel₀ hn.ne'
    rw [one_mul, mul_assoc, radialFactor_mul hl hlt hn.le,
      radialFactor_mul hw hwt (tentMap_pos hl hlt hw hwt hn).le,
      tentMap_inv hl hlt hw hwt]
  change radialFactor w l t ‖radialMap l w t z‖ • (radialFactor l w t ‖z‖ • z) = z
  rw [radialMap_norm hl hlt hw hwt, smul_smul, heq, one_smul]

/-- Change one positive disc radius to another, fixing all points
at or beyond a larger radius. -/
theorem exists_radial_disc_resize {l w t : ℝ} (hl : 0 < l) (hlt : l < t)
    (hw : 0 < w) (hwt : w < t) :
    ∃ Θ : ℂ ≃ₜ ℂ,
      (∀ z, t ≤ ‖z‖ → Θ z = z) ∧
      (∀ z, ‖Θ z‖ = tentMap 0 l w t ‖z‖) ∧
      Θ '' closedBall 0 l = closedBall 0 w := by
  let Θ : ℂ ≃ₜ ℂ := {
    toFun := radialMap l w t
    invFun := radialMap w l t
    left_inv := radialMap_inverse hl hlt hw hwt
    right_inv := radialMap_inverse hw hwt hl hlt
    continuous_toFun := (radialFactor_continuous hl hlt).comp continuous_norm |>.smul continuous_id
    continuous_invFun := (radialFactor_continuous hw hwt).comp continuous_norm |>.smul
      continuous_id }
  have hscale : ∀ z : ℂ, ‖z‖ ≤ l → Θ z = (w / l) • z := by
    intro z hz
    change radialFactor l w t ‖z‖ • z = _
    congr 1
    simp only [radialFactor, max_eq_left hz, tentMap, tent_left hl hlt hl.le le_rfl,
      sub_zero, div_self hl.ne', mul_one]
    congr 1
    ring
  refine ⟨Θ, ?_, radialMap_norm hl hlt hw hwt, ?_⟩
  · intro z hz
    change radialFactor l w t ‖z‖ • z = z
    have hn : l ≤ ‖z‖ := hlt.le.trans hz
    have hnpos : 0 < ‖z‖ := hl.trans_le hn
    simp only [radialFactor, max_eq_right hn, tentMap, tent_high hl hlt hz,
      mul_zero, add_zero, div_self hnpos.ne', one_smul]
  · apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [mem_closedBall_zero_iff] at hz ⊢
      rw [hscale z hz, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hw hl)]
      exact (mul_le_mul_of_nonneg_left hz (div_pos hw hl).le).trans_eq (div_mul_cancel₀ w hl.ne')
    · intro z hz
      rw [mem_closedBall_zero_iff] at hz
      let v : ℂ := (l / w) • z
      have hv : ‖v‖ ≤ l := by
        dsimp only [v]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hl hw)]
        exact (mul_le_mul_of_nonneg_left hz (div_pos hl hw).le).trans_eq (div_mul_cancel₀ l hw.ne')
      refine ⟨v, mem_closedBall_zero_iff.mpr hv, ?_⟩
      rw [hscale v hv]
      dsimp only [v]
      rw [smul_smul]
      have heq : w / l * (l / w) = 1 := by field_simp
      rw [heq, one_smul]

end GraphMinor.GM12
