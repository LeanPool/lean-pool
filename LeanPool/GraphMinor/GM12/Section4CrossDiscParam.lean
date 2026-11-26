/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SmallCrossDiscs

/-!
# Parametrizing the boundary of a crossing disc

In XII (4.5), claim (1), page 253, the boundary marks of each
crossing disc must be matched to the prescribed boundary marks.
Scale the unit circle by the radius and then apply the crossing
coordinates. This is a continuous injective parametrization of
the entire boundary, with no extra points.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Metric Surface

/-- The circle parametrization of a coordinate crossing disc. -/
noncomputable def crossDiscParam (A : ℂ ≃L[ℝ] ℂ) (x : ℂ) (r : ℝ) (w : Circle) : ℂ :=
  x + A (r • (w : ℂ))

/-- The scaled circle covers exactly the circle of positive radius. -/
theorem range_scaled_circle {r : ℝ} (hr : 0 < r) :
    range (fun w : Circle => r • (w : ℂ)) = sphere (0 : ℂ) r := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  · intro hz
    have hn : ‖r⁻¹ • z‖ = 1 := by
      rw [norm_smul, mem_sphere_zero_iff_norm.mp hz, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
      exact inv_mul_cancel₀ (ne_of_gt hr)
    refine ⟨⟨r⁻¹ • z, mem_sphere_zero_iff_norm.mpr hn⟩, ?_⟩
    change r • (r⁻¹ • z) = z
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]

/-- The coordinate circle parametrizes the entire boundary of
the crossing disc continuously and injectively. This supplies
boundary data for the disc matching in XII (4.5), page 253. -/
theorem crossDiscParam_properties (A : ℂ ≃L[ℝ] ℂ) (x : ℂ)
    {r : ℝ} (hr : 0 < r) :
    Continuous (crossDiscParam A x r) ∧ Function.Injective (crossDiscParam A x r) ∧
      range (crossDiscParam A x r) =
        discBd ((fun z => x + A z) '' closedBall 0 r) := by
  have hc : Continuous (crossDiscParam A x r) := by
    unfold crossDiscParam
    fun_prop
  have hinj : Function.Injective (crossDiscParam A x r) := by
    intro a b hab
    apply Subtype.ext
    have hsm : r • (a : ℂ) = r • (b : ℂ) := A.injective (add_left_cancel hab)
    exact (smul_right_injective _ (ne_of_gt hr)) hsm
  let h : ℂ ≃ₜ ℂ := A.toHomeomorph.trans (Homeomorph.addLeft x)
  have hD : IsClosedDisc (closedBall (0 : ℂ) r) ∧
      discBd (closedBall (0 : ℂ) r) = sphere 0 r := by
    have hi : interior (closedBall (0 : ℂ) r) = ball 0 r := interior_closedBall _ (ne_of_gt hr)
    obtain ⟨hd, hb⟩ := isClosedDisc_of_convex (convex_closedBall (0 : ℂ) r)
      (by rw [hi]; exact ⟨0, mem_ball_self hr⟩) isBounded_closedBall isClosed_closedBall
    exact ⟨hd, hb.trans (frontier_closedBall _ (ne_of_gt hr))⟩
  have hb := (hD.1.image h.continuous.continuousOn h.symm.continuous.continuousOn
    (fun z _ => h.symm_apply_apply z)).2
  rw [hD.2] at hb
  refine ⟨hc, hinj, ?_⟩
  change range (h ∘ (fun w : Circle => r • (w : ℂ))) = discBd (h '' closedBall 0 r)
  rw [range_comp, range_scaled_circle hr, hb]

end GraphMinor.GM12
