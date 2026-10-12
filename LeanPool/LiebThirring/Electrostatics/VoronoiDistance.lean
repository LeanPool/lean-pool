/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.VoronoiBoundary
import Mathlib.Geometry.Euclidean.Triangle

/-!
# Nearest Voronoi face and boundary distance

Nearest-other nuclear distance determines the distance from a nucleus to its Voronoi boundary.
-/

public section

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

namespace LiebThirring

variable {M : ℕ}

theorem norm_bisectorNormal (R : Fin M → Position) (hR : Function.Injective R)
    {k l : Fin M} (hkl : k ≠ l) : ‖bisectorNormal R k l‖ = 1 := by
  have hp : 0 < ‖R l - R k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hR.ne hkl.symm))
  simp only [bisectorNormal, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hp, inv_mul_cancel₀ hp.ne']

theorem mem_voronoiCell_iff_normal (R : Fin M → Position)
    (hR : Function.Injective R) (k : Fin M) (x : Position) :
    x ∈ voronoiCell R k ↔ ∀ l, l ≠ k →
      inner ℝ (bisectorNormal R k l) (x - R k) < ‖R l - R k‖ / 2 := by
  rw [mem_voronoiCell_iff_inner]
  apply forall_congr'
  intro l
  apply imp_congr_right
  intro hl
  have hp : 0 < ‖R l - R k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hR.ne hl))
  simp only [bisectorNormal, real_inner_smul_left, ← div_eq_inv_mul]
  rw [div_lt_iff₀ hp]
  constructor <;> intro h <;> nlinarith only [h]

theorem mem_bisectorPlane_iff_normal (R : Fin M → Position)
    (hR : Function.Injective R) {k l : Fin M} (hkl : k ≠ l) (x : Position) :
    x ∈ bisectorPlane R k l ↔
      inner ℝ (bisectorNormal R k l) (x - R k) = ‖R l - R k‖ / 2 := by
  have hp : 0 < ‖R l - R k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hR.ne hkl.symm))
  rw [mem_bisectorPlane, le_antisymm_iff, dist_le_dist_iff_inner_le]
  have hexp := norm_sub_sq_real (x - R k) (R l - R k)
  rw [sub_sub_sub_cancel_right, real_inner_comm] at hexp
  simp only [bisectorNormal, real_inner_smul_left, ← div_eq_inv_mul]
  rw [div_eq_iff hp.ne']
  constructor
  · rintro ⟨h₁, h₂⟩
    have hsq := (sq_le_sq₀ (dist_nonneg : 0 ≤ dist x (R l))
      (dist_nonneg : 0 ≤ dist x (R k))).2 h₂
    simp only [dist_eq_norm] at hsq
    nlinarith only [hexp, h₁, hsq]
  · intro he
    constructor
    · nlinarith only [he]
    · apply (sq_le_sq₀ (dist_nonneg : 0 ≤ dist x (R l))
        (dist_nonneg : 0 ≤ dist x (R k))).1
      simp only [dist_eq_norm]
      nlinarith only [hexp, he]

/-- The direction `n_kl` points from `C_k` into its excluded half-space. -/
theorem exterior_halfSpace_subset_compl_voronoiCell
    (R : Fin M → Position) (hR : Function.Injective R)
    {k l : Fin M} (hkl : k ≠ l) :
    {x | ‖R l - R k‖ / 2 ≤ inner ℝ (bisectorNormal R k l) (x - R k)} ⊆
      (voronoiCell R k)ᶜ := by
  intro x hx hc
  exact ((mem_voronoiCell_iff_normal R hR k x).mp hc l hkl.symm).not_ge hx

/-- Any radius below all half inter-nuclear distances gives a ball in the cell. -/
theorem ball_subset_voronoiCell_of_bound (R : Fin M → Position) (k : Fin M)
    (r : ℝ) (hr : ∀ l, l ≠ k → 2 * r ≤ dist (R k) (R l)) :
    ball (R k) r ⊆ voronoiCell R k := by
  intro x hx l hl
  have ht := dist_triangle (R k) x (R l)
  have hx' : dist x (R k) < r := hx
  rw [dist_comm (R k) x] at ht
  linarith only [ht, hr l hl, hx']

end LiebThirring

end
