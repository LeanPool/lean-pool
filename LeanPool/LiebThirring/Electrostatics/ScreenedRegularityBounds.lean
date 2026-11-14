/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.ScreenedRegularityBasic
import LeanPool.LiebThirring.Electrostatics.ShellAssemblyGeometry

/-!
# Global bounds for the screened potential

An explicit finite bound valid throughout space, including at nuclei.

The nuclear configuration fits inside a ball of some nonnegative radius.
-/

public section

open scoped NNReal

namespace LiebThirring

theorem screenedPotentialReal_le_cell_bound {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (k : Fin M)
    {x : Position} (hx : x ∈ closedVoronoiCell R k) :
    screenedPotentialReal Z R x ≤
      ∑ p ∈ Finset.univ.erase k, 2 * (Z : ℝ) / ‖R p - R k‖ := by
  classical
  rw [screenedPotentialReal_eq_on_closedVoronoiCell Z R hR k hx]
  apply Finset.sum_le_sum
  intro p hp
  have hpk := (Finset.mem_erase.mp hp).1
  have hd : 0 < ‖R p - R k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hR.ne hpk))
  have hxpos : 0 < ‖x - R p‖ := norm_pos_iff.mpr
    (sub_ne_zero.mpr (ne_nucleus_of_mem_closedVoronoiCell R hR k p hpk hx))
  have hs := nuclear_separation_le_twice_dist R k p hx
  have hi : ‖x - R p‖⁻¹ ≤ 2 / ‖R p - R k‖ := by
    rw [← one_div, div_le_div_iff₀ hxpos hd]
    simpa only [one_mul] using hs
  calc
    _ ≤ (Z : ℝ) * (2 / ‖R p - R k‖) := mul_le_mul_of_nonneg_left hi Z.coe_nonneg
    _ = _ := by ring

/-- An explicit finite bound valid throughout space, including at nuclei. -/
theorem screenedPotentialReal_le_global_bound {M : ℕ} (hM : 1 ≤ M) (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (x : Position) :
    screenedPotentialReal Z R x ≤
      ∑ k : Fin M, ∑ p ∈ Finset.univ.erase k, 2 * (Z : ℝ) / ‖R p - R k‖ := by
  classical
  obtain ⟨k, hk⟩ := exists_nearest_nucleus hM R x
  have hx : x ∈ closedVoronoiCell R k := by
    intro p
    simpa only [dist_eq_norm] using hk p
  apply (screenedPotentialReal_le_cell_bound Z R hR k hx).trans
  apply Finset.single_le_sum _ (Finset.mem_univ k)
  intro l hl
  exact Finset.sum_nonneg (fun p hp => div_nonneg
    (mul_nonneg (by norm_num) Z.coe_nonneg) (norm_nonneg _))

theorem bounded_screenedPotentialReal {M : ℕ} (hM : 1 ≤ M) (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) :
    ∃ C : ℝ, ∀ x, |screenedPotentialReal Z R x| ≤ C := by
  classical
  refine ⟨∑ k : Fin M, ∑ p ∈ Finset.univ.erase k,
    2 * (Z : ℝ) / ‖R p - R k‖, fun x => ?_⟩
  rw [abs_of_nonneg (screenedPotentialReal_nonneg Z R x)]
  exact screenedPotentialReal_le_global_bound hM Z R hR x

/-- The nuclear configuration fits inside a ball of some nonnegative radius. -/
theorem exists_nuclear_radius {M : ℕ} (R : Fin M → Position) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k, ‖R k‖ ≤ A := by
  classical
  refine ⟨∑ k : Fin M, ‖R k‖, Finset.sum_nonneg (fun k _ => norm_nonneg _), ?_⟩
  intro k
  exact Finset.single_le_sum (fun l _ => norm_nonneg _) (Finset.mem_univ k)

/-- Outside twice a ball containing the nuclei, every denominator is large. -/
theorem half_norm_le_nuclear_distance {M : ℕ} (R : Fin M → Position)
    {A : ℝ} (hA : ∀ k, ‖R k‖ ≤ A) {x : Position} (hx : 2 * A ≤ ‖x‖)
    (k : Fin M) : ‖x‖ / 2 ≤ ‖x - R k‖ := by
  have ht := norm_le_norm_sub_add x (R k)
  linarith only [ht, hA k, hx]

/-- The explicit `O(1/|x|)` estimate of screened-potential regularity. -/
theorem screenedPotentialReal_le_decay {M : ℕ} (hM : 1 ≤ M) (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R)
    {A : ℝ} (hA : ∀ k, ‖R k‖ ≤ A) {x : Position}
    (hx : 2 * A ≤ ‖x‖) (hxpos : 0 < ‖x‖) :
    screenedPotentialReal Z R x ≤ 2 * (M - 1 : ℕ) * (Z : ℝ) / ‖x‖ := by
  classical
  obtain ⟨k, hk⟩ := exists_nearest_nucleus hM R x
  have hcell : x ∈ closedVoronoiCell R k := by
    intro p
    simpa only [dist_eq_norm] using hk p
  rw [screenedPotentialReal_eq_on_closedVoronoiCell Z R hR k hcell]
  have hterm (p : Fin M) : (Z : ℝ) * ‖x - R p‖⁻¹ ≤ (Z : ℝ) * (2 / ‖x‖) := by
    apply mul_le_mul_of_nonneg_left _ Z.coe_nonneg
    have hd := half_norm_le_nuclear_distance R hA hx p
    have hp : 0 < ‖x - R p‖ := lt_of_lt_of_le (half_pos hxpos) hd
    rw [← one_div, div_le_div_iff₀ hp hxpos]
    simp only [one_mul]
    linarith
  calc
    _ ≤ ∑ _p ∈ Finset.univ.erase k, (Z : ℝ) * (2 / ‖x‖) :=
      Finset.sum_le_sum (fun p _ => hterm p)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- A global version of the decay estimate, with denominator `1 + |x|`. -/
theorem exists_screenedPotentialReal_le_one_add_norm {M : ℕ} (hM : 1 ≤ M)
    (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |screenedPotentialReal Z R x| ≤ C / (1 + ‖x‖) := by
  obtain ⟨B, hB⟩ := bounded_screenedPotentialReal hM Z R hR
  have hBpos : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  obtain ⟨A, hA, hbound⟩ := exists_nuclear_radius R
  let D : ℝ := 2 * (M - 1 : ℕ) * (Z : ℝ)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) Z.coe_nonneg
  refine ⟨B * (2 * A + 2) + 2 * D,
    add_nonneg (mul_nonneg hBpos (by linarith)) (mul_nonneg (by norm_num) hD), ?_⟩
  intro x
  have hden : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
  rw [le_div_iff₀ hden]
  by_cases hx : ‖x‖ ≤ 2 * A + 1
  · have hb := mul_le_mul_of_nonneg_right (hB x) hden.le
    have ht := mul_le_mul_of_nonneg_left (show 1 + ‖x‖ ≤ 2 * A + 2 by linarith) hBpos
    exact (hb.trans ht).trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) hD))
  · have hxpos : 0 < ‖x‖ := by linarith
    have hfar : 2 * A ≤ ‖x‖ := by linarith
    have hd := screenedPotentialReal_le_decay hM Z R hR hbound hfar hxpos
    change screenedPotentialReal Z R x ≤ D / ‖x‖ at hd
    have hb : |screenedPotentialReal Z R x| * ‖x‖ ≤ D := by
      rw [abs_of_nonneg (screenedPotentialReal_nonneg Z R x)]
      exact (le_div_iff₀ hxpos).mp hd
    have ht : 1 + ‖x‖ ≤ 2 * ‖x‖ := by linarith
    have hm := mul_le_mul_of_nonneg_left ht (abs_nonneg (screenedPotentialReal Z R x))
    have hs : |screenedPotentialReal Z R x| * (1 + ‖x‖) ≤ 2 * D := by nlinarith
    exact hs.trans (le_add_of_nonneg_left (mul_nonneg hBpos (by linarith)))

end LiebThirring

end
