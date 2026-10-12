/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.Screened
public import LeanPool.LiebThirring.Electrostatics.NewtonConsequences
import all LeanPool.LiebThirring.Electrostatics.Screened
import all LeanPool.LiebThirring.Electrostatics.Basic
import LeanPool.LiebThirring.Electrostatics.Gaussian

/-!
# Geometry and attraction of electron shells

A finite nonempty nuclear configuration has a nearest index.

Identify the nearest distance without a Voronoi tie-breaking choice.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- A finite nonempty nuclear configuration has a nearest index. -/
theorem exists_nearest_nucleus {M : ℕ} (hM : 1 ≤ M)
    (R : Fin M → Position) (a : Position) :
    ∃ k : Fin M, ∀ l, ‖a - R k‖ ≤ ‖a - R l‖ := by
  classical
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ
    (fun k : Fin M => ‖a - R k‖) Finset.univ_nonempty
  exact ⟨k, fun l => hk l (Finset.mem_univ l)⟩

/-- Identify the nearest distance without a Voronoi tie-breaking choice. -/
theorem nearestNucleusDistance_eq_of_min {M : ℕ} (R : Fin M → Position)
    (a : Position) (k : Fin M) (hk : ∀ l, ‖a - R k‖ ≤ ‖a - R l‖) :
    nearestNucleusDistance R a = ENNReal.ofReal ‖a - R k‖ := by
  apply le_antisymm (iInf_le _ k)
  exact le_iInf (fun l => ENNReal.ofReal_le_ofReal (hk l))

/-- Removing a nearest nucleus minimizes the remaining nuclear potential. -/
theorem screenedPotential_eq_of_min {M : ℕ} (Z : ℝ≥0) (R : Fin M → Position)
    (a : Position) (k : Fin M) (hk : ∀ l, ‖a - R k‖ ≤ ‖a - R l‖) :
    screenedPotential Z R a =
      ∑ l ∈ Finset.univ.erase k, (Z : ℝ≥0∞) * coulombKernel a (R l) := by
  classical
  apply le_antisymm (iInf_le _ k)
  apply le_iInf
  intro l
  by_cases hkl : k = l
  · exact hkl ▸ le_rfl
  · have hker : (Z : ℝ≥0∞) * coulombKernel a (R l) ≤
        (Z : ℝ≥0∞) * coulombKernel a (R k) :=
      mul_le_mul_right (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (hk l))) _
    have hkm : k ∈ Finset.univ.erase l := Finset.mem_erase.mpr ⟨hkl, Finset.mem_univ _⟩
    have hlm : l ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨Ne.symm hkl, Finset.mem_univ _⟩
    rw [← Finset.sum_erase_add _ _ hlm, ← Finset.sum_erase_add _ _ hkm]
    rw [Finset.erase_right_comm]
    exact add_le_add_right hker _

/-- The nuclear potential splits into its screened part and nearest singularity. -/
theorem nuclearPotential_eq_screened_add {M : ℕ} (hM : 1 ≤ M)
    (Z : ℝ≥0) (R : Fin M → Position) (a : Position) :
    (∑ k : Fin M, (Z : ℝ≥0∞) * coulombKernel a (R k)) =
      screenedPotential Z R a + (Z : ℝ≥0∞) * (nearestNucleusDistance R a)⁻¹ := by
  classical
  obtain ⟨k, hk⟩ := exists_nearest_nucleus hM R a
  rw [screenedPotential_eq_of_min Z R a k hk, nearestNucleusDistance_eq_of_min R a k hk]
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ k)).symm

/-- On a half-nearest-distance sphere every nuclear distance is at least the radius. -/
theorem shell_nuclear_distance_bound {M : ℕ} (R : Fin M → Position)
    (a y : Position) (d : ℝ) (hd : ∀ k, d ≤ ‖a - R k‖)
    (hy : ‖y - a‖ = d / 2) :
    ENNReal.ofReal (d / 2) ≤ nearestNucleusDistance R y := by
  apply le_iInf
  intro k
  apply ENNReal.ofReal_le_ofReal
  have ht := norm_sub_le_norm_sub_add_norm_sub a y (R k)
  rw [norm_sub_rev a y, hy] at ht
  linarith only [hd k, ht]

/-- Newton gives exact attraction to each nucleus from an electron shell. -/
theorem lintegral_shell_nuclearPotential {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (a : Position) {d : ℝ} (hd : 0 < d)
    (hbound : ∀ k, d ≤ ‖a - R k‖) :
    (∫⁻ y, ∑ k : Fin M, (Z : ℝ≥0∞) * coulombKernel y (R k) ∂shell a (d / 2)) =
      ∑ k : Fin M, (Z : ℝ≥0∞) * coulombKernel a (R k) := by
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [lintegral_const_mul]
    · simp_rw [coulombKernel_symm _ (R k)]
      change (Z : ℝ≥0∞) * coulombPotential (shell a (d / 2)) (R k) = _
      rw [coulombPotential_shell_of_radius_le a (half_pos hd) (R k), coulombKernel_symm]
      rw [norm_sub_rev]
      exact (half_le_self hd.le).trans (hbound k)
    · exact measurable_coulombKernel.of_uncurry_right
  · intro k _
    exact measurable_const.mul measurable_coulombKernel.of_uncurry_right

/-- The shell contribution of the nearest singularity is at most `2Z/d`. -/
theorem lintegral_shell_nearest_le {M : ℕ} (Z : ℝ≥0) (R : Fin M → Position)
    (a : Position) {d : ℝ} (hd : 0 < d) (hbound : ∀ k, d ≤ ‖a - R k‖) :
    (∫⁻ y, (Z : ℝ≥0∞) * (nearestNucleusDistance R y)⁻¹ ∂shell a (d / 2)) ≤
      (Z : ℝ≥0∞) * (ENNReal.ofReal (d / 2))⁻¹ := by
  calc
    _ ≤ ∫⁻ _y, (Z : ℝ≥0∞) * (ENNReal.ofReal (d / 2))⁻¹ ∂shell a (d / 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_shell_norm a (half_pos hd).le] with y hy
      exact mul_le_mul_right (ENNReal.inv_le_inv.mpr
        (shell_nuclear_distance_bound R a y d hbound hy)) _
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- Measurability of the nearest-nucleus distance, including the empty infimum. -/
theorem measurable_nearestNucleusDistance {M : ℕ} (R : Fin M → Position) :
    Measurable (nearestNucleusDistance R) := by
  exact Measurable.iInf (fun k =>
    ((measurable_id.sub measurable_const).norm.ennreal_ofReal))

/-- Additive attraction estimate on one shell; its screened integral is kept intact. -/
theorem nuclearPotential_le_shell_screened_add {M : ℕ} (hM : 1 ≤ M)
    (Z : ℝ≥0) (R : Fin M → Position) (a : Position) {d : ℝ} (hd : 0 < d)
    (hbound : ∀ k, d ≤ ‖a - R k‖) :
    (∑ k : Fin M, (Z : ℝ≥0∞) * coulombKernel a (R k)) ≤
      (∫⁻ y, screenedPotential Z R y ∂shell a (d / 2)) +
        (Z : ℝ≥0∞) * (ENNReal.ofReal (d / 2))⁻¹ := by
  rw [← lintegral_shell_nuclearPotential Z R a hd hbound]
  simp_rw [nuclearPotential_eq_screened_add hM Z R]
  have hm : Measurable (fun y : Position => (Z : ℝ≥0∞) * (nearestNucleusDistance R y)⁻¹) :=
    measurable_const.mul (measurable_nearestNucleusDistance R).inv
  rw [lintegral_add_right _ hm]
  exact add_le_add_right (lintegral_shell_nearest_le Z R a hd hbound) _

end LiebThirring

end
