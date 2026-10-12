/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitGeometry
public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitHalfSpace

/-!
# Exterior half-space lower bound for the Baxter correction

Exact normalization of one half-space contribution.

Each exterior contributes the required nearest-other inverse distance.
-/

public section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- Exact normalization of one half-space contribution. -/
theorem inverse_fourth_halfSpace_coefficient (Z : ℝ≥0) (d : ℝ) (hd : 0 < d) :
    ENNReal.ofReal ((Z : ℝ) ^ 2 / (8 * Real.pi)) * ENNReal.ofReal (Real.pi / (d / 2)) =
      (Z : ℝ≥0∞) ^ 2 / 4 * (ENNReal.ofReal d)⁻¹ := by
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (Z : ℝ) ^ 2 / (8 * Real.pi)),
    ← ENNReal.ofReal_inv_of_pos hd]
  have hz : (Z : ℝ≥0∞) = ENNReal.ofReal (Z : ℝ) := ENNReal.coe_nnreal_eq Z
  rw [hz, ← ENNReal.ofReal_pow (NNReal.coe_nonneg Z) 2, ← ENNReal.ofReal_ofNat (n := 4),
    ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (Z : ℝ) ^ 2 / 4)]
  congr 1
  field_simp
  ring

/-- Each exterior contributes the required nearest-other inverse distance. -/
theorem baxterCorrection_summand_le_exterior_integral {M : ℕ}
    (hM : 2 ≤ M) (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (k : Fin M) :
    (Z : ℝ≥0∞) ^ 2 / 4 * (nearestOtherNucleusDistance R k)⁻¹ ≤
      ENNReal.ofReal ((Z : ℝ) ^ 2 / (8 * Real.pi)) *
        ∫⁻ x in (voronoiCell R k)ᶜ, ENNReal.ofReal ((‖x - R k‖ ^ 4)⁻¹) := by
  obtain ⟨l, hl, he, hsub⟩ := exists_nearest_exterior_halfSpace R hR hM k
  have hd : 0 < ‖R l - R k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hR.ne hl))
  have hsub' : {x : Position | ‖R l - R k‖ / 2 ≤ inner ℝ (bisectorNormal R k l) (x - R k)} ⊆
      (voronoiCell R k)ᶜ := by
    simpa only [he, ENNReal.toReal_ofReal (norm_nonneg _)] using hsub
  rw [he, ← inverse_fourth_halfSpace_coefficient Z _ hd]
  exact mul_le_mul_right
    (lintegral_inverse_fourth_halfSpace_le_of_subset (bisectorNormal R k l) (R k)
      (norm_bisectorNormal R hR hl.symm) (half_pos hd) _ hsub') _

/-- The entire nearest-nucleus correction is bounded by the exterior integral sum. -/
theorem baxterCorrection_le_exterior_integrals {M : ℕ}
    (hM : 2 ≤ M) (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R) :
    baxterCorrection Z R ≤ ENNReal.ofReal ((Z : ℝ) ^ 2 / (8 * Real.pi)) *
      ∑ k : Fin M, ∫⁻ x in (voronoiCell R k)ᶜ, ENNReal.ofReal ((‖x - R k‖ ^ 4)⁻¹) := by
  rw [baxterCorrection, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => baxterCorrection_summand_le_exterior_integral hM Z R hR k

end LiebThirring

end
