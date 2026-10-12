/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.FaceMeasure
public import LeanPool.LiebThirring.Electrostatics.Screened
import LeanPool.LiebThirring.Electrostatics.Gaussian
import LeanPool.LiebThirring.Electrostatics.ShellAssemblyGeometry
import all LeanPool.LiebThirring.Electrostatics.Basic
import all LeanPool.LiebThirring.Electrostatics.Screened

/-!
# Exact energy bookkeeping conditional on the potential identity

An off-diagonal symmetric finite sum counts its upper triangle twice.

At a nucleus the screened potential omits that nucleus.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LiebThirring

/-- An off-diagonal symmetric finite sum counts its upper triangle twice. -/
theorem sum_erase_eq_two_sum_upper {M : ℕ} (f : Fin M → Fin M → ℝ≥0∞)
    (hf : ∀ k l, f k l = f l k) :
    (∑ k : Fin M, ∑ l ∈ Finset.univ.erase k, f k l) =
      2 * ∑ k : Fin M, ∑ l ∈ Finset.univ.filter (fun l => k < l), f k l := by
  classical
  have hs (k l : Fin M) : (if l ≠ k then f k l else 0) =
      (if k < l then f k l else 0) + (if l < k then f l k else 0) := by
    rcases lt_trichotomy k l with h | h | h
    · rw [ite_eq_left (ne_of_gt h)]
      simp only [h, not_lt_of_ge h.le, ↓reduceIte, add_zero]
    · subst l
      simp only [ne_eq, not_true_eq_false, lt_self_iff_false, ↓reduceIte, add_zero]
    · rw [ite_eq_left (ne_of_lt h)]
      simp only [h, not_lt_of_ge h.le, ↓reduceIte, zero_add, hf k l]
  simp_rw [← Finset.filter_ne', Finset.sum_filter, hs, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun k l => if l < k then f l k else 0), two_mul]

/-- At a nucleus the screened potential omits that nucleus. -/
theorem screenedPotential_at_nucleus_eq_sum {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (k : Fin M) :
    screenedPotential Z R (R k) =
      ∑ l ∈ Finset.univ.erase k, (Z : ℝ≥0∞) * coulombKernel (R k) (R l) := by
  apply screenedPotential_eq_of_min
  intro l
  simp only [sub_self, norm_zero, norm_nonneg]

/-- Testing the face charge against one nuclear kernel uses exactly the potential identity. -/
theorem lintegral_nuclear_attraction_of_potential_eq {M : ℕ}
    (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (hPhi : ∀ x, screenedPotential Z R x =
      coulombPotential (voronoiFaceMeasure R hR (Z : ℝ)) x) (k : Fin M) :
    (∫⁻ y, (Z : ℝ≥0∞) * coulombKernel y (R k)
      ∂voronoiFaceMeasure R hR (Z : ℝ)) =
      ∑ l ∈ Finset.univ.erase k, (Z : ℝ≥0∞) ^ 2 * coulombKernel (R k) (R l) := by
  rw [lintegral_const_mul _ measurable_coulombKernel.of_uncurry_right]
  simp_rw [coulombKernel_symm _ (R k)]
  change (Z : ℝ≥0∞) * coulombPotential (voronoiFaceMeasure R hR (Z : ℝ)) (R k) = _
  rw [← hPhi, screenedPotential_at_nucleus_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [pow_two, mul_assoc]

/-- Additive exact deficit identity, avoiding subtraction of extended quantities. -/
theorem energy_add_nearestIntegral_eq_two_repulsion_of_potential_eq {M : ℕ}
    (hM : 1 ≤ M) (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (hPhi : ∀ x, screenedPotential Z R x =
      coulombPotential (voronoiFaceMeasure R hR (Z : ℝ)) x) :
    coulombEnergy (voronoiFaceMeasure R hR (Z : ℝ)) (voronoiFaceMeasure R hR (Z : ℝ)) +
      (∫⁻ y, (Z : ℝ≥0∞) * (nearestNucleusDistance R y)⁻¹
        ∂voronoiFaceMeasure R hR (Z : ℝ)) =
      2 * nuclearRepulsion (fun _ => Z) R := by
  have hm : Measurable (fun y : Position => (Z : ℝ≥0∞) * (nearestNucleusDistance R y)⁻¹) :=
    measurable_const.mul (measurable_nearestNucleusDistance R).inv
  have hsum : (∫⁻ y, ∑ k : Fin M, (Z : ℝ≥0∞) * coulombKernel y (R k)
      ∂voronoiFaceMeasure R hR (Z : ℝ)) = 2 * nuclearRepulsion (fun _ => Z) R := by
    rw [lintegral_finsetSum]
    · simp_rw [lintegral_nuclear_attraction_of_potential_eq Z R hR hPhi]
      rw [sum_erase_eq_two_sum_upper]
      · simp only [nuclearRepulsion, pow_two]
      · intro k l
        rw [coulombKernel_symm]
    · intro k _
      exact measurable_const.mul measurable_coulombKernel.of_uncurry_right
  simp_rw [nuclearPotential_eq_screened_add hM Z R] at hsum
  rw [lintegral_add_right _ hm] at hsum
  simp_rw [hPhi] at hsum
  exact hsum

/-- The normalized first equality in the energy deficit, with its the potential identity premise
explicit. -/
theorem half_energy_add_half_nearestIntegral_eq_repulsion_of_potential_eq {M : ℕ}
    (hM : 1 ≤ M) (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (hPhi : ∀ x, screenedPotential Z R x =
      coulombPotential (voronoiFaceMeasure R hR (Z : ℝ)) x) :
    coulombEnergy (voronoiFaceMeasure R hR (Z : ℝ)) (voronoiFaceMeasure R hR (Z : ℝ)) / 2 +
      (∫⁻ y, (Z : ℝ≥0∞) * (nearestNucleusDistance R y)⁻¹
        ∂voronoiFaceMeasure R hR (Z : ℝ)) / 2 =
      nuclearRepulsion (fun _ => Z) R := by
  rw [← ENNReal.add_div, energy_add_nearestIntegral_eq_two_repulsion_of_potential_eq hM Z R hR hPhi]
  rw [mul_comm (2 : ℝ≥0∞), ENNReal.mul_div_cancel_right] <;> norm_num

end LiebThirring

end
