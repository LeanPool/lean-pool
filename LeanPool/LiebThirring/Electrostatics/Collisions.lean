/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.ShellAssembly

/-!
# Baxter's additive inequality at collisions and empty configurations

Meeting a nucleus makes the nearest-nucleus distance zero.

An electron-nucleus collision makes the control infinite, including at zero charge.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- Meeting a nucleus makes the nearest-nucleus distance zero. -/
theorem nearestNucleusDistance_eq_zero_of_eq {M : ℕ} (R : Fin M → Position)
    (a : Position) (k : Fin M) (ha : a = R k) :
    nearestNucleusDistance R a = 0 := by
  apply le_antisymm ?_ zero_le
  calc
    nearestNucleusDistance R a ≤ ENNReal.ofReal ‖a - R k‖ := iInf_le _ k
    _ = 0 := by rw [ha, sub_self, norm_zero, ENNReal.ofReal_zero]

/-- An electron-nucleus collision makes the control infinite, including at zero charge. -/
theorem nearestNucleusControl_eq_top_of_collision {N M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (x : Configuration N) (i : Fin N) (k : Fin M)
    (hx : particlePosition x i = R k) : nearestNucleusControl Z R x = ⊤ := by
  unfold nearestNucleusControl
  have hs : (∑ j : Fin N, (nearestNucleusDistance R (particlePosition x j))⁻¹) = ⊤ := by
    apply ENNReal.sum_eq_top.mpr
    exact ⟨i, Finset.mem_univ _, by rw [nearestNucleusDistance_eq_zero_of_eq R _ k hx,
      ENNReal.inv_zero]⟩
  rw [hs, ENNReal.mul_top]
  exact ne_of_gt (by positivity)

/-- A collision of two positive equally charged nuclei makes nuclear repulsion infinite. -/
theorem nuclearRepulsion_eq_top_of_collision {M : ℕ} (Z : ℝ≥0) (hZ : Z ≠ 0)
    (R : Fin M → Position) (k l : Fin M) (hkl : k < l) (hR : R k = R l) :
    nuclearRepulsion (fun _ => Z) R = ⊤ := by
  unfold nuclearRepulsion
  apply ENNReal.sum_eq_top.mpr
  refine ⟨k, Finset.mem_univ _, ENNReal.sum_eq_top.mpr ?_⟩
  refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkl⟩, ?_⟩
  rw [coulombKernel, hR, sub_self, norm_zero, ENNReal.ofReal_zero, ENNReal.inv_zero,
    ENNReal.mul_top]
  exact mul_ne_zero (ENNReal.coe_ne_zero.mpr hZ) (ENNReal.coe_ne_zero.mpr hZ)

/-- Zero charge annihilates attraction and correction even at collisions. -/
theorem baxter_zero_charge (N M : ℕ) (R : Fin M → Position) (x : Configuration N) :
    attraction (fun _ => (0 : ℝ≥0)) R x + baxterCorrection 0 R ≤
      electronRepulsion x + nuclearRepulsion (fun _ => 0) R + nearestNucleusControl 0 R x := by
  simp only [attraction, baxterCorrection, ENNReal.coe_zero, zero_mul,
    Finset.sum_const_zero, zero_pow (by norm_num : 2 ≠ 0), ENNReal.zero_div, zero_add]
  exact zero_le

/-- With no nuclei, attraction and correction are empty sums. -/
theorem baxter_no_nuclei (N : ℕ) (Z : ℝ≥0) (R : Fin 0 → Position)
    (x : Configuration N) :
    attraction (fun _ => Z) R x + baxterCorrection Z R ≤
      electronRepulsion x + nuclearRepulsion (fun _ => Z) R + nearestNucleusControl Z R x := by
  simp only [attraction, baxterCorrection, Finset.univ_eq_empty, Finset.sum_empty,
    Finset.sum_const_zero, mul_zero, zero_add]
  exact zero_le

/-- The exact Baxter conclusion from the basic electrostatic inequality, for every endpoint and
collision case. -/
theorem baxter_of_basicElectrostaticInequality
    (hB12 : ∀ (M : ℕ) (Z : ℝ≥0) (R : Fin M → Position), 1 ≤ M →
      Function.Injective R → BasicElectrostaticInequality Z R)
    (N M : ℕ) (Z : ℝ≥0) (R : Fin M → Position) (x : Configuration N) :
    attraction (fun _ => Z) R x + baxterCorrection Z R ≤
      electronRepulsion x + nuclearRepulsion (fun _ => Z) R +
        nearestNucleusControl Z R x := by
  classical
  by_cases hZ : Z = 0
  · subst Z
    exact baxter_zero_charge N M R x
  by_cases hM : M = 0
  · subst M
    exact baxter_no_nuclei N Z R x
  by_cases hR : Function.Injective R
  · by_cases hx : ∀ i k, particlePosition x i ≠ R k
    · exact baxter_of_basicElectrostaticInequality_of_separated Z R x
        (Nat.one_le_iff_ne_zero.mpr hM) (hB12 M Z R (Nat.one_le_iff_ne_zero.mpr hM) hR) hx
    · push Not at hx
      obtain ⟨i, k, hx⟩ := hx
      rw [nearestNucleusControl_eq_top_of_collision Z R x i k hx, add_top]
      exact le_top
  · obtain ⟨k, l, heq, hne⟩ := Function.not_injective_iff.mp hR
    rcases lt_or_gt_of_ne hne with hkl | hlk
    · rw [nuclearRepulsion_eq_top_of_collision Z hZ R k l hkl heq, add_top, top_add]
      exact le_top
    · rw [nuclearRepulsion_eq_top_of_collision Z hZ R l k hlk heq.symm, add_top, top_add]
      exact le_top

end LiebThirring

end
