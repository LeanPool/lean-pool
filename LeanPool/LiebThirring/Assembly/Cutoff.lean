/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import LeanPool.LiebThirring.Assembly.CutoffRadial
public import LeanPool.LiebThirring.Defs.Coulomb
import LeanPool.LiebThirring.Assembly.Coulomb

/-!
# The everywhere nearest-nucleus cutoff

The extended nearest-distance cutoff, infinite at nuclei when `a > 0`.

The nearest-distance cutoff is measurable.
-/

public section
open MeasureTheory Set
open scoped ENNReal
namespace LiebThirring.Assembly
/-- The extended nearest-distance cutoff, infinite at nuclei when `a > 0`. -/
@[expose] noncomputable def nearestNucleusCutoff {M : ℕ}
    (a r : ℝ) (R : Fin M → Position) (x : Position) : ℝ≥0∞ :=
  if nearestNucleusDistance R x < ENNReal.ofReal r then
    ENNReal.ofReal a * (nearestNucleusDistance R x)⁻¹ else 0

/-- The cutoff plus its constant tail controls the inverse nearest distance everywhere. -/
theorem nearestNucleusInverse_le_cutoff {M : ℕ} (a r : ℝ) (hr : 0 < r)
    (R : Fin M → Position) (x : Position) :
    ENNReal.ofReal a * (nearestNucleusDistance R x)⁻¹ ≤
      nearestNucleusCutoff a r R x + ENNReal.ofReal (a / r) := by
  unfold nearestNucleusCutoff
  split_ifs with h
  · exact le_add_right le_rfl
  · rw [zero_add, ENNReal.ofReal_div_of_pos hr, div_eq_mul_inv]
    exact mul_le_mul_right (ENNReal.inv_le_inv.mpr (le_of_not_gt h)) _

/-- A nearest-distance cutoff power is bounded pointwise by the sum of one-center powers. -/
theorem nearestNucleusCutoff_rpow_le_sum {M : ℕ} (a r : ℝ) (hr : 0 < r)
    (R : Fin M → Position) (x : Position) :
    nearestNucleusCutoff a r R x ^ ((5 : ℝ) / 2) ≤
      ∑ k : Fin M, nucleusCutoff a r (R k) x ^ ((5 : ℝ) / 2) := by
  classical
  cases M with
  | zero =>
    simp only [nearestNucleusCutoff, nearestNucleusDistance, iInf_of_empty,
      not_top_lt, ite_false, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 5 / 2),
      Finset.univ_eq_empty, Finset.sum_empty, le_refl]
  | succ M =>
    obtain ⟨k, hk⟩ := Finite.exists_min (fun k : Fin (M + 1) => ENNReal.ofReal ‖x - R k‖)
    have hd : nearestNucleusDistance R x = ENNReal.ofReal ‖x - R k‖ :=
      le_antisymm (iInf_le _ k) (le_iInf hk)
    unfold nearestNucleusCutoff
    split_ifs with h
    · have hkr : ‖x - R k‖ < r := by
        rw [hd] at h
        exact (ENNReal.ofReal_lt_ofReal_iff hr).mp h
      rw [hd]
      calc
        _ = nucleusCutoff a r (R k) x ^ ((5 : ℝ) / 2) := by
          rw [nucleusCutoff, ite_eq_left hkr]
        _ ≤ _ := Finset.single_le_sum
          (f := fun j : Fin (M + 1) => nucleusCutoff a r (R j) x ^ ((5 : ℝ) / 2))
          (fun j _ => bot_le) (Finset.mem_univ k)
    · rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 5 / 2)]
      exact bot_le

/-- The cutoff power integral of the nearest-nucleus cutoff, uniformly over all nuclear
configurations. -/
theorem lintegral_nearestNucleusCutoff_rpow_le {M : ℕ} (a r : ℝ) (ha : 0 ≤ a)
    (hr : 0 < r) (R : Fin M → Position) :
    ∫⁻ x : Position, nearestNucleusCutoff a r R x ^ ((5 : ℝ) / 2) ≤
      ENNReal.ofReal (8 * Real.pi * M * a ^ ((5 : ℝ) / 2) * Real.sqrt r) := by
  calc
    _ ≤ ∫⁻ x : Position, ∑ k : Fin M, nucleusCutoff a r (R k) x ^ ((5 : ℝ) / 2) :=
      lintegral_mono (nearestNucleusCutoff_rpow_le_sum a r hr R)
    _ = ∑ k : Fin M, ∫⁻ x : Position, nucleusCutoff a r (R k) x ^ ((5 : ℝ) / 2) := by
      apply lintegral_finsetSum
      intro k _
      exact (ENNReal.continuous_rpow_const).measurable.comp
        (measurable_nucleusCutoff a r (R k))
    _ = _ := by
      simp only [lintegral_nucleusCutoff_rpow a r ha hr, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg M)]
      congr 1
      ring

end LiebThirring.Assembly

end
