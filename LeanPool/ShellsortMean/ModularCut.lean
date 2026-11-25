/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.GapMonotone
public import Mathlib.Data.Nat.ModEq

/-! Threshold counts by residue for words made of gaps divisible by a common modulus. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- A sequence of passes with gaps divisible by d preserves the position
residue modulo d of each original key. -/
theorem sortWord_preserves_divisor_residue {n d : ℕ} (p : RankPlacement n)
    (gaps : List ℕ) (hd : ∀ h ∈ gaps, d ∣ h) (x : Fin n) :
    ((sortWord p gaps) x).val % d = (p x).val % d := by
  induction gaps generalizing p with
  | nil => rfl
  | cons h hs ih =>
    change ((sortWord (gapSort p h) hs) x).val % d = (p x).val % d
    rw [ih (gapSort p h) (fun k hk => hd k (by simp [hk]))]
    exact Nat.ModEq.of_dvd (hd h (by simp)) (gapSort_preserves_residue p h x)

/-- At the cut after a divisible-gap middle, every true threshold count in
every residue class equals its value just before the middle. -/
theorem sortWord_threshold_divisor_count {n d : ℕ} (p : RankPlacement n)
    (gaps : List ℕ) (hd : ∀ h ∈ gaps, d ∣ h) (t r : ℕ) :
    chainLowerCount (thresholdSet (sortWord p gaps) t) d r =
      chainLowerCount (thresholdSet p t) d r := by
  rw [threshold_chain_count_keys, threshold_chain_count_keys]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight
    (fun x => by rw [sortWord_preserves_divisor_residue p gaps hd x])

/-- Sorting the d-chains gives the same array on either side of this cut. -/
theorem gapSort_after_divisible_word {n d : ℕ} (p : RankPlacement n)
    (gaps : List ℕ) (hd : ∀ h ∈ gaps, d ∣ h) :
    gapSort (sortWord p gaps) d = gapSort p d := by
  apply gapSort_unique
  · intro x
    rw [gapSort_preserves_residue, sortWord_preserves_divisor_residue p gaps hd x]
  · intro x y hxy
    apply gapSort_sorted
    simpa only [gapSort_preserves_residue, sortWord_preserves_divisor_residue p gaps hd] using hxy

/-- The d-sorted input gives a lower bound on the actual footrule at the cut. -/
theorem divisible_word_footrule_lower {n d : ℕ} (p : RankPlacement n)
    (gaps : List ℕ) (hd : ∀ h ∈ gaps, d ∣ h) :
    footrule (gapSort p d) ≤ footrule (sortWord p gaps) := by
  rw [← gapSort_after_divisible_word p gaps hd]
  exact gapSort_footrule_le _ _

private def cutBit {n : ℕ} (x t : Fin n) : ℝ := if x ≤ t then 1 else 0

private theorem cutBit_sum_dist {n : ℕ} (x y : Fin n) :
    (∑ t : Fin n, |cutBit x t - cutBit y t|) = |(x.val : ℝ) - y.val| := by
  suffices mono : ∀ a b : Fin n, a ≤ b →
      (∑ t : Fin n, |cutBit a t - cutBit b t|) = |(a.val : ℝ) - b.val| by
    rcases le_total x y with h | h
    · exact mono x y h
    · simpa only [abs_sub_comm (cutBit y _) (cutBit x _), abs_sub_comm (y.val : ℝ) x.val]
        using mono y x h
  intro a b hab
  have bits (t : Fin n) : |cutBit a t - cutBit b t| =
      (if a ≤ t ∧ t < b then (1 : ℝ) else 0) := by
    by_cases hb : b ≤ t
    · simp [cutBit, hb, hab.trans hb, not_lt_of_ge hb]
    · by_cases ha : a ≤ t <;> simp [cutBit, ha, hb, lt_of_not_ge hb]
  simp_rw [bits]
  have seteq : Finset.univ.filter (fun t : Fin n => a ≤ t ∧ t < b) = Finset.Ico a b := by
    ext t; simp
  rw [Finset.sum_boole, seteq, Fin.card_Ico, Nat.cast_sub hab]
  have hval : (a.val : ℝ) ≤ b.val := by exact_mod_cast hab
  rw [abs_of_nonpos (sub_nonpos.mpr hval)]
  ring

private theorem modular_count_sum {n : ℕ} (p : RankPlacement n) (d r : ℕ) (t : Fin n) :
    (chainLowerCount (thresholdSet p (t.val + 1)) d r : ℝ) =
      ∑ i : Fin n, if i.val % d = r then cutBit (p.symm i) t else 0 := by
  unfold chainLowerCount thresholdSet
  simp only [Finset.filter_filter, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro i _
  have hlt : (p.symm i).val < t.val + 1 ↔ p.symm i ≤ t := Nat.lt_succ_iff
  by_cases hr : i.val % d = r <;> simp [cutBit, hr, hlt]

/-- The area of all classwise threshold discrepancies is bounded by the
physical footrule. The input and every finite positive modulus are arbitrary. -/
theorem sum_modular_threshold_discrepancies_le_footrule {n d : ℕ} (hd : 0 < d)
    (p : RankPlacement n) :
    (∑ t : Fin n, ∑ r ∈ Finset.range d,
      |(chainLowerCount (thresholdSet p (t.val + 1)) d r : ℝ) -
        chainLowerCount (thresholdSet (Equiv.refl (Fin n)) (t.val + 1)) d r|) ≤ footrule p := by
  simp only [modular_count_sum, Equiv.refl_symm, Equiv.refl_apply]
  rw [footrule_by_positions, ← Finset.sum_congr rfl
    (fun i _ => cutBit_sum_dist (p.symm i) i |>.trans (abs_sub_comm _ _))]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t _
  calc
    _ ≤ ∑ r ∈ Finset.range d, ∑ i : Fin n,
          if i.val % d = r then |cutBit (p.symm i) t - cutBit i t| else 0 := by
      apply Finset.sum_le_sum
      intro r _
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro i _
      by_cases hr : i.val % d = r <;> simp [hr]
    _ = _ := by
      rw [Finset.sum_comm]
      simp [Finset.mem_range, Nat.mod_lt _ hd]

end Shellsort
end
