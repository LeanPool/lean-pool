/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.Coulomb

/-!
# Reindexing nuclear repulsion

The symmetric off-diagonal sum counts each nuclear pair twice.

Deleting zero-charge nuclei and reindexing the remaining support preserve nuclear repulsion,
including singular configurations.
-/

public section

open scoped ENNReal NNReal

namespace LiebThirring.Assembly

private theorem sum_support {α : Type*} [Fintype α] (I : Set α) [Fintype I] (f : α → ℝ≥0∞)
    (hf : ∀ k, k ∉ I → f k = 0) :
    (∑ k, f k) = ∑ k : I, f k.val := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ I.toFinset)
    (fun k _ hk => hf k (by simpa only [Set.mem_toFinset] using hk))]
  exact (Finset.sum_subtype I.toFinset (fun _ => Set.mem_toFinset) f)

/-- The symmetric off-diagonal sum counts each nuclear pair twice. -/
theorem nuclearRepulsion_double_sum {M : ℕ} (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    (∑ k, ∑ l, if k ≠ l then
      ((z k : ℝ≥0∞) * (z l : ℝ≥0∞)) * coulombKernel (R k) (R l) else 0) =
      2 * nuclearRepulsion z R := by
  apply sum_ne_eq_two_sum_lt
  intro k l
  simp only [coulombKernel, norm_sub_rev (R k) (R l)]
  ac_rfl

/-- Deleting zero-charge nuclei and reindexing the remaining support preserve
nuclear repulsion, including singular configurations. -/
theorem nuclearRepulsion_reindex_support {M m : ℕ} (I : Set (Fin M)) (e : Fin m ≃ I)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (hz : ∀ k, k ∉ I → z k = 0) :
    nuclearRepulsion z R =
      nuclearRepulsion (fun j => z (e j).val) (fun j => R (e j).val) := by
  classical
  let : Fintype I := Fintype.ofEquiv (Fin m) e
  apply (ENNReal.mul_right_inj (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp
  rw [← nuclearRepulsion_double_sum, ← nuclearRepulsion_double_sum]
  let f (k l : Fin M) : ℝ≥0∞ := if k ≠ l then
      ((z k : ℝ≥0∞) * (z l : ℝ≥0∞)) * coulombKernel (R k) (R l) else 0
  have hfleft (k : Fin M) (hk : k ∉ I) (l : Fin M) : f k l = 0 := by
    simp only [f, hz k hk, ENNReal.coe_zero, zero_mul, ite_self]
  have hfright (l : Fin M) (hl : l ∉ I) (k : Fin M) : f k l = 0 := by
    simp only [f, hz l hl, ENNReal.coe_zero, mul_zero, zero_mul, ite_self]
  change (∑ k, ∑ l, f k l) = _
  rw [sum_support I (fun k => ∑ l, f k l) (fun k hk => by
    simp only [hfleft k hk, Finset.sum_const_zero])]
  simp_rw [sum_support I (f _) (fun l hl => hfright l hl _)]
  rw [← e.sum_comp]
  simp_rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  dsimp [f]
  have heq : (e k).val = (e l).val ↔ k = l := by
    rw [← Subtype.ext_iff, e.injective.eq_iff]
  simp only [heq]

end LiebThirring.Assembly

end
