/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.Basic
public import Mathlib.NumberTheory.ZetaValues

/-! # The inverse-square distance sum in the interpolation perturbation estimate -/

@[expose] public section

namespace NoncommutativeAMGM
open scoped BigOperators

/-- Basel's sum, counted on both sides of a fixed index in a finite interval. -/
theorem inverseSquare_gap_sum {m j : ℕ} (hj : j ≤ m) :
    (∑ l ∈ (Finset.range (m + 1)).erase j, 1 / ((j : ℝ) - l) ^ 2) ≤
      Real.pi ^ 2 / 3 := by
  classical
  let s := Finset.range (m + 1)
  let f := fun l : ℕ ↦ 1 / ((j : ℝ) - l) ^ 2
  have hleft : (∑ l ∈ s.filter (fun l ↦ l < j), f l) ≤ Real.pi ^ 2 / 6 := by
    let t := s.filter (fun l ↦ l < j)
    have hinj : Set.InjOn (fun l ↦ j - l) t := by
      intro a ha b hb he
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      dsimp only at he
      omega
    have he : (∑ k ∈ t.image (fun l ↦ j - l), 1 / (k : ℝ) ^ 2) = ∑ l ∈ t, f l := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Nat.cast_sub (Nat.le_of_lt (Finset.mem_filter.mp hl).2)]
    rw [← he]
    exact sum_le_hasSum _ (fun _ _ ↦ by positivity) hasSum_zeta_two
  have hright : (∑ l ∈ s.filter (fun l ↦ ¬l < j), f l) ≤ Real.pi ^ 2 / 6 := by
    let t := s.filter (fun l ↦ ¬l < j)
    have hinj : Set.InjOn (fun l ↦ l - j) t := by
      intro a ha b hb he
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      dsimp only at he
      omega
    have he : (∑ k ∈ t.image (fun l ↦ l - j), 1 / (k : ℝ) ^ 2) = ∑ l ∈ t, f l := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Nat.cast_sub (by have := (Finset.mem_filter.mp hl).2; omega)]
      dsimp [f]
      rw [show ((l : ℝ) - j) ^ 2 = ((j : ℝ) - l) ^ 2 by ring]
    rw [← he]
    exact sum_le_hasSum _ (fun _ _ ↦ by positivity) hasSum_zeta_two
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun l ↦ l < j) f
  have herase := Finset.sum_erase_add s f (by simp [s]; omega : j ∈ s)
  have hzero : f j = 0 := by simp [f]
  rw [hzero, add_zero] at herase
  change (∑ l ∈ s.erase j, f l) ≤ _
  linarith

/-- The inverse-square distance to the nearer endpoint sums to at most `π²/3`. -/
theorem inverseSquare_endpoint_sum (m : ℕ) :
    (∑ j ∈ Finset.Ioo 0 m, 1 / ((min j (m - j) : ℕ) : ℝ) ^ 2) ≤ Real.pi ^ 2 / 3 := by
  classical
  let s := Finset.Ioo 0 m
  have hleft : (∑ j ∈ s, 1 / (j : ℝ) ^ 2) ≤ Real.pi ^ 2 / 6 :=
    sum_le_hasSum _ (fun _ _ ↦ by positivity) hasSum_zeta_two
  have hright : (∑ j ∈ s, 1 / ((m - j : ℕ) : ℝ) ^ 2) ≤ Real.pi ^ 2 / 6 := by
    have hinj : Set.InjOn (fun j ↦ m - j) s := by
      intro a ha b hb he
      have ha' := (Finset.mem_Ioo.mp ha).2
      have hb' := (Finset.mem_Ioo.mp hb).2
      dsimp only at he
      omega
    rw [← Finset.sum_image (f := fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) hinj]
    exact sum_le_hasSum _ (fun _ _ ↦ by positivity) hasSum_zeta_two
  have hpoint (j : ℕ) :
      1 / ((min j (m - j) : ℕ) : ℝ) ^ 2 ≤
        1 / (j : ℝ) ^ 2 + 1 / ((m - j : ℕ) : ℝ) ^ 2 := by
    rcases le_total j (m - j) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (by positivity)
  have h := Finset.sum_le_sum (fun j (_ : j ∈ s) ↦ hpoint j)
  rw [Finset.sum_add_distrib] at h
  exact h.trans (by linarith)

end NoncommutativeAMGM
