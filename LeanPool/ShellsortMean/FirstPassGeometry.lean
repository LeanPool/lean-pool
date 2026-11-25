/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.ChainCoordinates

/-! The chain geometry and coefficients governing first-pass displacement. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- The number of slots in the chain containing the tagged slot. -/
def tagChainLength {n : ℕ} (h : ℕ) (i : Fin n) : ℕ :=
  (chainPositions n h (i.val % h)).card

theorem tagChainLength_pos {n : ℕ} (h : ℕ) (i : Fin n) : 0 < tagChainLength h i := by
  apply Finset.card_pos.mpr
  exact ⟨i, by simp [chainPositions]⟩

theorem tagChainLength_le {n : ℕ} (h : ℕ) (i : Fin n) : tagChainLength h i ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n)

theorem tagChainLength_last {n : ℕ} (h : ℕ) (hh : 0 < h) (i : Fin n) :
    i.val % h + h * (tagChainLength h i - 1) + 1 ≤ n := by
  have hp := source_prefix_position_lt (Finset.univ : Finset (Fin n)) h (i.val % h)
    (tagChainLength h i - 1) hh (Nat.mod_lt _ hh)
    (by change tagChainLength h i - 1 < tagChainLength h i; have := tagChainLength_pos h i; omega)
  omega

theorem tagChainLength_next {n : ℕ} (h : ℕ) (hh : 0 < h) (i : Fin n) :
    n ≤ i.val % h + h * tagChainLength h i := by
  unfold tagChainLength
  rw [chainPositions_card, residuePrefixCount_formula h (i.val % h) n hh (Nat.mod_lt _ hh)]
  have hn := Nat.mod_add_div n h
  have hrem := Nat.mod_lt n hh
  split_ifs with hr
  · rw [Nat.mul_add, Nat.mul_one]
    omega
  · simp only [Nat.add_zero]
    omega

/-- Summing a three-valued coefficient over actual physical positions. -/
theorem tagged_chain_sum {n : ℕ} (h : ℕ) (i : Fin n) (v0 vc vo : ℝ) :
    (∑ a : Fin n, if a = i then v0 else if a.val % h = i.val % h then vc else vo) =
      v0 + ((tagChainLength h i : ℝ) - 1) * vc +
        ((n : ℝ) - (tagChainLength h i : ℝ)) * vo := by
  have he : ∀ a : Fin n,
      (if a = i then v0 else if a.val % h = i.val % h then vc else vo) =
      (if a.val % h = i.val % h then vc else vo) + (if a = i then v0 - vc else 0) := by
    intro a
    by_cases ha : a = i <;> simp [ha]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcount := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun a => a.val % h = i.val % h)
  have hcard : ((Finset.univ.filter (fun a : Fin n => a.val % h = i.val % h)).card : ℝ) =
      (tagChainLength h i : ℝ) := rfl
  have hnot : ((Finset.univ.filter (fun a : Fin n => ¬a.val % h = i.val % h)).card : ℝ) =
      (n : ℝ) - (tagChainLength h i : ℝ) := by
    have hc := congrArg (fun v : ℕ => (v : ℝ)) hcount
    simp only [Nat.cast_add, Finset.card_univ, Fintype.card_fin] at hc
    change (tagChainLength h i : ℝ) + _ = _ at hc
    linarith
  rw [hcard, hnot]
  ring

/-- The contribution of a lower-key indicator to first-pass displacement. -/
def firstPassCoefficient {n : ℕ} (h : ℕ) (i a : Fin n) : ℝ :=
  if a = i then 0 else if a.val % h = i.val % h then (h : ℝ) - 1 else - 1

theorem firstPassCoefficient_sum {n : ℕ} (h : ℕ) (i : Fin n) :
    (∑ a : Fin n, firstPassCoefficient h i a) =
      (h : ℝ) * (tagChainLength h i : ℝ) - h + 1 - n := by
  unfold firstPassCoefficient
  rw [tagged_chain_sum]
  ring

theorem firstPassCoefficient_sq_sum {n : ℕ} (h : ℕ) (i : Fin n) :
    (∑ a : Fin n, (firstPassCoefficient h i a) ^ 2) =
      ((tagChainLength h i : ℝ) - 1) * ((h : ℝ) - 1) ^ 2 +
        ((n : ℝ) - (tagChainLength h i : ℝ)) := by
  have he : ∀ a : Fin n, (firstPassCoefficient h i a) ^ 2 =
      if a = i then (0 : ℝ) else if a.val % h = i.val % h then ((h : ℝ) - 1) ^ 2 else 1 := by
    intro a
    unfold firstPassCoefficient
    split_ifs <;> norm_num
  simp_rw [he]
  rw [tagged_chain_sum]
  ring

theorem firstPassCoefficient_endpoint_bounds {n : ℕ} (h : ℕ) (hh : 0 < h) (i : Fin n) :
    -((h : ℝ) - 1) ≤ ((i.val % h : ℕ) : ℝ) + ∑ a : Fin n, firstPassCoefficient h i a ∧
    ((i.val % h : ℕ) : ℝ) + (∑ a : Fin n, firstPassCoefficient h i a) ≤ (h : ℝ) - 1 := by
  rw [firstPassCoefficient_sum]
  have hL : 1 ≤ tagChainLength h i := tagChainLength_pos h i
  have hl := congrArg (fun v : ℕ => (v : ℝ)) (Nat.sub_add_cancel hL)
  push_cast at hl
  have hlast : ((i.val % h : ℕ) : ℝ) + (h : ℝ) * (tagChainLength h i - 1 : ℕ) + 1 ≤ n := by
    exact_mod_cast tagChainLength_last h hh i
  have hnext : (n : ℝ) ≤ ((i.val % h : ℕ) : ℝ) + (h : ℝ) * tagChainLength h i := by
    exact_mod_cast tagChainLength_next h hh i
  have hhR : 1 ≤ (h : ℝ) := by exact_mod_cast hh
  constructor <;> nlinarith

theorem firstPassCoefficient_sq_sum_bound {n : ℕ} (h : ℕ) (hh : 0 < h) (i : Fin n) :
    (∑ a : Fin n, (firstPassCoefficient h i a) ^ 2) ≤ (n : ℝ) * h := by
  rw [firstPassCoefficient_sq_sum]
  have hL : 1 ≤ tagChainLength h i := tagChainLength_pos h i
  have hLR : 1 ≤ (tagChainLength h i : ℝ) := by exact_mod_cast hL
  have hhR : 1 ≤ (h : ℝ) := by exact_mod_cast hh
  have hmNat : h * (tagChainLength h i - 1) ≤ n - 1 := by
    have hp := tagChainLength_last h hh i
    omega
  have hn : 1 ≤ n := by have := i.isLt; omega
  have hm : (h : ℝ) * ((tagChainLength h i : ℝ) - 1) ≤ (n : ℝ) - 1 := by
    have hc : (h : ℝ) * ((tagChainLength h i - 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hmNat
    simpa only [Nat.cast_sub hL, Nat.cast_sub hn, Nat.cast_one] using hc
  have hb := mul_le_mul_of_nonneg_left hm (show 0 ≤ (h : ℝ) - 1 by linarith)
  have hp := mul_nonneg (show 0 ≤ (tagChainLength h i : ℝ) - 1 by linarith)
    (show 0 ≤ (h : ℝ) - 1 by linarith)
  nlinarith

end Shellsort
end
