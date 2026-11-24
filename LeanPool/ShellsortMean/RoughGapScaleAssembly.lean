/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Mathlib.Analysis.Real.Sqrt
public import LeanPool.ShellsortMean.PermutationGeometry
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! A finite threshold identity for actual rank placements, and conditional
assembly of real-valued expected costs across a finite dyadic schedule. -/

@[expose] public section

namespace Shellsort.RoughGapScaleAssembly

open Finset

/-- Cut just after rank t. The contribution from the cut coordinate cancels
because the two low-key sets always have the same size. -/
def thresholdMoment {n : ℕ} (p : RankPlacement n) (t : ℕ) : ℤ :=
  ∑ x : Fin n, ((p x).val : ℤ) *
    ((if x.val ≤ t then 1 else 0) - (if (p x).val ≤ t then 1 else 0))

/-- Unnormalized sum of squared distances between current and sorted slots. -/
def squareDisplacement {n : ℕ} (p : RankPlacement n) : ℤ :=
  ∑ x : Fin n, (((p x).val : ℤ) - (x.val : ℤ)) ^ 2

private theorem countCuts (x n : ℕ) :
    (∑ t ∈ range n, if x ≤ t then (1 : ℤ) else 0) = ((n - x : ℕ) : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega

/-- The exact identity 2 ∑ V_T = ∑ (position − rank)² for any permutation. -/
theorem twice_sum_thresholdMoment {n : ℕ} (p : RankPlacement n) :
    2 * (∑ t ∈ range n, thresholdMoment p t) = squareDisplacement p := by
  classical
  have slot (x : Fin n) :
      (∑ t ∈ range n, ((p x).val : ℤ) *
        ((if x.val ≤ t then 1 else 0) - (if (p x).val ≤ t then 1 else 0))) =
        ((p x).val : ℤ) * (((p x).val : ℤ) - (x.val : ℤ)) := by
    rw [← mul_sum, sum_sub_distrib, countCuts, countCuts]
    rw [Int.ofNat_sub (Nat.le_of_lt x.isLt), Int.ofNat_sub (Nat.le_of_lt (p x).isLt)]
    ring
  have squared := Equiv.sum_comp p (fun x : Fin n => (x.val : ℤ) ^ 2)
  have correction :
      (∑ x : Fin n, (((p x).val : ℤ) ^ 2 - (x.val : ℤ) ^ 2)) = 0 := by
    rw [sum_sub_distrib, sub_eq_zero]
    exact squared
  unfold thresholdMoment squareDisplacement
  rw [sum_comm]
  simp_rw [slot]
  rw [mul_sum]
  calc
    _ = ∑ x : Fin n, ((((p x).val : ℤ) - (x.val : ℤ)) ^ 2 +
        (((p x).val : ℤ) ^ 2 - (x.val : ℤ) ^ 2)) := by
          apply sum_congr rfl
          intro x _
          ring
    _ = _ := by rw [sum_add_distrib, correction, add_zero]

/-- Once each conditional scale contracts q with an additive H√q term,
q remains at most B²H² until the last checkpoint. -/
theorem dyadic_square_bound (levels : ℕ) (q H : ℕ → ℝ) (α κ B : ℝ)
    (ha : 0 ≤ α) (hk : 0 ≤ κ) (hb : 0 ≤ B)
    (hB : α * B ^ 2 + κ * B ≤ B ^ 2 / 4)
    (positive : ∀ j ≤ levels, 0 < H j)
    (initial : q 0 ≤ (B * H 0) ^ 2)
    (half : ∀ j < levels, H (j + 1) = H j / 2)
    (step : ∀ j < levels, q (j + 1) ≤ α * q j + κ * H j * Real.sqrt (q j)) :
    ∀ j ≤ levels, q j ≤ (B * H j) ^ 2 := by
  intro j hj
  induction j with
  | zero => exact initial
  | succ j ih =>
    have before : j < levels := by omega
    have hH := (positive j before.le).le
    have old := ih before.le
    have hs : Real.sqrt (q j) ≤ B * H j := by
      simpa [Real.sqrt_sq (mul_nonneg hb hH)] using Real.sqrt_le_sqrt old
    calc
      q (j + 1) ≤ α * q j + κ * H j * Real.sqrt (q j) := step j before
      _ ≤ α * (B * H j) ^ 2 + (κ * H j) * (B * H j) :=
        add_le_add (mul_le_mul_of_nonneg_left old ha)
          (mul_le_mul_of_nonneg_left hs (mul_nonneg hk hH))
      _ = (α * B ^ 2 + κ * B) * (H j) ^ 2 := by ring
      _ ≤ (B ^ 2 / 4) * (H j) ^ 2 := mul_le_mul_of_nonneg_right hB (sq_nonneg _)
      _ = (B * H (j + 1)) ^ 2 := by rw [half j before]; ring

/-- A coefficient α < 1/4 allows any sufficiently large square bound. -/
theorem exists_diagonal_bound (α κ initialBound : ℝ) (ha : α < 1 / 4) :
    ∃ B : ℝ, 0 ≤ B ∧ initialBound ≤ B ∧ α * B ^ 2 + κ * B ≤ B ^ 2 / 4 := by
  let B := max 0 (max initialBound (κ / (1 / 4 - α)))
  have nonneg : 0 ≤ B := le_max_left _ _
  have initial : initialBound ≤ B := le_trans (le_max_left _ _) (le_max_right _ _)
  have lower : κ / (1 / 4 - α) ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
  have bound := (div_le_iff₀ (by linarith : 0 < 1 / 4 - α)).mp lower
  refine ⟨B, nonneg, initial, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right bound nonneg]

/-- Sum the normalized scale costs, counting an explicit final sorting pass.
All cost, scale, and moment estimates are hypotheses supplied by the caller. -/
theorem total_normalized_cost (levels : ℕ) (q H cost : ℕ → ℝ)
    (B μ finish cutoff : ℝ) (hb : 0 ≤ B) (hm : 0 ≤ μ)
    (positive : ∀ j ≤ levels, 0 < H j)
    (bounds : ∀ j ≤ levels, q j ≤ (B * H j) ^ 2)
    (costs : ∀ j < levels, cost j ≤ 1 + μ * Real.sqrt (q j) / H j)
    (last : finish ≤ 1 + μ * Real.sqrt (q levels)) (endScale : H levels ≤ cutoff) :
    (∑ j ∈ range levels, cost j) + finish ≤
      (levels : ℝ) * (1 + μ * B) + (1 + μ * B * cutoff) := by
  have rad (j : ℕ) (hj : j ≤ levels) : Real.sqrt (q j) ≤ B * H j := by
    simpa [Real.sqrt_sq (mul_nonneg hb (positive j hj).le)] using
      Real.sqrt_le_sqrt (bounds j hj)
  have paid (j : ℕ) (hj : j < levels) : cost j ≤ 1 + μ * B := by
    apply (costs j hj).trans
    apply add_le_add_right
    apply (div_le_iff₀ (positive j hj.le)).mpr
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (rad j hj.le) hm
  have subtotal : (∑ j ∈ range levels, cost j) ≤ (levels : ℝ) * (1 + μ * B) := by
    calc
      _ ≤ ∑ _j ∈ range levels, (1 + μ * B) :=
        sum_le_sum (fun j hj => paid j (mem_range.mp hj))
      _ = _ := by simp; ring
  have tail := (rad levels le_rfl).trans (mul_le_mul_of_nonneg_left endScale hb)
  apply add_le_add subtotal
  calc
    finish ≤ 1 + μ * Real.sqrt (q levels) := last
    _ ≤ 1 + μ * (B * cutoff) := add_le_add_right (mul_le_mul_of_nonneg_left tail hm) 1
    _ = _ := by ring

theorem rough65536_coefficient :
    (16 * (1 / 2 : ℚ) ^ 10 + 16 * 10 * 48 / 65536 = 17 / 128) ∧
      (17 / 128 : ℚ) < 1 / 4 := by norm_num






end Shellsort.RoughGapScaleAssembly
