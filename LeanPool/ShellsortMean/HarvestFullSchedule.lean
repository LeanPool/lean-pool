/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestTenCover
public import LeanPool.ShellsortMean.HarvestTenLegal
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! A size-indexed ordinary Shellsort word, chosen before the input. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestFullSchedule
open Finset Actual214 HarvestBlockIteration HarvestTenSchedule HarvestTenCover

private theorem with_tail {n : ℕ} (hn : 0 < n) (P : RankPlacement n → RankPlacement n)
    (ss : List Stage) (hs : List ℕ) (ws : List PositiveWord) (tail : PositiveWord)
    (cert : Certified P ss hs) (fit : Covers (2 ^ 28) n ss hs ws)
    (end_bound : endCenter n ss ≤ 2 ^ 49) :
    uniformAverage (fun p => (ordinaryWordComparisons (P p) (ws.flatten++tail) : ℝ)) ≤
      ((ws.flatten++tail).length : ℝ) * ((1 + (2 : ℝ) ^ 165) * n) := by
  have pay := certified_comparison_sum hn ss hs ws P n (2 ^ 28) (initial_bound hn P) cert fit
  let P' := fun p => sortWord (P p) (ws.flatten.map Subtype.val)
  have cp := certified_final_bound ss hs P n (initial_bound hn P) cert
  have endR : (endCenter n ss : ℝ) ≤ (2 : ℝ) ^ 49 := by exact_mod_cast end_bound
  have budget : meanEnergy P' ≤ (((2 : ℝ) ^ 164) * (1 : ℕ)) ^ 2 := by
    dsimp only [P']
    rw [covers_word fit]
    apply cp.trans
    unfold scaleBound
    apply pow_le_pow_left₀ (by positivity)
    calc
      _ ≤ (2 : ℝ) ^ 115 * 2 ^ 49 := mul_le_mul_of_nonneg_left endR (by positivity)
      _ = _ := by norm_num
  have tailPay := HarvestWordCost.actual_word_from_square hn (by decide : 0 < 1) P' tail
    (fun k _ => k.property) ((2 : ℝ) ^ 164) (by positivity) budget
  have split : uniformAverage (fun p => (ordinaryWordComparisons (P p) (ws.flatten++tail) : ℝ)) =
      uniformAverage (fun p => (ordinaryWordComparisons (P p) ws.flatten : ℝ)) +
      uniformAverage (fun p => (ordinaryWordComparisons (P' p) tail : ℝ)) := by
    simp only [comparisons_append, Nat.cast_add, uniformAverage_add, P']
  rw [split, List.length_append, Nat.cast_add, add_mul]
  apply add_le_add
  · apply pay.trans
    gcongr; norm_num
  · apply tailPay.trans
    gcongr; norm_num

/-- Bound on the literal key comparison count of a predetermined legal
ordinary linear-insertion Shellsort word for every input size n ≥ 2.
The expectation is over uniform rank permutations. -/
theorem exists_ordinary_shellsort_word (n : ℕ) (hn : 2 ≤ n) :
    ∃ w : PositiveWord,
      (w.map Subtype.val).Pairwise (· > ·) ∧
      (∀ k ∈ w, k.val < n) ∧ (w.map Subtype.val).getLast? = some 1 ∧
      (∀ p : RankPlacement n, sortWord p (w.map Subtype.val) = Equiv.refl _) ∧
      w.length ≤ Nat.log 2 n ∧
      uniformAverage (fun p : RankPlacement n => (ordinaryWordComparisons p w : ℝ)) ≤
        (1 + (2 : ℝ) ^ 165) * (n : ℝ) * Real.logb 2 n := by
  let k := count n
  let S := stages k
  let P : RankPlacement n → RankPlacement n := id
  have hp : 0 < n := by omega
  have centers : Centers n S := centers_from_size hn
  obtain ⟨hs, cert⟩ := select_blocks_from_size hp S centers P
  have picked := certified_choices cert
  obtain ⟨ws, fit⟩ := menu_covers centers picked
  let t := positiveTail (tailCount k)
  let w := ws.flatten ++ t
  have bound := with_tail hp P S hs ws t cert fit (end_center_bound hn)
  have valEq : w.map Subtype.val = realizedWord S hs ++ tailWord k := by
    simp only [w, t, List.map_append, covers_word fit]
    congr 1
    simp [positiveTail, tailWord, List.map_map, Function.comp_def]
  have legal := HarvestTenLegal.full_word_legal hn hs picked
  change (realizedWord S hs ++ tailWord k).Pairwise (· > ·) ∧
    (∀ h ∈ realizedWord S hs ++ tailWord k, 0 < h ∧ h < n) ∧
    (realizedWord S hs ++ tailWord k).getLast? = some 1 at legal
  have wl : w.length = k := by simpa [w, t] using covers_length fit
  have countBound : w.length ≤ Nat.log 2 n := by rw [wl]; exact count_le_log hn
  refine ⟨w, ?_, ?_, ?_, ?_, countBound, ?_⟩
  · rw [valEq]; exact legal.1
  · intro g hg
    have hmem : g.val ∈ w.map Subtype.val := List.mem_map_of_mem hg
    rw [valEq] at hmem
    exact (legal.2.1 _ hmem).2
  · rw [valEq]; exact legal.2.2
  · intro p
    rw [valEq]
    exact HarvestTenLegal.full_word_sorts hn hs picked p
  · have len : (w.length : ℝ) ≤ Real.logb 2 n := by
      exact (show (w.length : ℝ) ≤ (Nat.log 2 n : ℝ) by exact_mod_cast countBound).trans
        (Real.natLog_le_logb n 2)
    apply bound.trans
    change (w.length : ℝ) * ((1 + (2 : ℝ) ^ 165) * n) ≤ _
    rw [mul_comm (w.length : ℝ)]
    exact mul_le_mul_of_nonneg_left len (by positivity)


/-- The witnesses can be a single function of size alone, including the
trivial sizes where the selected word is empty. No planning-time claim. -/
theorem exists_size_indexed_family :
    ∃ W : ℕ → PositiveWord, ∀ n : ℕ, 2 ≤ n →
      ((W n).map Subtype.val).Pairwise (· > ·) ∧
      (∀ k ∈ W n, k.val < n) ∧ ((W n).map Subtype.val).getLast? = some 1 ∧
      (∀ p : RankPlacement n, sortWord p ((W n).map Subtype.val) = Equiv.refl _) ∧
      (W n).length ≤ Nat.log 2 n ∧
      uniformAverage (fun p : RankPlacement n => (ordinaryWordComparisons p (W n) : ℝ)) ≤
        (1 + (2 : ℝ) ^ 165) * (n : ℝ) * Real.logb 2 n := by
  classical
  refine ⟨fun n => if h : 2 ≤ n then Classical.choose (exists_ordinary_shellsort_word n h) else
    [], ?_⟩
  intro n hn
  simp only [dite_eq_left hn]
  exact Classical.choose_spec (exists_ordinary_shellsort_word n hn)

end Shellsort.HarvestFullSchedule
