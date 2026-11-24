/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestScaleNumbers

/-! Deterministically select a common list of physical gap choices for
any supplied finite sequence of block centers and fixed suffixes. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestBlockIteration
open Finset Actual214 RoughGapScaleAssembly HarvestScaleNumbers HarvestMenuBlock

/-- A block of three core passes followed by a fixed suffix of further passes. -/
structure Stage where
  /-- The index of the center for the third core gap. -/
  j : ℕ
  /-- The fixed gaps used after the three core passes. -/
  suffix : List ℕ

/-- The upper budget for the mean squared displacement at center `c`. -/
def scaleBound (c : ℕ) : ℝ := ((2 : ℝ) ^ 115 * c) ^ 2
/-- Mean normalized squared displacement after applying the prefix map to uniform inputs. -/
def meanEnergy {n : ℕ} (P : RankPlacement n → RankPlacement n) : ℝ :=
  uniformAverage (fun p => RoughGapSelection.energy (P p))

/-- The two retained gaps, the selected third gap and the fixed suffix. -/
def stageWord (s : Stage) (h : ℕ) : List ℕ :=
  gap (s.j + 2) :: gap (s.j + 1) :: h :: s.suffix

/-- The lower-size and ratio requirements on the sequence of block centers. -/
def Centers : ℕ → List Stage → Prop
  | _, [] => True
  | prev, s::ss => 9400 ≤ gap s.j ∧ prev ≤ 2 ^ 16 * gap s.j ∧ Centers (gap s.j) ss

/-- A selected list with a genuine input-independent menu tag per block.
The incoming prefix for the recursive call includes its real sorted suffix. -/
def Certified {n : ℕ} (P : RankPlacement n → RankPlacement n) : List Stage → List ℕ → Prop
  | [], hs => hs = []
  | _::_, [] => False
  | s::ss, h::hs =>
      h ∈ choices s.j ∧
      meanEnergy (fun p => block s.j h (P p)) ≤ scaleBound (gap s.j) ∧
      meanEnergy (fun p => sortWord (P p) (stageWord s h)) ≤ scaleBound (gap s.j) ∧
      Certified (fun p => sortWord (P p) (stageWord s h)) ss hs

theorem word_square_le {n : ℕ} (p : RankPlacement n) (w : List ℕ) :
    squareDisplacement (sortWord p w) ≤ squareDisplacement p := by
  induction w generalizing p with
  | nil => rfl
  | cons h hs ih => exact (ih (gapSort p h)).trans (HarvestCutTotals.square_le p h)

theorem word_mean_le {n : ℕ} (P : RankPlacement n → RankPlacement n) (w : List ℕ) :
    meanEnergy (fun p => sortWord (P p) w) ≤ meanEnergy P := by
  apply uniformAverage_mono
  intro p
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast word_square_le (P p) w

/-- Scale arithmetic. The old quadratic term uses at most 2^-15 of the new
budget. The square-root term uses at most one half. -/
theorem contract_scales {x : ℝ} {prev c : ℕ} (old : x ≤ scaleBound prev)
    (ratio : prev ≤ 2 ^ 16 * c) :
    (1 / (2 : ℝ) ^ 47) * x + (2 : ℝ) ^ 98 * c * Real.sqrt x ≤ scaleBound c := by
  have s : (prev : ℝ) ≤ (2 : ℝ) ^ 16 * c := by exact_mod_cast ratio
  have scaled : (2 : ℝ) ^ 115 * prev ≤ (2 : ℝ) ^ 115 * ((2 : ℝ) ^ 16 * c) := by gcongr
  have sq : x ≤ ((2 : ℝ) ^ 115 * ((2 : ℝ) ^ 16 * c)) ^ 2 :=
    old.trans (pow_le_pow_left₀ (by positivity) scaled 2)
  have rt := (Real.sqrt_le_sqrt sq).trans_eq (Real.sqrt_sq (by positivity))
  calc
    _ ≤ (1 / (2 : ℝ) ^ 47) * ((2 : ℝ) ^ 115 * ((2 : ℝ) ^ 16 * c)) ^ 2 +
        (2 : ℝ) ^ 98 * c * ((2 : ℝ) ^ 115 * ((2 : ℝ) ^ 16 * c)) := by gcongr
    _ ≤ scaleBound c := by
      dsimp [scaleBound]
      ring_nf
      gcongr; norm_num

/-- Every stage has its own shared gap, selected against the pushforward
of the original input law by the previously fixed execution. -/
theorem select_blocks {n : ℕ} (hn : 0 < n) (ss : List Stage) (prev : ℕ)
    (centers : Centers prev ss) (P : RankPlacement n → RankPlacement n)
    (initial : meanEnergy P ≤ scaleBound prev) : ∃ hs, Certified P ss hs := by
  induction ss generalizing prev P with
  | nil => exact ⟨[], rfl⟩
  | cons s ss ih =>
    obtain ⟨large, ratio, rest⟩ := centers
    obtain ⟨h, legal, sel⟩ := select_actual_linear_block hn P s.j large
    have core : meanEnergy (fun p => block s.j h (P p)) ≤ scaleBound (gap s.j) :=
      sel.trans (contract_scales initial ratio)
    have post : meanEnergy (fun p => sortWord (P p) (stageWord s h)) ≤ scaleBound (gap s.j) := by
      simp only [stageWord, sortWord]
      have mid := word_mean_le (fun p => block s.j h (P p)) s.suffix
      exact (show meanEnergy (fun p => sortWord (block s.j h (P p)) s.suffix) ≤
        scaleBound (gap s.j) from mid.trans core)
    obtain ⟨hs, tail⟩ := ih (gap s.j) rest _ post
    exact ⟨h::hs, legal, core, post, tail⟩

theorem initial_bound {n : ℕ} (hn : 0 < n) (P : RankPlacement n → RankPlacement n) :
    meanEnergy P ≤ scaleBound n := by
  have N : (0 : ℝ) < n := by exact_mod_cast hn
  have point (p : RankPlacement n) : RoughGapSelection.energy (P p) ≤ (n : ℝ) ^ 2 := by
    apply (div_le_iff₀ N).mpr
    simp only [squareDisplacement, Int.cast_sum, Int.cast_pow, Int.cast_sub, Int.cast_natCast]
    calc
      _ ≤ ∑ _i : Fin n, (n : ℝ) ^ 2 := by
        apply sum_le_sum
        intro i _
        have u : (((P p) i).val : ℝ) ≤ n := by exact_mod_cast ((P p) i).isLt.le
        have v : (i.val : ℝ) ≤ n := by exact_mod_cast i.isLt.le
        have lo : - (n : ℝ) ≤ (((P p) i).val : ℝ) - i.val := by
          linarith [Nat.cast_nonneg (α := ℝ) ((P p) i).val]
        have hi : (((P p) i).val : ℝ) - i.val ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) i.val]
        nlinarith [mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr lo)]
      _ = _ := by simp [mul_comm]
  have h := uniformAverage_mono _ _ point
  rw [uniformAverage_const] at h
  apply h.trans
  dsimp [scaleBound]
  rw [mul_pow]
  exact le_mul_of_one_le_left (sq_nonneg _) (by norm_num)

/-- Entry from arbitrary fixed preprocessing, using n as the initial scale. -/
theorem select_blocks_from_size {n : ℕ} (hn : 0 < n) (ss : List Stage)
    (centers : Centers n ss) (P : RankPlacement n → RankPlacement n) :
    ∃ hs, Certified P ss hs :=
  select_blocks hn ss n centers P (initial_bound hn P)

/-- Write the actual ordinary gap list in its execution order. -/
def realizedWord : List Stage → List ℕ → List ℕ
  | s::ss, h::hs => stageWord s h ++ realizedWord ss hs
  | _, _ => []

/-- The center reached after running the listed blocks, with the initial center as default. -/
def endCenter : ℕ → List Stage → ℕ
  | prev, [] => prev
  | _, s::ss => endCenter (gap s.j) ss

theorem certified_choices {n : ℕ} {P : RankPlacement n → RankPlacement n}
    {ss : List Stage} {hs : List ℕ} (hc : Certified P ss hs) :
    List.Forall₂ (fun s h => h ∈ choices s.j) ss hs := by
  induction ss generalizing P hs with
  | nil => obtain rfl : hs = [] := hc; exact .nil
  | cons s ss ih =>
    cases hs with
    | nil => exact False.elim hc
    | cons h hs => exact .cons hc.1 (ih hc.2.2.2)

private theorem sort_append {n : ℕ} (p : RankPlacement n) (u v : List ℕ) :
    sortWord p (u++v) = sortWord (sortWord p u) v := by
  induction u generalizing p with
  | nil => rfl
  | cons h hs ih => exact ih (gapSort p h)

theorem certified_final_bound {n : ℕ} (ss : List Stage) (hs : List ℕ)
    (P : RankPlacement n → RankPlacement n) (prev : ℕ)
    (prior : meanEnergy P ≤ scaleBound prev) (hc : Certified P ss hs) :
    meanEnergy (fun p => sortWord (P p) (realizedWord ss hs)) ≤ scaleBound (endCenter prev ss) := by
  induction ss generalizing hs P prev with
  | nil => obtain rfl : hs = [] := hc; exact prior
  | cons s ss ih =>
    cases hs with
    | nil => exact False.elim hc
    | cons h hs =>
      simp only [realizedWord, sort_append, endCenter]
      exact ih hs _ (gap s.j) hc.2.2.1 hc.2.2.2

/-- Comparison budget for any individual positive pass after any additional
fixed prefix, as charged by ordinary gapped linear insertion. -/
theorem pass_comparisons_from_budget {n h : ℕ} (hn : 0 < n) (hh : 0 < h)
    (P : RankPlacement n → RankPlacement n) (w : List ℕ) (c : ℕ)
    (budget : meanEnergy P ≤ scaleBound c) :
    uniformAverage (fun p =>
      (gapComparisonCost (sortWord (P p) w) h hh : ℝ) / n) ≤
        1 + (2 / (h : ℝ)) * ((2 : ℝ) ^ 115 * c) := by
  apply (RoughGapSelection.prefix_mean_comparisons hn hh
    (fun p => sortWord (P p) w)).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Real.sqrt_le_sqrt ((word_mean_le P w).trans budget)).trans_eq
    (Real.sqrt_sq (by positivity))

end Shellsort.HarvestBlockIteration
