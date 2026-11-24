/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Ring
public import LeanPool.ShellsortMean.PermutationGeometry
public import Mathlib.Logic.Equiv.Basic

/-!
Actual chain inversion counts on rank-to-position permutations. The statistic
counts reversed key pairs at two ordered physical slots. Its equality with an
operational insertion-shift counter is a separate theorem, not assumed here.
-/
@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

def gapPositionPairs (n k : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2 ∧ ij.1.val % k = ij.2.val % k)

def gapInversions {n : ℕ} (p : RankPlacement n) (k : ℕ) : ℕ :=
  ((gapPositionPairs n k).filter (fun ij => p.symm ij.2 < p.symm ij.1)).card

def pairInversionIndicator {n : ℕ} (p : RankPlacement n) (i j : Fin n) : ℝ :=
  if p.symm j < p.symm i then 1 else 0

/-- Swap two physical positions, preserving the uniform law on permutations. -/
def swapPositionsEquiv {n : ℕ} (i j : Fin n) : RankPlacement n ≃ RankPlacement n where
  toFun p := p.trans (Equiv.swap i j)
  invFun p := p.trans (Equiv.swap i j)
  left_inv p := by ext x; simp
  right_inv p := by ext x; simp

theorem swapPositionsEquiv_inverse_left {n : ℕ} (p : RankPlacement n) (i j : Fin n) :
    (swapPositionsEquiv i j p).symm i = p.symm j := by
  simp [swapPositionsEquiv]

theorem swapPositionsEquiv_inverse_right {n : ℕ} (p : RankPlacement n) (i j : Fin n) :
    (swapPositionsEquiv i j p).symm j = p.symm i := by
  simp [swapPositionsEquiv]

theorem swapPositionsEquiv_no_fixed {n : ℕ} (p : RankPlacement n) (i j : Fin n)
    (hij : i ≠ j) : swapPositionsEquiv i j p ≠ p := by
  intro he
  have h := swapPositionsEquiv_inverse_left p i j
  rw [he] at h
  exact hij (p.symm.injective h)

theorem uniformAverage_reindex {n : ℕ} (e : RankPlacement n ≃ RankPlacement n)
    (f : RankPlacement n → ℝ) :
    uniformAverage (fun p => f (e p)) = uniformAverage f := by
  unfold uniformAverage
  rw [e.sum_comp]

theorem uniformAverage_add {n : ℕ} (f g : RankPlacement n → ℝ) :
    uniformAverage (fun p => f p + g p) = uniformAverage f + uniformAverage g := by
  simp only [uniformAverage, Finset.sum_add_distrib, add_div]

theorem pairInversionIndicator_swap_sum {n : ℕ} (p : RankPlacement n) (i j : Fin n)
    (hij : i ≠ j) :
    pairInversionIndicator p i j + pairInversionIndicator (swapPositionsEquiv i j p) i j = 1 := by
  unfold pairInversionIndicator
  rw [swapPositionsEquiv_inverse_left, swapPositionsEquiv_inverse_right]
  have hne : p.symm i ≠ p.symm j := fun he => hij (p.symm.injective he)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · simp [hlt, not_lt_of_gt hlt]
  · simp [hgt, not_lt_of_gt hgt]

/-- Every two distinct fixed original slots are inverted with exact probability 1/2. -/
theorem uniform_pair_inversion_half {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    uniformAverage (fun p : RankPlacement n => pairInversionIndicator p i j) = 1 / 2 := by
  have hp : (fun p : RankPlacement n => pairInversionIndicator p i j +
      pairInversionIndicator (swapPositionsEquiv i j p) i j) = fun _ => (1 : ℝ) :=
    funext (fun p => pairInversionIndicator_swap_sum p i j hij)
  have hm := congrArg uniformAverage hp
  rw [uniformAverage_add,
    uniformAverage_reindex (swapPositionsEquiv i j) (fun p => pairInversionIndicator p i j),
    uniformAverage_const] at hm
  linarith

theorem gapInversions_eq_indicator_sum {n : ℕ} (p : RankPlacement n) (k : ℕ) :
    (gapInversions p k : ℝ) =
      ∑ ij ∈ gapPositionPairs n k, pairInversionIndicator p ij.1 ij.2 := by
  unfold gapInversions pairInversionIndicator
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  rfl

/-- Exact first-pass expectation for the actual inversion statistic. -/
theorem uniform_gapInversions_half_pairs (n k : ℕ) :
    uniformAverage (fun p : RankPlacement n => (gapInversions p k : ℝ)) =
      ((gapPositionPairs n k).card : ℝ) / 2 := by
  simp_rw [gapInversions_eq_indicator_sum]
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]
  change (∑ ij ∈ gapPositionPairs n k,
    uniformAverage (fun p : RankPlacement n => pairInversionIndicator p ij.1 ij.2)) = _
  have he : ∀ ij ∈ gapPositionPairs n k,
      uniformAverage (fun p : RankPlacement n => pairInversionIndicator p ij.1 ij.2) = 1 / 2 := by
    intro ij hij
    have hlt := (Finset.mem_filter.mp hij).2.1
    exact uniform_pair_inversion_half ij.1 ij.2 (ne_of_lt hlt)
  simp only [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul]
  ring

end Shellsort
end
