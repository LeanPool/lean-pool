/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestMenuBlock
public import LeanPool.ShellsortMean.HarvestCutTotals

/-! One completed physical block with both charges measured on its actual
incoming permutation. The two deterministic passes and the uniform menu
are the same as in the per-cut estimate. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestAggregateBudget
open Finset Actual214 RoughGapEndpoint RoughGapScaleAssembly HarvestMenuBlock

/-- Coefficient of incoming global footrule, including the retained low modes. -/
def bF (c g D m : ℕ) : ℝ :=
  4 * 18800 * (g : ℝ) * (D : ℝ) ^ 2 + (c : ℝ) * (((2 * m - 1 : ℕ) : ℝ) * 18800 * (32 + 8 *
    Real.pi / D) + 4)

/-- Coefficient of incoming squared displacement (the summed cut moment is half of it). -/
def bQ (D m : ℕ) : ℝ :=
  ((2 * m - 1 : ℕ) : ℝ) * 18800 * (8 * Real.pi / D) + 4 * (2 + (D : ℝ) ^ 2) / (2 : ℝ) ^ m

def highFoot (c D m : ℕ) : ℝ := (c : ℝ) * (((2 * m - 1 : ℕ) : ℝ) * 18800 * (32 + 8 * Real.pi / D)
  + 4)

private theorem aggregate {n D m : ℕ} (j : ℕ) (p : RankPlacement n) (A : ℝ)
    (step : let z := gapSort (gapSort p (gap (j + 2))) (gap (j + 1))
      (∑ h ∈ choices j, (squareDisplacement (gapSort z h) : ℝ)) / ((choices j).card : ℝ) ≤
        ∑ t ∈ range n, (A * mass p (t + 1) + highBound (gap j) D m (mass z (t + 1)) (cutMoment z
          (t + 1) : ℝ))) :
    let z := gapSort (gapSort p (gap (j + 2))) (gap (j + 1))
    (∑ h ∈ choices j, (squareDisplacement (gapSort z h) : ℝ)) / ((choices j).card : ℝ) ≤
      (A + highFoot (gap j) D m) * footrule p + bQ D m * (squareDisplacement p : ℝ) := by
  intro z
  let c := gap j
  let B := (c : ℝ) * (((2 * m - 1 : ℕ) : ℝ) * 18800 * (32 + 8 * Real.pi / D) + 4)
  let C := bQ D m
  have Bpos : 0 ≤ B := by dsimp [B]; positivity
  have Cpos : 0 ≤ C := by dsimp [C, bQ]; positivity
  have sum_mass (q : RankPlacement n) : (∑ t ∈ range n, mass q (t + 1)) = footrule q :=
    HarvestCutTotals.total_cut_mass q
  have lin (s V : ℝ) : highBound c D m s V = B * s + (2 * C) * V := by
    dsimp [highBound, B, C, bQ]
    ring
  have fmono : footrule z ≤ footrule p :=
    (gapSort_footrule_le _ _).trans (gapSort_footrule_le _ _)
  have qmono : (squareDisplacement z : ℝ) ≤ (squareDisplacement p : ℝ) := by
    exact_mod_cast (HarvestCutTotals.square_le _ _).trans (HarvestCutTotals.square_le p _)
  apply step.trans
  change (∑ t ∈ range n, (A * mass p (t + 1) +
    highBound c D m (mass z (t + 1)) (cutMoment z (t + 1) : ℝ))) ≤ _
  simp only [lin, sum_add_distrib, ←mul_sum, sum_mass, HarvestCutTotals.total_cut_moment]
  have foot := mul_le_mul_of_nonneg_left fmono Bpos
  have sq := mul_le_mul_of_nonneg_left qmono Cpos
  change _ ≤ (A + B) * (footrule p) + C * (squareDisplacement p : ℝ)
  linarith only [foot, sq]

theorem actual_block_budget {n D m : ℕ} (j : ℕ) (hc : 9400 ≤ gap j)
    (hd : 0 < D) (hm : 0 < m) (p : RankPlacement n) :
    let z := gapSort (gapSort p (gap (j + 2))) (gap (j + 1))
    (∑ h ∈ choices j, (squareDisplacement (gapSort z h) : ℝ)) / ((choices j).card : ℝ) ≤
      bF (gap j) (gap (j + 2)) D m * footrule p + bQ D m * (squareDisplacement p : ℝ) :=
  aggregate j p _ (actual_block_square j hc hd hm p)

theorem actual_block_budget_linear {n D m : ℕ} (j : ℕ) (hc : 9400 ≤ gap j)
    (hd : 0 < D) (hm : 0 < m) (p : RankPlacement n) :
    let z := gapSort (gapSort p (gap (j + 2))) (gap (j + 1))
    (∑ h ∈ choices j, (squareDisplacement (gapSort z h) : ℝ)) / ((choices j).card : ℝ) ≤
      (2 * 18800 * (gap (j + 2) : ℝ) * D + highFoot (gap j) D m) * footrule p +
        bQ D m * (squareDisplacement p : ℝ) :=
  aggregate j p _ (actual_block_square_linear j hc hd hm p)

end Shellsort.HarvestAggregateBudget
