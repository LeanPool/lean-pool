/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.ChainInversionBound
public import LeanPool.ShellsortMean.FirstPassCostBounds
public import LeanPool.ShellsortMean.GapInsertionOutput
public import LeanPool.ShellsortMean.TaggedUpper

/-!
Composition of actual insertion right-shift counters along actual gapSort
checkpoints. GapInsertionOutput proves that these checkpoints are precisely
the outputs of the executed chain insertion routines.
-/
@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

theorem uniformAverage_mono {n : ℕ} (f g : RankPlacement n → ℝ)
    (hfg : ∀ p, f p ≤ g p) : uniformAverage f ≤ uniformAverage g := by
  unfold uniformAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun p _ => hfg p))
    (Nat.cast_nonneg _)

theorem uniformAverage_nonneg {n : ℕ} (f : RankPlacement n → ℝ)
    (hf : ∀ p, 0 ≤ f p) : 0 ≤ uniformAverage f := by
  unfold uniformAverage
  exact div_nonneg (Finset.sum_nonneg (fun p _ => hf p)) (Nat.cast_nonneg _)

theorem uniformAverage_const_mul {n : ℕ} (c : ℝ) (f : RankPlacement n → ℝ) :
    uniformAverage (fun p => c * f p) = c * uniformAverage f := by
  unfold uniformAverage
  rw [← Finset.mul_sum, mul_div_assoc]

/-- The sum of the three executed successful-right-shift counters, evaluated
at their genuine successive states. The key-comparison cost is separate. -/
def threePassInsertionCost {n : ℕ} (p : RankPlacement n) (h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) : ℕ :=
  gapInsertionCost p h hh +
    gapInsertionCost (gapSort p h) g hg +
    gapInsertionCost (gapSort (gapSort p h) g) 1 (by decide)

theorem uniform_threePassInsertionCost_decomposition (n h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) :
    uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) =
      uniformAverage (fun p : RankPlacement n => (gapInsertionCost p h hh : ℝ)) +
      uniformAverage (fun p : RankPlacement n => (gapInsertionCost (gapSort p h) g hg : ℝ)) +
      uniformAverage (fun p : RankPlacement n =>
        (gapInsertionCost (gapSort (gapSort p h) g) 1 (by decide) : ℝ)) := by
  simp only [threePassInsertionCost, Nat.cast_add, uniformAverage_add]

/-- The second-pass input remains the actual first-pass state; its law is
never replaced by a fresh independent or uniform permutation. -/
theorem uniform_secondPassCost_geometry (n h g : ℕ) (hg : 0 < g) :
    uniformAverage (fun p : RankPlacement n => (gapInsertionCost (gapSort p h) g hg : ℝ)) ≤
      (2 / (g : ℝ)) * uniformAverage (fun p : RankPlacement n => footrule (gapSort p h)) := by
  rw [← uniformAverage_const_mul]
  apply uniformAverage_mono
  intro p
  have hb := gapInsertionCost_le_two_footrule_div (gapSort p h) g hg
  convert hb using 1
  ring

/-- The two-pass residual-state bound gives a true average cost bound for
the final executed insertion pass, with no assumed state-to-cost interface. -/
theorem uniform_thirdPassCost_upper (n h g : ℕ) (hh : 0 < h)
    (hg : 0 < g) (hc : Nat.Coprime h g) :
    uniformAverage (fun p : RankPlacement n =>
      (gapInsertionCost (gapSort (gapSort p h) g) 1 (by decide) : ℝ)) ≤
      (n : ℝ) * (((g : ℝ) - 1) * Real.sqrt ((h : ℝ) + 3) / 2) := by
  exact (uniformAverage_mono _ _ (fun p => ordinaryInsertionCost_le_footrule
    (gapSort (gapSort p h) g))).trans (uniform_twoPass_footrule_bound n h g hh hg hc)

/-- A finite lower bound for every positive first/second gap, supplied by
the actual first-pass cost alone. It is not a uniform n^(3/2) lower bound. -/
theorem uniform_threePassInsertionCost_lower (n h g : ℕ) (hh : 0 < h) (hg : 0 < g) :
    (n : ℝ) ^ 2 / (4 * (h : ℝ)) - (n : ℝ) / 4 ≤
      uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) := by
  apply (uniform_firstPassCost_lower n h hh).trans
  apply uniformAverage_mono
  intro p
  have hl : gapInsertionCost p h hh ≤ threePassInsertionCost p h g hh hg := by
    unfold threePassInsertionCost
    omega
  exact_mod_cast hl

/-- Finite three-pass upper interface expressed entirely in true process
quantities. Only the actual first-pass footrule mean still needs evaluation. -/
theorem uniform_threePassInsertionCost_geometry_upper (n h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) (hc : Nat.Coprime h g) :
    uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) ≤
      (n : ℝ) ^ 2 / (4 * (h : ℝ)) +
      (2 / (g : ℝ)) * uniformAverage (fun p : RankPlacement n => footrule (gapSort p h)) +
      (n : ℝ) * (((g : ℝ) - 1) * Real.sqrt ((h : ℝ) + 3) / 2) := by
  rw [uniform_threePassInsertionCost_decomposition]
  exact add_le_add
    (add_le_add (uniform_firstPassCost_upper n h hh) (uniform_secondPassCost_geometry n h g hg))
    (uniform_thirdPassCost_upper n h g hh hg hc)

end Shellsort
end
