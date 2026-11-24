/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.GapComparisonBridge
public import LeanPool.ShellsortMean.NaturalThreePass

/-!
Actual linear-search key-comparison counters along the three genuine insertion
checkpoints. These results are for a specified implementation and specified
natural gap family; they are not claims about arbitrary comparison strategies,
unrestricted gap optimality, or total machine time.
-/
@[expose] public noncomputable section
namespace Shellsort

/-- The executed comparison count for gap passes `h`, `g` and one. -/
def threePassComparisonCost {n : ℕ} (p : RankPlacement n) (h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) : ℕ :=
  gapComparisonCost p h hh + gapComparisonCost (gapSort p h) g hg +
    gapComparisonCost (gapSort (gapSort p h) g) 1 (by decide)

theorem threePassComparisonCost_bounds {n : ℕ} (p : RankPlacement n) (h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) :
    threePassInsertionCost p h g hh hg ≤ threePassComparisonCost p h g hh hg ∧
      threePassComparisonCost p h g hh hg ≤ threePassInsertionCost p h g hh hg + 3 * n := by
  have h₁ := gapComparisonCost_lower p h hh
  have h₂ := gapComparisonCost_lower (gapSort p h) g hg
  have h₃ := gapComparisonCost_lower (gapSort (gapSort p h) g) 1 (by decide)
  have h₁' := gapComparisonCost_upper p h hh
  have h₂' := gapComparisonCost_upper (gapSort p h) g hg
  have h₃' := gapComparisonCost_upper (gapSort (gapSort p h) g) 1 (by decide)
  unfold threePassInsertionCost threePassComparisonCost
  omega

theorem uniform_threePassComparisonCost_bounds (n h g : ℕ) (hh : 0 < h) (hg : 0 < g) :
    uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) ≤
        uniformAverage (fun p : RankPlacement n => (threePassComparisonCost p h g hh hg : ℝ)) ∧
      uniformAverage (fun p : RankPlacement n => (threePassComparisonCost p h g hh hg : ℝ)) ≤
        uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) + 3
          * n := by
  constructor
  · apply uniformAverage_mono
    intro p
    exact_mod_cast (threePassComparisonCost_bounds p h g hh hg).1
  · have hb := uniformAverage_mono
      (fun p : RankPlacement n => (threePassComparisonCost p h g hh hg : ℝ))
      (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ) + 3 * n)
      (fun p => by exact_mod_cast (threePassComparisonCost_bounds p h g hh hg).2)
    simpa only [uniformAverage_add, uniformAverage_const] using hb

/-- The comparison count of the three-pass word built from the integer fourth root. -/
def naturalThreePassComparisonCost {n : ℕ} (hn : 16 ≤ n) (p : RankPlacement n) : ℕ :=
  threePassComparisonCost p (fourthRoot n ^ 2 + 1) (fourthRoot n)
    (by positivity) (by have hq := fourthRoot_ge_two n hn; omega)

/-- Finite end-to-end comparison bound for q=floor(n^(1/4)), gaps (q²+1,q,1). -/
theorem uniform_naturalThreePassComparisonCost_bounds (n : ℕ) (hn : 16 ≤ n) :
    (n : ℝ) * Real.sqrt (n : ℝ) / 8 ≤
        uniformAverage (fun p : RankPlacement n => (naturalThreePassComparisonCost hn p : ℝ)) ∧
      uniformAverage (fun p : RankPlacement n => (naturalThreePassComparisonCost hn p : ℝ)) ≤
        4 * (n : ℝ) * Real.sqrt (n : ℝ) + 3 * n := by
  have hq : 0 < fourthRoot n := by have := fourthRoot_ge_two n hn; omega
  have hb := uniform_threePassComparisonCost_bounds n (fourthRoot n ^ 2 + 1) (fourthRoot n)
    (by positivity) hq
  have hm := uniform_naturalThreePassInsertionCost_bounds n hn
  change _ ≤ uniformAverage (fun p : RankPlacement n => (naturalThreePassComparisonCost hn p : ℝ)) ∧
    uniformAverage (fun p : RankPlacement n => (naturalThreePassComparisonCost hn p : ℝ)) ≤ _
  change uniformAverage (fun p : RankPlacement n => (naturalThreePassInsertionCost hn p : ℝ)) ≤
      uniformAverage (fun p : RankPlacement n => (naturalThreePassComparisonCost hn p : ℝ)) ∧
    uniformAverage (fun p : RankPlacement n => (naturalThreePassComparisonCost hn p : ℝ)) ≤
      uniformAverage (fun p : RankPlacement n => (naturalThreePassInsertionCost hn p : ℝ)) + 3 *
        n at hb
  constructor
  · exact hm.1.trans hb.1
  · linarith [hb.2, hm.2]

/-- Clean constant-factor comparison estimate; the sharper additive bound is above. -/
theorem uniform_naturalThreePassComparisonCost_scaled (n : ℕ) (hn : 16 ≤ n) :
    (n : ℝ) * Real.sqrt (n : ℝ) / 8 ≤
        uniformAverage (fun p : RankPlacement n => (naturalThreePassComparisonCost hn p : ℝ)) ∧
      uniformAverage (fun p : RankPlacement n => (naturalThreePassComparisonCost hn p : ℝ)) ≤
        5 * (n : ℝ) * Real.sqrt (n : ℝ) := by
  have hb := uniform_naturalThreePassComparisonCost_bounds n hn
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hs : 4 ≤ Real.sqrt (n : ℝ) := by nlinarith
  have hp := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    (show 0 ≤ Real.sqrt (n : ℝ) - 3 by linarith)
  exact ⟨hb.1, by nlinarith [hb.2]⟩

end Shellsort
end
