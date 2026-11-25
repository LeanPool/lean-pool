/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.ActualCostComposition
public import LeanPool.ShellsortMean.FirstPassUpper
public import LeanPool.ShellsortMean.NaturalFamily

/-!
End-to-end finite bounds for the specified three-pass construction.
The input law is the uniform law on all rank placements. The counted cost is
the total successful-right-shift counter of the actual insertion executions.
This file does not assert a lower bound for all three-pass gap sequences.
-/
@[expose] public noncomputable section
namespace Shellsort

theorem uniform_secondPassCost_upper (n h g : ℕ) (hh : 0 < h) (hg : 0 < g) :
    uniformAverage (fun p : RankPlacement n => (gapInsertionCost (gapSort p h) g hg : ℝ)) ≤
      (2 / (g : ℝ)) * ((n : ℝ) * ((h : ℝ) - 1 + Real.sqrt ((n : ℝ) * h) / 2)) := by
  exact (uniform_secondPassCost_geometry n h g hg).trans
    (mul_le_mul_of_nonneg_left (uniform_onePass_footrule_bound n h hh) (by positivity))

/-- A finite numerical bound for all positive coprime h,g, applied to the
true three-pass process and its executed right-shift counters. -/
theorem uniform_threePassInsertionCost_upper (n h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) (hc : Nat.Coprime h g) :
    uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) ≤
      (n : ℝ) ^ 2 / (4 * (h : ℝ)) +
      (2 / (g : ℝ)) * ((n : ℝ) * ((h : ℝ) - 1 + Real.sqrt ((n : ℝ) * h) / 2)) +
      (n : ℝ) * (((g : ℝ) - 1) * Real.sqrt ((h : ℝ) + 3) / 2) := by
  rw [uniform_threePassInsertionCost_decomposition]
  exact add_le_add
    (add_le_add (uniform_firstPassCost_upper n h hh) (uniform_secondPassCost_upper n h g hh hg))
    (uniform_thirdPassCost_upper n h g hh hg hc)

/-- The concrete legal gap word is (q²+1,q,1), q=⌊n^(1/4)⌋. -/
def naturalThreePassInsertionCost {n : ℕ} (hn : 16 ≤ n) (p : RankPlacement n) : ℕ :=
  threePassInsertionCost p (fourthRoot n ^ 2 + 1) (fourthRoot n)
    (by positivity) (by have hq := fourthRoot_ge_two n hn; omega)

/-- End-to-end two-sided finite bound for this explicit construction only.
Every cost term is an executed insertion-shift counter at the genuine state;
the uniform input law and the entire state-to-cost chain are proved above. -/
theorem uniform_naturalThreePassInsertionCost_bounds (n : ℕ) (hn : 16 ≤ n) :
    (n : ℝ) * Real.sqrt (n : ℝ) / 8 ≤
        uniformAverage (fun p : RankPlacement n => (naturalThreePassInsertionCost hn p : ℝ)) ∧
      uniformAverage (fun p : RankPlacement n => (naturalThreePassInsertionCost hn p : ℝ)) ≤
        4 * (n : ℝ) * Real.sqrt (n : ℝ) := by
  let q := fourthRoot n
  let h := q ^ 2 + 1
  have hqN : 2 ≤ q := fourthRoot_ge_two n hn
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast hqN
  have hg : 0 < q := by omega
  have hh : 0 < h := by dsimp [h]; positivity
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hg
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR
  have hs4 : (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) ^ 2 := by
    calc
      _ = ((Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hs2]
  have hs3 : (Real.sqrt (n : ℝ)) ^ 3 = (n : ℝ) * Real.sqrt (n : ℝ) := by
    calc
      _ = (Real.sqrt (n : ℝ)) ^ 2 * Real.sqrt (n : ℝ) := by ring
      _ = _ := by rw [hs2]
  have hlo : (q : ℝ) ^ 4 ≤ (n : ℝ) := by exact_mod_cast (fourthRoot_spec n).1
  have hhi : (n : ℝ) < ((q : ℝ) + 1) ^ 4 := by exact_mod_cast (fourthRoot_spec n).2
  have hs := natural_family_scale (q : ℝ) (n : ℝ) hq hlo hhi
  let m₁ := uniformAverage (fun p : RankPlacement n => (gapInsertionCost p h hh : ℝ))
  let m₂ := uniformAverage (fun p : RankPlacement n => (gapInsertionCost (gapSort p h) q hg : ℝ))
  let m₃ := uniformAverage (fun p : RankPlacement n =>
    (gapInsertionCost (gapSort (gapSort p h) q) 1 (by decide) : ℝ))
  have hm₂0 : 0 ≤ m₂ := uniformAverage_nonneg _ (fun p => Nat.cast_nonneg _)
  have hm₃0 : 0 ≤ m₃ := uniformAverage_nonneg _ (fun p => Nat.cast_nonneg _)
  have hm₁ := uniform_firstPassCost_bounds n h hh
  have hm₁lo : (Real.sqrt (n : ℝ)) ^ 4 / (4 * ((q : ℝ) ^ 2 + 1)) -
      (Real.sqrt (n : ℝ)) ^ 2 / 4 ≤ m₁ := by
    simpa only [hs4, hs2, h, Nat.cast_add, Nat.cast_pow, Nat.cast_one] using hm₁.1
  have hm₁up : m₁ ≤ (Real.sqrt (n : ℝ)) ^ 4 / (4 * ((q : ℝ) ^ 2 + 1)) := by
    simpa only [hs4, h, Nat.cast_add, Nat.cast_pow, Nat.cast_one] using hm₁.2
  have hm₂up : m₂ ≤ 2 * (Real.sqrt (n : ℝ)) ^ 2 * q +
      (Real.sqrt (n : ℝ)) ^ 3 * Real.sqrt ((q : ℝ) ^ 2 + 1) / q := by
    have hb := uniform_secondPassCost_upper n h q hh hg
    apply hb.trans_eq
    rw [hs2, hs3]
    simp only [h, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    rw [Real.sqrt_mul hnR]
    field_simp
    ring
  have hm₃up : m₃ ≤ (Real.sqrt (n : ℝ)) ^ 2 * ((q : ℝ) - 1) / 2 *
      Real.sqrt ((q : ℝ) ^ 2 + 4) := by
    have hb := uniform_thirdPassCost_upper n h q hh hg (natural_gap_coprime q)
    apply hb.trans_eq
    rw [hs2]
    simp only [h, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    rw [show (q : ℝ) ^ 2 + 1 + 3 = (q : ℝ) ^ 2 + 4 by ring]
    ring
  have hb := natural_family_finite_bounds (q : ℝ) (Real.sqrt (n : ℝ)) m₁ m₂ m₃
    hq hs.1 hs.2 hm₂0 hm₃0 hm₁lo hm₁up hm₂up hm₃up
  have htotal : uniformAverage (fun p : RankPlacement n =>
      (naturalThreePassInsertionCost hn p : ℝ)) = m₁ + m₂ + m₃ := by
    exact uniform_threePassInsertionCost_decomposition n h q hh hg
  rw [htotal]
  simpa only [hs3, mul_assoc] using hb

end Shellsort
end
