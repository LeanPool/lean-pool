/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastDilation

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastOffsetDropBlock

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The drop history's head block, and what it costs the offset

The account's line producer states its drop history as
`iterationDropSum r F n` — a sum from the **original** origin `k = 1`.  The
offset iteration lemma asks for the history of the shifted sequence, a sum from
the offset.  The two differ by the head block `k ∈ (0, n₀]`, and the print's own
endgame writes its sum from `2 n₀`, so this is exactly the gap between what the
account produces and what the iteration consumes.

The head block costs one thing and it is cheap: every one of its weights is at
most `r ^ j`, its drops telescope, and the total is bounded by `F 0 · r ^ j`.
So the offset recursion holds with source constant

```
delta_offset  =  A · F 0  +  deltaRec ,
```

both summands law-free — `F 0` is the bootstrap floor and `A` is's law-free
recursion constant.  That is the same balance shape
the absolute scale constants already solve, with no delay factor and no
law-dependent inflation.

Both statements below are exact: `iterationDropSum_succ` is the sum's own
recurrence, and the offset bound is that recurrence applied twice, since the
shifted history obeys the identical one.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- **The drop history's recurrence.**  Peeling the top index. -/
theorem iterationDropSum_succ (r : ℝ) (F : ℕ → ℝ) (m : ℕ) :
    iterationDropSum r F (m + 1) =
      r * iterationDropSum r F m + (F m - F (m + 1)) := by
  rw [iterationDropSum, iterationDropSum,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), Finset.mul_sum]
  have hhead : ∑ k ∈ Finset.Icc 1 m,
      r ^ (m + 1 - k) * (F (k - 1) - F k) =
      ∑ k ∈ Finset.Icc 1 m, r * (r ^ (m - k) * (F (k - 1) - F k)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have h : m + 1 - k = (m - k) + 1 := by omega
    rw [h, pow_succ]
    ring
  rw [hhead]
  have htop : r ^ (m + 1 - (m + 1)) * (F (m + 1 - 1) - F (m + 1)) =
      F m - F (m + 1) := by
    simp
  rw [htop]

end

end HCPolySupport.HighContrast.Quenched
