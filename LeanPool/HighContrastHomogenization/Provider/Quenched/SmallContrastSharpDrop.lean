/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRecursionAssembly

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSharpDrop

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The sharp single-drop bound: `hA1` without the geometric slack

`hA1` (`HCPoly.Provider.Quenched.SmallContrastRecursionAssembly`) demands

```
a * ((r ^ H)⁻¹ * (1 - r)⁻¹) + 3 * cw * cdrop ≤ A
```

so the recursion constant `A` absorbs both `3 ^ (alpha * H)` and
`(1 - 3 ^ (-alpha))⁻¹ ≈ 1 / (alpha * log 3)`.  The second factor is's
`A ≳ 1/alpha`, and it is what made `hsmall` demand `deltaRec = O(alpha ^ 5)`
instead of AK.Book's `O(alpha ^ 2)`.

**The `(1 - r)⁻¹` is pure slack.**  `single_drop_le_iteration_sharp` obtains the
lagged drop by bounding *one term* by a *whole sum*
(`Finset.single_le_sum`) and then paying `lagged_drop_sum_le`'s geometric
factor for that sum.  Bounding the single term directly costs nothing:
writing `a i := F (n-i-1) - F (n-i) ≥ 0`, the drop telescopes and every weight
in range is at least `r ^ H`, so

```
r ^ H * (F (n-H) - F n) = ∑_{i<H} r ^ H * a i ≤ ∑_{i<H} r ^ i * a i
                        ≤ ∑_{i<n} r ^ i * a i = iterationDropSum r F n .
```

This file proves that, giving

```
F (n-H) - F n ≤ (r ^ H)⁻¹ * iterationDropSum r F n
```

with **no `(1 - r)⁻¹`**, and re-derives the recursion step from it so that `A`
carries only `(r ^ H)⁻¹`.  `H` is a window height, not a rate, so `A` is then
free of the `1/alpha` blow-up.

These are **parallel declarations beside** the defective
ones, not bounds on them: `single_drop_le_iteration_sharp` and `hrec_final_sharp_at_jb_src` are left
untouched, and the `_sharp` forms sit next to them.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-! ## The weight is antitone -/

/-- For `0 < r < 1` the powers of `r` are antitone in the exponent. -/
private theorem pow_le_pow_of_lt_one_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {i H : ℕ} (hiH : i ≤ H) : r ^ H ≤ r ^ i := by
  have hsplit : r ^ H = r ^ i * r ^ (H - i) := by
    rw [← pow_add]
    congr 1
    omega
  have h1 : r ^ (H - i) ≤ 1 := pow_le_one₀ hr0.le hr1.le
  calc r ^ H = r ^ i * r ^ (H - i) := hsplit
    _ ≤ r ^ i * 1 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hr0.le i)
    _ = r ^ i := mul_one _

/-! ## The telescoping and the reindexing -/

/-- The partial sums of the one-step increments telescope to the lagged
drops. -/
private theorem increment_partial_sum {F : ℕ → ℝ} (n : ℕ) :
    ∀ j : ℕ, ∑ i ∈ Finset.range j, (F (n - i - 1) - F (n - i)) =
      F (n - j) - F n := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep : n - (j + 1) = n - j - 1 := by omega
      rw [hstep]
      ring

/-- The depth-indexed increment sum is the generation-indexed drop sum. -/
private theorem increment_sum_reindex {F : ℕ → ℝ} {r : ℝ} (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i * (F (n - i - 1) - F (n - i)) =
      ∑ k ∈ Finset.Icc 1 n, r ^ (n - k) * (F (k - 1) - F k) := by
  refine Finset.sum_nbij' (fun i => n - i) (fun k => n - k) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    show n - (n - i) = i
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    show n - (n - k) = k
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    have h1 : n - (n - i) = i := by omega
    rw [h1]

/-! ## The sharp single-drop bound -/

/-- **The lagged drop, without the geometric factor.**  For a nonincreasing
`F` and `0 < r < 1`,

  `F (n-H) - F n ≤ (r ^ H)⁻¹ * iterationDropSum r F n`.

Compare `single_drop_le_iteration_sharp`, which carries a spurious `(1 - r)⁻¹`
because it bounds this single term by the whole depth-indexed sum before
converting. -/
theorem single_drop_le_iteration_sharp {F : ℕ → ℝ}
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {n H : ℕ} (hH : H + 1 ≤ n) :
    F (n - H) - F n ≤ (r ^ H)⁻¹ * iterationDropSum r F n := by
  classical
  have ha0 : ∀ i : ℕ, 0 ≤ F (n - i - 1) - F (n - i) := fun i =>
    sub_nonneg.mpr (hFmono _ _ (Nat.sub_le _ _))
  have hrH : 0 < r ^ H := pow_pos hr0 H
  have hkey : r ^ H * (F (n - H) - F n) ≤ iterationDropSum r F n := by
    have h1 : r ^ H * (F (n - H) - F n) =
        ∑ i ∈ Finset.range H, r ^ H * (F (n - i - 1) - F (n - i)) := by
      rw [← increment_partial_sum (F := F) n H, Finset.mul_sum]
    have h2 : ∑ i ∈ Finset.range H, r ^ H * (F (n - i - 1) - F (n - i)) ≤
        ∑ i ∈ Finset.range H, r ^ i * (F (n - i - 1) - F (n - i)) := by
      refine Finset.sum_le_sum fun i hi => ?_
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_lt_one_le hr0 hr1
          (le_of_lt (Finset.mem_range.mp hi))) (ha0 i)
    have h3 : ∑ i ∈ Finset.range H, r ^ i * (F (n - i - 1) - F (n - i)) ≤
        ∑ i ∈ Finset.range n, r ^ i * (F (n - i - 1) - F (n - i)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun i _ _ => mul_nonneg (pow_nonneg hr0.le i) (ha0 i))
      intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    calc r ^ H * (F (n - H) - F n)
        = ∑ i ∈ Finset.range H, r ^ H * (F (n - i - 1) - F (n - i)) := h1
      _ ≤ ∑ i ∈ Finset.range H, r ^ i * (F (n - i - 1) - F (n - i)) := h2
      _ ≤ ∑ i ∈ Finset.range n, r ^ i * (F (n - i - 1) - F (n - i)) := h3
      _ = iterationDropSum r F n := increment_sum_reindex n
  rw [← le_div_iff₀' hrH] at hkey
  rw [inv_mul_eq_div]
  exact hkey

/-! ## The recursion step at the sharp constant -/

end

end HCPolySupport.HighContrast.Quenched
