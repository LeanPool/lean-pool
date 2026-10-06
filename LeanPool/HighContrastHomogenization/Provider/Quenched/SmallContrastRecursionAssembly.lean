/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastDropRegroup

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastRecursionAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# From the one-step estimate to the iteration lemma's hypothesis

The per-generation one-step estimate of `exists_account_one_step_entry_of_block_at_level`, once
its weak value has been replaced by the `n`-uniform scalar majorant
(the sharp weak-value majorant bound) and its slots by their carriers,
has the scalar shape

  `F n ≤ a·(F(n-H) - F n) + b_q·F(n)² + c_w·W²`,   `W ≤ u + v·F(j_b) + w`,

with `w` the drop group of the weak base and `u` the source group.  This file
performs the last algebraic step: it converts that shape into the literal
hypothesis of the iteration decay,

  `F n ≤ A·∑_{k ∈ [1,n]} r^{n-k}(F(k-1) - F k) + A·F(⌊3n/4⌋)² + δ·r^n`.

Three things happen here and nowhere else:

* the single lagged drop `F(n-H) - F n` is charged to the drop-history sum
  (`single_drop_le_iteration_sharp`) at the fixed cost `r^{-H}(1-r)^{-1}` — `H` is
  the absorption lag, chosen once, so this is a constant;
* the weak base is squared and split, so the `F(j_b)`-linear part of the weak
  value becomes the *quadratic* slot `A·F(⌊3n/4⌋)²` (this is the printed
  mechanism of accelerated convergence: the weak value is squared, and the
  per-scale variances are linear in the hatted excess at the base scale);
* the source group is charged to `δ·r^n` — **the entry-exponent condition**
  `3 c_w u_n² ≤ δ r^n`, which is what fixes the admissible `α` and therefore
  the entry delay.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- The drop-history sum consumed by the iteration decay. -/
@[expose]
def iterationDropSum (r : ℝ) (F : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, r ^ (n - k) * (F (k - 1) - F k)

theorem iterationDropSum_nonneg {F : ℕ → ℝ}
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p) {r : ℝ} (hr0 : 0 ≤ r) (n : ℕ) :
    0 ≤ iterationDropSum r F n :=
  iteration_sum_nonneg hFmono hr0 n

end

end HCPolySupport.HighContrast.Quenched
