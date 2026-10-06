/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBootstrapSmallness
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateParts
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRealClauses
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSplitAdapters

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBurnInUniform

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn-in as a threshold independent of the grid base

The use-site check settles this in the affirmative.

`exists_bootstrap_smallness_uniform_minimal`
(`HCPoly.Provider.Quenched.SmallContrastBootstrapSmallness`)
produces `N1 = sK + 1 + gap`, where `gap` comes from

```
exists_gap_three_pow_le (mul_pos hCB0 hfac0) hsigma0
```

with `hfac0 : 0 < bootstrapAdapterFactor Cd g K E mAl`.  So `gap` depends on
`CB` (a function of `d` and `g`), on `bootstrapAdapterFactor Cd g K E mAl`, and
on `sigma` — **and on nothing else.  In particular not on the grid base `lq`.**

Confirming this at the source: in `exists_bootstrap_tilt_bound`
the quantifier `∀ lq` precedes `∀ gap`, but the gap's own side condition

```
CB * bootstrapAdapterFactor Cd g K E mAl * 3 ^ (-(gap : ℝ)) ≤ sigma
```

is `lq`-free, and so is the scale bound `sK + 1 + gap ≤ n`.  Hence **one `gap`
serves every grid base simultaneously**, and the burn-in may be chosen before
the base rather than after it.

`exists_bootstrap_smallness_uniform_minimal` below is that reordering: same constant,
same proof, with `lq` introduced after `gap`.  It closes — the endpoint
may now instantiate at `lq := N1`, so the smallness floor holds **from the grid
base**, which is what `exists_one_step_with_slots_of_block_at_level_conv_split` demands.

This is a parallel declaration beside `exists_bootstrap_smallness_uniform_minimal`,
which is untouched.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-- **The floor from the grid base.**  Instantiating the uniform burn-in at
`lq := N1` gives the smallness clause in exactly the form
`exists_one_step_with_slots_of_block_at_level_conv_split` demands: the whole ray from the base. -/
theorem bootstrap_floor_from_base {d : ℕ} {P : Measure (CoeffSpace d)}
    {mAl : Mat d} {delta : ℝ} {N1 : ℤ}
    (hbase : (kZero d : ℤ) ≤ N1)
    (hfloor : ∀ lq : ℤ, (kZero d : ℤ) ≤ lq →
      ∀ n : ℤ, N1 ≤ n → hatExcessAt P (roundedGrid lq mAl) n ≤ delta) :
    ∀ k : ℤ, N1 ≤ k → hatExcessAt P (roundedGrid N1 mAl) k ≤ delta :=
  hfloor N1 hbase

end

end HCPolySupport.HighContrast.Quenched
