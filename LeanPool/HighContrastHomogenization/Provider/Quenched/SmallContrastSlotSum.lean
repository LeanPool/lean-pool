/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotAlgebra

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSlotSum

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Summing the variance slots against the linear weight

The refined three-group split
(`weakValueSharpMajorant_le_three_group_summed_at_level`) consumes the variance slots
already summed against the weight `3^{-j/2}`.  This file supplies that sum from
the two per-leg regimes of the slot instantiation, at the depth split
`J := t - j_b`:

* **shallow legs** `j ≤ J` (where `p = t - j ≥ j_b`, so the lagged supply
  applies at the base `j_b`): the source part is
  `c₁·3^{-e(J-j)} + c₂·3^{-(J-j)}` with `e = d/2 ≥ 1`, and the weight
  `3^{-j/2}` turns each such term into at most `(c₁+c₂)·3^{-J/2}`;
* **deep legs** `j > J` (where the supply must be read at its own base, giving
  only a constant `c₃`): the weight alone gives at most `c₃·3^{-J/2}`.

So every weighted term is at most `(c₁+c₂+c₃)·3^{-J/2}`, and the whole sum is
at most `(H_w+1)·(c₁+c₂+c₃)·3^{-J/2}`.  With `J = n - ⌊3n/4⌋ ≥ n/4` this
decays like `3^{-n/8}` up to the polynomial factor `H_w+1` — which is why the
recursion rate must be `α_rec ≤ 1/8 < 1/4` strictly
(`recursionAlpha`, `SmallContrastSlotAlgebra`).
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

open scoped Matrix

noncomputable section

/-- The weight `3^{-j/2}` of the linear slot. -/
@[expose]
def linWeight (j : ℕ) : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ))

theorem linWeight_nonneg (j : ℕ) : 0 ≤ linWeight j :=
  Real.rpow_nonneg (by norm_num) _

end

end HCPolySupport.HighContrast.Quenched
