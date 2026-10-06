/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAccountClauses
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdjointMirrors
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAverageDrops
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMetricFactorAccount
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSkewDagger
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValue

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastHrecInstance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The `hrec` instance at the real constants

Two bridges close the gap between the account's own conclusion and the
drop-history recursion.

* **`hVsum_of_family_sharp`** — the depth-indexed family of stage 2, summed against
  the linear weight through `slot_sum_with_base` and `slotSourceSeq_sum_le_sharp`,
  giving the literal `hVsum` hypothesis of
  `weakValueSharpMajorant_le_three_group_summed_at_level` with the two constants named:

  ```
  slotVsum  = (H_w+1)·(c₁+c₂+c₃)·3^{-J/2} + halfGeom·slotSourceSeq … J 0,
  slotCVsum = halfGeom·(slotBaseCoefficient d + slotBaseCoefficient d).
  ```

  The source constant decays in the generation through `J = ⌈n/4⌉`; this is
  `C_src`'s variance part.

* **`one_step_to_scalar_step_isotropy`** — the account's hatted one-step conclusion,
  read at `eps = d(Θ̂_t − 1)` and with the weak value replaced by the squared
  base `W²`, becomes exactly `hrec_of_one_step_sharp_at_jb`'s scalar input, with the three
  The row value lands in the quadratic slot through the row-value equation.

Composed with `per_generation_hrec_at_recursionAlpha_sharp_at_jb_src` these give the `hrec`
hypothesis at the corrected rate `α = recursionAlpha g`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The summed slot constants -/

/-- The base-scale constant of the summed slot bound. -/
@[expose]
def slotCVsum (d : ℕ) : ℝ :=
  halfGeom * (slotBaseCoefficient d + slotBaseCoefficient d)

/-! ## The account's conclusion in scalar form -/

end

end HCPolySupport.HighContrast.Quenched
