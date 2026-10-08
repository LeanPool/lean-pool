/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSubdivisionSupply

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastHvarFamily

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The `hvar` family at every depth

`exists_account_one_step_entry_of_block_at_level` consumes a real family
`V : ℕ → ℝ` with `scaleVariance … (t - j) ≤ ofReal (V j)` at every depth
`j ≤ H_w`.  This file builds that family from the two regimes of-13.2 and
discharges the bound at every depth from a *single* scalar hypothesis — the
bootstrap smallness `hatExcessAt P q k ≤ δ` on the whole range — plus the
account's own data and the subdivision supply of stage 1.

The family is

```
slotFamilyValue d Csub Msc δ F(j_b) J j
  = slotSourceSeq d Csub Msc δ J j + slotBaseCoefficient d · F(j_b),
```

with `J = (t - j_b).toNat`; `slotSourceSeq` is the shallow value at lag `J - j`
for `j ≤ J` and the deep constant beyond.  All the premises of the two slot
theorems are produced here from `δ ≤ 1/4`, `hat_drop_le_hatExcess` and the
monotonicity of the entry threshold in the scale.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- The per-depth value of the variance slot family. -/
@[expose]
def slotFamilyValue (d : ℕ) (Csub Msc delta Fjb : ℝ) (J j : ℕ) : ℝ :=
  slotSourceSeq d Csub Msc delta J j + slotBaseCoefficient d * Fjb

theorem slotFamilyValue_nonneg (d : ℕ) {Csub Msc delta Fjb : ℝ}
    (hCsub : 0 ≤ Csub) (hMsc : 0 ≤ Msc) (hdelta : 0 ≤ delta)
    (hFjb : 0 ≤ Fjb) (J j : ℕ) :
    0 ≤ slotFamilyValue d Csub Msc delta Fjb J j := by
  rw [slotFamilyValue]
  exact add_nonneg (slotSourceSeq_nonneg d hCsub hMsc hdelta J j)
    (mul_nonneg (slotBaseCoefficient_nonneg d) hFjb)

end

end HCPolySupport.HighContrast.Quenched
