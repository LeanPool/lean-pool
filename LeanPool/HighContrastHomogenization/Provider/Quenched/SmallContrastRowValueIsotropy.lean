/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowCapIsotropyAdjoint
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastPerGenerationRec

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastRowValueIsotropy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The isotropy row value and coefficient

The unparametrized row value and row coefficient contain
`boundaryConst Cd g mAl · 3^{g((t+G)-s)}`, so no bound against them is
independent of `Π`.  The definitions here instead carry the row constant as an
abstract scalar `cRow`:

```
rowCoefficientIsotropy d cRow kap = cRow · (kap · 36(1+d))
rowValue2Isotropy     d cRow kap eps = cRow · (kap · 36(1+d)·eps²)
```

Neither mentions `Cd`, `g`, `mAl` or `G`, so neither can carry `Π`; the
aspect-ratio obligation moves to the caller, who must supply a `cRow` the row
cap proves.  `rowSplitConstant` combines a `Π`-independent head with a deep-leg
term that tends to zero beyond the threshold.

Two simplifications follow.  The original coefficient needs a congruence lemma
(the row coefficient must be shown to depend on the window only through its
height) at the fusion's `hrowEq` step; `rowCoefficientIsotropy` does not mention the
window at all, so that step disappears.  The definition `quadCoefficient` is
already abstract in the row coefficient and is reused directly.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The scalar-parametrized pair -/

/-- **The isotropy row coefficient.**  The parallel definition beside
`rowCoefficient`, with the row's constant abstract. -/
@[expose]
def rowCoefficientIsotropy (d : ℕ) (cRow kap : ℝ) : ℝ :=
  cRow * (kap * (36 * (1 + (d : ℝ))))

/-- **The isotropy row value.**  The parallel definition beside the
unparametrized one. -/
@[expose]
def rowValue2Isotropy (d : ℕ) (cRow kap eps : ℝ) : ℝ :=
  cRow * (kap * (36 * (1 + (d : ℝ)) * eps ^ 2))

/-- **The isotropy analogue of the row-value equation.**  This is the
equation the one-step chain consumes. -/
theorem rowValue2Isotropy_eq_coefficient (d : ℕ) (cRow kap eps : ℝ) :
    rowValue2Isotropy d cRow kap eps = rowCoefficientIsotropy d cRow kap * eps ^ 2 := by
  rw [rowValue2Isotropy, rowCoefficientIsotropy]
  ring

theorem rowCoefficientIsotropy_nonneg {cRow kap : ℝ} (hcRow : 0 ≤ cRow)
    (hkap : 0 ≤ kap) : 0 ≤ rowCoefficientIsotropy d cRow kap := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  rw [rowCoefficientIsotropy]
  positivity

/-! ## The value the split row cap proves -/

/-- **The split row cap's constant**: a `Π`-free head at ratio
`3^{-3/2}`, plus the deep leg, which the caller's threshold drives below any
prescribed tolerance. -/
@[expose]
def rowSplitConstant (cIso cDeep : ℝ) : ℝ :=
  2 * (1 + cIso) * (1 / (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ)))) + cDeep

theorem one_le_row_head_geometric :
    (1 : ℝ) ≤ 1 / (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hlt : (3 : ℝ) ^ (-(3 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [le_div_iff₀ (by linarith only [hlt])]
  linarith only [hpos]

theorem rowSplitConstant_nonneg {cIso cDeep : ℝ} (hcIso : 0 ≤ cIso)
    (hcDeep : 0 ≤ cDeep) : 0 ≤ rowSplitConstant cIso cDeep := by
  have hgeo := one_le_row_head_geometric
  rw [rowSplitConstant]
  nlinarith only [hcIso, hcDeep, hgeo]

end

end HCPolySupport.HighContrast.Quenched
