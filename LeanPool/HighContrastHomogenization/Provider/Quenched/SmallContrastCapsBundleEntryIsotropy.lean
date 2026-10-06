/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.EndpointRelativeBlockRow
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdjointMirrors
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAverageDrops
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCapsBundleRowIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMaximumEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakEnergyTail
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValue

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCapsBundleEntryIsotropy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Phase 1: the entry caps bundle at a parametrized normalizing block

the block-parametrization construction the corresponding argument applied to
`SmallContrastCapsBundleEntryIsotropy`.  Substitutions
S1, S2 and S4 on the two weak conjuncts; the two **row** conjuncts are repointed
to the split row caps through `caps_bundle_entry_rows_isotropy`.  The centering
conjuncts are untouched.

The row constant is `rowSplitConstant cIso (capsDeepConstant Cd g mAl G k0 s t)`:
a dimension-only head `2(1+cIso)(1-3^{-3/2})⁻¹` plus a deep leg carrying
`boundaryConst·3^{g((t+G)-s)}` **times** the discount
`3^{(3/2-g)((k0-1)-s)}`, which the gap `s - k0` drives below any tolerance at
rate `3/2 - g > 1/2`.  So the row's `Π` rides in a *scale threshold*, not in a
constant — the same disposal the printed argument prescribes and the corresponding argument prefix
machinery
already absorbs.

`hgeomT` and `g ≤ rho` disappear entirely: the elaborator's unused-variable
linter shows they fed **only** the weak caps' maximal envelope, which is now the
`henvMax` hypothesis.  `hgeomS` stays — that is the row channel's own geometry.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- The isotropy row value is monotone in the row constant. -/
theorem rowValue2Isotropy_mono {cRow cRow' kap eps : ℝ} (hkap : 0 ≤ kap)
    (h : cRow ≤ cRow') :
    rowValue2Isotropy d cRow kap eps ≤ rowValue2Isotropy d cRow' kap eps := by
  rw [rowValue2Isotropy, rowValue2Isotropy]
  refine mul_le_mul_of_nonneg_right h ?_
  have hd0 : (0 : ℝ) ≤ 36 * (1 + (d : ℝ)) * eps ^ 2 := by positivity
  exact mul_nonneg hkap hd0

/-- The split constant is monotone in its deep leg — which is how one `cRow`
serves every generation: the deep leg only shrinks as the window rises. -/
theorem rowSplitConstant_mono {cIso c c' : ℝ} (h : c ≤ c') :
    rowSplitConstant cIso c ≤ rowSplitConstant cIso c' := by
  rw [rowSplitConstant, rowSplitConstant]
  linarith only [h]

end

end HCPolySupport.HighContrast.Quenched
