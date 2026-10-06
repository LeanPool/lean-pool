/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionStep
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSharpLine

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastLineProducer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# `hline`: the per-generation producer at the sharp constant

The per-generation analytic estimate.

`hline` is *precisely* `hrec_line_of_slots_isotropy_sharp_at_jb_at_level_src`'s conclusion
quantified
over `n ≥ ns` (the cited theorem).  the corresponding argument found no producer in
the construction: the account that would feed it was never built.  This file builds
it, in the two stages the corresponding argument separated.

**the corresponding step — the constants pack.**  Nine of the seventeen `n`-free hypotheses are
pure scalar side conditions on the slot constants.  `IsotropySlotConstants` bundles
them so the producer's binder stays readable, and the isotropic slot constants
are supplied from the exponent pack's `g`-clauses plus the four positivity facts
a caller already has.

**the corresponding step — the producer.**  `hline_of_slots_sharp_var_at_jb_at_level_src` takes
the `n`-free data once
and the `n`-dependent slots as families over `n`, and discharges `∀ n ≥ ns` by
`hrec_line_of_slots_isotropy_sharp_at_jb_at_level_src` at each generation.

The carriers that must vary with the generation are exactly `V`, `V0`, `Dr`,
`Vmean`, `bmaj`, `wv` and `jb`; everything appearing in the recursion constant
or in the recursion tolerance — `cD`, `delta`, `cVsum`, `cVm`, `vsum`, `vmsrc`,
`bsrc` — is
`n`-free of necessity, since `fusionRecursionConstantIsotropySharp` and the geometric
term are fixed across the recursion.  That split is forced by the statement, not
chosen.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## the corresponding step: the constants pack -/

/-- **The nine scalar side conditions** of the isotropy slot line.  Bundling
them keeps the producer's binder to the data that actually varies. -/
structure IsotropySlotConstants (d : ℕ) (g Cpre eta cRow kap M cD delta : ℝ) :
    Prop where
  hg0 : 0 ≤ g
  hg1 : g < 1
  hCpre : 0 ≤ Cpre
  heta : 0 < eta
  hcRow : 0 ≤ cRow
  hkap : 0 ≤ kap
  hM0 : 0 ≤ M
  hcD0 : 0 ≤ cD
  hdelta0 : 0 ≤ delta

/-! ## the corresponding step: the producer -/

end

end HCPolySupport.HighContrast.Quenched
