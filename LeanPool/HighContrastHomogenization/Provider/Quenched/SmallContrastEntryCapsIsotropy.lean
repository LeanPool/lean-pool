/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCapsBundleEntryIsotropy

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastEntryCapsIsotropy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Phase 1: the account entry caps at a parametrized normalizing block

the block-parametrization construction the corresponding argument applied to
`SmallContrastEntryCapsIsotropy`.  The mean-drop carrier
gets a parallel definition over the block and the envelope scalar; the established
`blockSize_meanDrop_le` it is built from is **already** fully parametric in both
(the cited theorem), so the substitution is exact.

The terminal envelope, which the established proof derived from the Dagger at the
inflated scalar, becomes the hypothesis `henvF`, and the **comparability
constant** — pinned to `kap2Value` in the established proof — becomes the parameter
`kapE`.  That last one is not cosmetic: `kapE` multiplies into the *load*
`loadScaleOfScalar cF kapE`, which feeds `L`, hence `A`, hence `alpha`.  Recipe
the corresponding argument exemption of `kap2Value` as a "supply value" holds only where it
multiplies the excess; in the load slot it is load-bearing, exactly as the corresponding argument
closing note warned ("the corresponding clause are load-bearing, not cosmetic") — the same
factoring as
everywhere else on this wave.

`meanDrop2ValueIsotropy` carries **no** `rfl` hinge back to the unparametrized
mean-drop value: the two bodies agree syntactically, but deciding that requires
unfolding the inflated reference inside `blockSize`, which is prohibitively
expensive.  The
identification is not needed — nothing consumes it, and the established carrier is
untouched, so the wave stays additive without it.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- **The entry mean-drop carrier at a parametrized normalizer.** -/
@[expose]
def meanDrop2ValueIsotropy (P : Measure (CoeffSpace d)) (lAl : ℤ) (cF : ℝ)
    (mAl : Mat d) (E F : BlockMat d) (t : ℤ) (j : ℕ) : ℝ :=
  4 * (d : ℝ) *
    (adaptedHattedContrast P (roundedGrid lAl mAl) (t - (j : ℤ)) -
      adaptedHattedContrast P (roundedGrid lAl mAl) t) *
    cF * blockSize E F

end

end HCPolySupport.HighContrast.Quenched
