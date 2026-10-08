/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.FixedGridWindowAccount
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAbsorptionChoice
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdjointMirrors
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAlignedGeometry
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAnnealedEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAverageDrops
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryCapsIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntrySupply
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionStep
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHvarFamily
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastIsotropyPack
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastLoadScalePiFree
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMeanDropCarrier
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastOneStepHub
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRealClauses
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowAtCenters
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSingleCellVariance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastTerminalComparability
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceLagged
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValue
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjointAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridCells
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowOscillationSum
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSchur
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSkewCarriers

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastHoneAtIsotropy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The family's output *is* the fused core's `hone` slot

The last joint between's two halves, and it is free.

`exists_one_step_family_at_isotropy_var_at_level_conv_family_min` reports each generation's step
with the
excess written `hatExcessAt P q ((N₀ : ℤ) + (n : ℤ))`;
the isotropic account core body's `hone` binder writes the same quantity
expanded, as `(d : ℝ) * (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)`.
Those are the two sides of `hatExcessAt`'s definition
(`HCPoly.Provider.Quenched.SmallContrastSmallnessPack`), so the joint is definitional.

`hone_of_one_step_family_isotropy` below checks it: **its proof is `h`**, so
its type-checking is the verification.  With it, the endpoint's
`hone` slot is filled by the family with no conversion layer at all — the
generation-step conversion is gone entirely.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-- **The joint.**  The one-step family's report, at the isotropy row carrier, is
the fused core's `hone` hypothesis on the nose. -/
theorem hone_of_one_step_family_isotropy {d : ℕ} {Cpre eta : ℝ} {H : ℕ}
    {P : Measure (CoeffSpace d)} {q : Mat d} {N₀ ns : ℕ}
    {cRow kap : ℝ} {wv : ℕ → ℝ}
    (h : ∀ n : ℕ, ns ≤ n →
      adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
        4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
              (16 * (d : ℝ) *
                (adaptedHattedContrast P q ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                  adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)))) +
            rowValue2Isotropy d cRow kap
              (hatExcessAt P q ((N₀ : ℤ) + (n : ℤ))) + wv n) +
          2 * ((3 * (d : ℝ) + 4) *
            hatExcessAt P q ((N₀ : ℤ) + (n : ℤ)) ^ 2)) :
    ∀ n : ℕ, ns ≤ n →
      adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
        4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
              (16 * (d : ℝ) *
                (adaptedHattedContrast P q ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                  adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)))) +
            rowValue2Isotropy d cRow kap
                ((d : ℝ) *
                (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) + wv n) +
          2 * ((3 * (d : ℝ) + 4) *
            ((d : ℝ) *
              (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) ^ 2) := h

end

end HCPolySupport.HighContrast.Quenched
