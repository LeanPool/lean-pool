/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicAnchoredObservationToPhysicalFluxRate

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.UniformFluxScheduledRateExtraction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scheduled-rate extraction from the squared flux row

The squared Whitney-row rate is converted to the terminal one-half power.  All
finite deterministic factors are retained in one explicit real constant.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- CapObs-free terminal rate on the module-50 response-window witness. -/
@[expose]
def RowConvertedFluxScheduledRateAtWitness
    (d : ℕ) (C₀ : ℝ → ℝ → ℝ → ℝ)
    (_g kappaRate Cdual : ℝ)
    (capFlux hardyConstant boundaryEnergy : ℝ≥0∞)
    (s rho Rad epsilon Xval outputFactor : ℝ) : Prop :=
  capFlux ≠ ⊤ ∧
    ENNReal.ofReal outputFactor *
        (ENNReal.ofReal Cdual *
          ruledScheduledTwoRowCap d hardyConstant capFlux) ≤
      ENNReal.ofReal (C₀ s rho Rad * (epsilon * Xval) ^ kappaRate) *
        boundaryEnergy ^ (1 / 2 : ℝ)

end

end RowSupply
end HighContrast
end HCPolySupport
