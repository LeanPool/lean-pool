/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.ExactRootGaugeTerminalDefinition

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.CertificatePositiveDefiniteness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# What the reconciled-smallness certificate hands the deterministic holes

Two of the three premises of the C¹ slope approximation at the exact-gauge
terminal are discharged from the certificate itself; only the exact-gauge
terminal remains.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- The `c`-parameterised certificate carries the positive-definiteness of the
homogenized symmetric part, exactly as `RootInterface.RootGoodScale` does. -/
theorem rootGoodScaleAt_posDef [NeZero d] {g c kappaRate : ℝ} {abar : Mat d}
    {a : CoeffSpace d} {x : ℝ}
    (h : rootGoodScaleAt d g c kappaRate abar a x) :
    (symmPart abar).PosDef := by
  obtain ⟨hh, -, -⟩ := h
  obtain ⟨amp, Xc, hcert, -⟩ := hh.good
  obtain ⟨hS, -⟩ := hcert
  exact hS

end

end CorrectorComposition
end HighContrast
end HCPolySupport
