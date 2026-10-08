/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup

/-!
# High-contrast homogenization: Frozen.Stationarity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Stationarity of the coefficient law

The law of the coefficient field is invariant under the integer translations of
the coefficient space.  The coefficient fields are uniformly elliptic almost
everywhere, with ellipticity constants belonging to the field and entering no
estimate; `e.qualitative.ellipticity` follows from this, and every
quantitative object of the development — `Π`, the gauge and its growth witness,
`Θ_m`, and every dimensional constant — is independent of them.
-/

/-- **Stationarity of the coefficient law.**  Every integer translation of the
coefficient space preserves the law. -/
@[expose]
def HCPoly.Frozen.IsStationaryLaw {d : ℕ}
    (P : MeasureTheory.Measure (HCPolySupport.HighContrast.CoeffSpace d)) : Prop :=
  ∀ z : Fin d → ℤ,
    MeasureTheory.Measure.map (HCPolySupport.HighContrast.translateCoeff z) P = P

/-! ## The assumption under the project namespace

`HCPolySupport.HighContrast.IsStationaryLaw` is `HCPoly.Frozen.IsStationaryLaw` itself, not a second
reading of it: the proofs of the paper's propositions are written in the project
namespace and use the frozen declaration through this name. -/
namespace HCPolySupport.HighContrast

export HCPoly.Frozen (IsStationaryLaw)

end HCPolySupport.HighContrast
