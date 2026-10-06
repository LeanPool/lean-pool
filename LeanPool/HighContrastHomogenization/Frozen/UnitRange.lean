/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup

/-!
# High-contrast homogenization: Frozen.UnitRange

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Unit range of dependence

The local sigma-fields of two Borel sets at sup-distance at least one are
independent under the law.  The coefficient fields are uniformly elliptic almost
everywhere, with ellipticity constants belonging to the field and entering no
estimate; `e.qualitative.ellipticity` follows from this, and every
quantitative object of the development — `Π`, the gauge and its growth witness,
`Θ_m`, and every dimensional constant — is independent of them.
-/

/-- **Unit range of dependence.**  Local sigma-fields of unit-separated
Borel sets are independent. -/
@[expose]
def HCPoly.Frozen.IsUnitRangeLaw {d : ℕ}
    (P : MeasureTheory.Measure (HCPolySupport.HighContrast.CoeffSpace d)) : Prop :=
  ∀ U V : Set (HCPolySupport.Vec d), MeasurableSet U → MeasurableSet V →
    HCPolySupport.HighContrast.UnitSeparated U V →
      ProbabilityTheory.Indep (HCPolySupport.HighContrast.coeffSigma d U)
        (HCPolySupport.HighContrast.coeffSigma d V) P

/-! ## The assumption under the project namespace

`HCPolySupport.HighContrast.IsUnitRangeLaw` is `HCPoly.Frozen.IsUnitRangeLaw` itself, not a second
reading of it: the proofs of the paper's propositions are written in the project
namespace and use the frozen declaration through this name. -/
namespace HCPolySupport.HighContrast

export HCPoly.Frozen (IsUnitRangeLaw)

end HCPolySupport.HighContrast
