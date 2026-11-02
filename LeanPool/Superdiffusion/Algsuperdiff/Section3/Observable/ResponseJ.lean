/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.Comparator
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.Expectations

/-!
# ResponseJ

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Section 3 normalized response observable

This file defines the genuine scalar response observable on the centered cube
`square_m`.  For a positive comparator `sigma` and a direction `e`, its loads
are exactly `sigma^(-1/2) e` and `sigma^(1/2) e`.  The coefficient argument is
an actual CoarseGraining `RegCoeffField`; later cutoff-specific declarations
merely compose this map with the genuine cutoff field.

## References

* ABK26, (2.4), definition of `J(U,p,q;a)`.
* ABK26, Section 2.5 and Section 3 response normalizations.
-/

namespace Algsuperdiff.Section3.Observable

open HCPolySupport HCPolySupport.Book.Ch04 MeasureTheory

noncomputable section

/-- The response observable
`a ↦ J(square_m, sigma^(-1/2)e, sigma^(1/2)e; a)`. -/
noncomputable def responseJAtScale {d : ℕ} (m : ℤ)
    (sigma : PositiveScalar) (e : Vec d) : RegCoeffField d → ℝ :=
  restrictionResponseJObservableCubeSet (originCube d m)
    (inverseSqrtLoad sigma e) (sqrtLoad sigma e)

/-- The normalized scalar response is pointwise nonnegative. -/
theorem responseJAtScale_nonneg {d : ℕ} (m : ℤ)
    (sigma : PositiveScalar) (e : Vec d) (a : RegCoeffField d) :
    0 ≤ responseJAtScale m sigma e a :=
  restrictionResponseJObservableCubeSet_nonneg (originCube d m)
    (inverseSqrtLoad sigma e) (sqrtLoad sigma e) a

end

end Algsuperdiff.Section3.Observable
