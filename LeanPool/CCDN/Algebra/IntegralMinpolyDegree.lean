/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-! Degree bounds for integral elements: over an integrally closed base ring, the minimal
polynomial of an integral element has degree at most the degree of the fraction-field
extension. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- Let `R` be an integrally closed domain with fraction field `F`, and let `E` be a finite
extension of `F` receiving compatible maps from `R`, `A` and `F`. The minimal polynomial over
`R` of an integral element `a` of the domain `A` has degree at most `[E : F]`. -/
theorem integral_minpoly_natDegree_le_fraction_finrank
    (R A F E : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Field F] [Field E]
    [Algebra R A] [Algebra R F] [IsFractionRing R F]
    [Algebra R E] [Algebra A E] [Algebra F E]
    [IsScalarTower R A E] [IsScalarTower R F E]
    [FiniteDimensional F E] (a : A) (ha : IsIntegral R a) :
    (minpoly R a).natDegree ≤ Module.finrank F E := by
  rw [← (minpoly.monic ha).natDegree_map (algebraMap R F),
    ← minpoly.isIntegrallyClosed_eq_field_fractions F E ha]
  exact minpoly.natDegree_le (algebraMap A E a)

end
end CCDN
