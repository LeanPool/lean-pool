/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup

/-!
# High-contrast homogenization: Consistency.WitnessField

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The constant identity coefficient field as a point of `CoeffSpace`

This module checks the definition `CoeffSpace` of the coefficient space of
`s.introduction` at its reference point `constIdentity`, through the field
`identityField` and the translation `translateCoeff` that the point must respect.

Were the check to fail, the coefficient space would lose its exhibited point:
the class `CoeffSpace d` would be empty, the Dirac witness law of
`HCPoly.Annealed.Witness` could not be formed, and the hypothesis set of
`t.polynomial.entry` — a probability law that is stationary, of unit range and
coarsely elliptic — would be left without a model and its conclusion vacuous.  A
failure of `translateCoeff_constIdentity` would put the witness law outside the
translation-invariant class `s.introduction` prints, and a failure of
`coeFn_identityField` would make the field, as an a.e. class, something other
than the identity matrix.

This module is a consistency check of that definition and is not a result of the
paper.

The reference point of the coefficient space of `s.introduction`: the
field whose value is the identity matrix almost everywhere.  It is uniformly
elliptic with both ellipticity constants equal to one, and it is fixed by every
integer translation of the coefficient space.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The constant identity coefficient field, as a point of the a.e.-quotient
carrier of coefficient fields. -/
@[expose]
def identityField (d : ℕ) : Source.AKL.Field d :=
  AEEqFun.const (Vec d) (1 : Mat d)

theorem coeFn_identityField :
    (⇑(identityField d) : Vec d → Mat d) =ᵐ[volume] fun _ => (1 : Mat d) :=
  AEEqFun.coeFn_const _ _

/-- The identity matrix acts as the identity on vectors. -/
theorem matVecMul_identity (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- The identity matrix is uniformly elliptic with both constants equal to
one. -/
theorem isEllipticMatrix_identity : IsEllipticMatrix (1 : ℝ) 1 (1 : Mat d) := by
  have hinv : (1 : Mat d)⁻¹ = 1 := by simp
  refine ⟨one_pos, le_rfl, fun ξ => ?_, fun ξ => ?_⟩
  · rw [matVecMul_identity, one_mul]
    exact le_rfl
  · rw [hinv, matVecMul_identity, inv_one, one_mul]
    exact le_rfl

theorem aeUniformlyEllipticField_identityField :
    AEUniformlyEllipticField (identityField d) := by
  refine aeUniformlyEllipticField_of_ae_isEllipticMatrix one_pos le_rfl ?_
  filter_upwards [coeFn_identityField (d := d)] with x hx
  rw [hx]
  exact isEllipticMatrix_identity

/-- The constant identity field as a point of the coefficient space. -/
@[expose]
def constIdentity (d : ℕ) : CoeffSpace d :=
  ⟨identityField d, aeUniformlyEllipticField_identityField⟩

theorem coeFn_constIdentity :
    (⇑(constIdentity d).1 : Vec d → Mat d) =ᵐ[volume] fun _ => (1 : Mat d) :=
  coeFn_identityField

/-- The constant identity field is fixed by every integer translation. -/
theorem translateField_identityField (z : Fin d → ℤ) :
    Source.AKL.translateField z (identityField d) = identityField d := by
  refine AEEqFun.ext_iff.mpr ?_
  have hshift := (measurePreserving_add_right (volume : Measure (Vec d))
        (Source.AKL.intTranslation z)).quasiMeasurePreserving.tendsto_ae
      (coeFn_identityField (d := d))
  filter_upwards [Source.AKL.translateField_ae z (identityField d), hshift,
    coeFn_identityField (d := d)] with x hx hshiftx hidx
  have hshiftx' : (identityField d) (x + Source.AKL.intTranslation z) = (1 : Mat d) := hshiftx
  rw [hx, hshiftx', hidx]

theorem translateCoeff_constIdentity (z : Fin d → ℤ) :
    translateCoeff z (constIdentity d) = constIdentity d :=
  Subtype.ext (translateField_identityField z)

end

end HighContrast
end HCPolySupport
