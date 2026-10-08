/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedSymmetricReferenceEllipticity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions

/-!
# High-contrast homogenization: Provider.Regularity.RoundedReferenceConstantMatrix

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant-matrix package for the rounded reference

The rounded coordinate change produces a constant symmetric reference that is
near, but not equal, to the identity.  This module packages that reference in
the Chapter 3 constant-coefficient carrier with the source's explicit
ellipticity constants.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- The matrix value of the constant rounded symmetric reference. -/
@[expose]
def roundedReferenceMatrix
    (abar : Mat d) (hS : (symmPart abar).PosDef) : Mat d :=
  roundedSymmetricReferenceCoefficient abar hS 0

/-- The rounded symmetric reference field is constant with the selected
matrix value. -/
theorem roundedSymmetricReferenceCoefficient_apply_eq_roundedReferenceMatrix
    (abar : Mat d) (hS : (symmPart abar).PosDef) (y : Vec d) :
    roundedSymmetricReferenceCoefficient abar hS y =
      roundedReferenceMatrix abar hS := by
  rfl

/-- The selected rounded reference matrix is positive definite. -/
theorem roundedReferenceMatrix_posDef [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    (roundedReferenceMatrix abar hS).PosDef := by
  simpa only [roundedReferenceMatrix] using
    roundedSymmetricReferenceCoefficient_posDef abar hS (0 : Vec d)

/-- The selected rounded reference matrix has the exact near-identity
ellipticity constants used by the regularity black box. -/
theorem isEllipticMatrix_roundedReferenceMatrix [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    IsEllipticMatrix (99 / 100 : ℝ) (101 / 100 : ℝ)
      (roundedReferenceMatrix abar hS) := by
  simpa only [roundedReferenceMatrix] using
    isEllipticMatrix_roundedSymmetricReferenceCoefficient
      abar hS (0 : Vec d)

/-- The genuinely rounded comparison matrix in the Chapter 3
constant-coefficient carrier. -/
@[expose]
def roundedReferenceConstantCoeffMatrix [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    Book.Ch03.ConstantCoeffMatrix d where
  matrix := roundedReferenceMatrix abar hS
  isSymm := isSymm_of_isHermitian
    (roundedReferenceMatrix_posDef abar hS).isHermitian
  lam := 99 / 100
  Lam := 101 / 100
  lam_pos := by norm_num
  lam_le_Lam := by norm_num
  elliptic := isEllipticMatrix_roundedReferenceMatrix abar hS

@[simp] theorem roundedReferenceConstantCoeffMatrix_matrix [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    (roundedReferenceConstantCoeffMatrix abar hS).matrix =
      roundedReferenceMatrix abar hS :=
  rfl

/-- The Chapter 3 constant field is exactly the rounded symmetric reference,
not the scalar identity field. -/
theorem constantCoeffField_roundedReferenceConstantCoeffMatrix [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    constantCoeffField (roundedReferenceConstantCoeffMatrix abar hS).matrix =
      roundedSymmetricReferenceCoefficient abar hS := by
  funext y
  exact
    (roundedSymmetricReferenceCoefficient_apply_eq_roundedReferenceMatrix
      abar hS y).symm

end

end HighContrast
end HCPolySupport
