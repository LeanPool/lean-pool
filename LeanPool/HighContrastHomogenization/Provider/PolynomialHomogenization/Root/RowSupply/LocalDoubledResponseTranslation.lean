/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.DescendantCoefficientRestriction
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DeterministicIdentities
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Translation
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Translation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.LocalDoubledResponseTranslation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local translation covariance for doubled responses

The public coefficient carrier is defined only almost everywhere.  This file
packages translation covariance without selecting pointwise representatives:
the coefficient on the translated cube and the translated coefficient on the
base cube need only agree almost everywhere with a common physical field.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

@[expose]
public noncomputable def replaceCoeffOn
    {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (f : CoeffField d)
    (h : f =ᵐ[volumeMeasureOn (U : Set (Vec d))] a.toCoeffField) :
    Book.Ch02.CoeffOn U where
  toCoeffField := f
  lam := a.lam
  Lam := a.Lam
  lam_pos := a.lam_pos
  lam_le_Lam := a.lam_le_Lam
  aeStronglyMeasurable := by
    intro i j
    refine (a.aeStronglyMeasurable i j).congr ?_
    filter_upwards [h] with x hx
    by_cases hxU : x ∈ (U : Set (Vec d))
    · simp [restrictCoeffField, hxU, hx]
    · simp [restrictCoeffField, hxU]
  aeElliptic := by
    filter_upwards [h, a.aeElliptic] with x hx hEll
    simpa only [hx] using hEll

private theorem replaceCoeffOn_aeeq
    {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (f : CoeffField d)
    (h : f =ᵐ[volumeMeasureOn (U : Set (Vec d))] a.toCoeffField) :
    Book.Ch02.CoeffOn.AEEq (replaceCoeffOn a f h) a :=
  h

private theorem responseJ_translate_of_aeeq
    {U V : Book.Ch02.Domain d} (z : Vec d)
    (hset : (U : Set (Vec d)) = translateSet z (V : Set (Vec d)))
    (aU : Book.Ch02.CoeffOn U) (aV : Book.Ch02.CoeffOn V)
    (hcoeff : translateCoeffField z aU.toCoeffField
      =ᵐ[ volumeMeasureOn (V : Set (Vec d))] aV.toCoeffField)
    (p q : Vec d) :
    Book.Ch02.responseJ U aU p q = Book.Ch02.responseJ V aV p q := by
  let bV : Book.Ch02.CoeffOn V :=
    replaceCoeffOn aV (translateCoeffField z aU.toCoeffField) hcoeff
  calc
    Book.Ch02.responseJ U aU p q =
        ResponseJ (U : Set (Vec d)) p q aU.toCoeffField :=
      HCPolySupport.Internal.Ch02.book_responseJ_eq_ResponseJ U aU p q
    _ = ResponseJ (translateSet z (V : Set (Vec d))) p q aU.toCoeffField := by
      rw [← hset]
    _ = ResponseJ (V : Set (Vec d)) p q
        (translateCoeffField z aU.toCoeffField) :=
      ResponseJ_translateSet_eq_translateCoeffField z (V : Set (Vec d)) p q
        aU.toCoeffField
    _ = Book.Ch02.responseJ V bV p q := by
      exact (HCPolySupport.Internal.Ch02.book_responseJ_eq_ResponseJ V bV p q).symm
    _ = Book.Ch02.responseJ V aV p q :=
      Book.Ch02.responseJ_eq_ofAEEq (replaceCoeffOn_aeeq aV _ hcoeff) p q

/-- The doubled response is translation covariant under local a.e.
identification of the translated coefficient field. -/
theorem doubledResponseJ_translate_of_aeeq
    {U V : Book.Ch02.Domain d} (z : Vec d)
    (hset : (U : Set (Vec d)) = translateSet z (V : Set (Vec d)))
    (aU : Book.Ch02.CoeffOn U) (aV : Book.Ch02.CoeffOn V)
    (hcoeff : translateCoeffField z aU.toCoeffField
      =ᵐ[ volumeMeasureOn (V : Set (Vec d))] aV.toCoeffField)
    (P Q : BlockVec d) :
    Book.Ch02.doubledResponseJ U aU P Q =
      Book.Ch02.doubledResponseJ V aV P Q := by
  rcases P with ⟨p, q⟩
  rcases Q with ⟨qStar, pStar⟩
  rw [Book.Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum,
    Book.Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum]
  have hmain := responseJ_translate_of_aeeq z hset aU aV hcoeff
  have hadjoint := responseJ_translate_of_aeeq z hset aU.transpose aV.transpose
    (hcoeff.mono fun x hx => by
      exact congrArg matTranspose hx)
  rw [hmain, hadjoint]

end

end RowSupply
end HighContrast
end HCPolySupport
