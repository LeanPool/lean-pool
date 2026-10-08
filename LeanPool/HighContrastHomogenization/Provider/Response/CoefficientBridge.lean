/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DomainBridge
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedResponseSubadditivity
public import LeanPool.HighContrastHomogenization.Setup.Moments

/-!
# High-contrast homogenization: Provider.Response.CoefficientBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coefficient of a sample on an adapted cell

The variational layer of Armstrong–Kuusi Chapter 2 reads a coefficient field through the
domain-local interface `Book.Ch02.CoeffOn U`: a representative together with a
pair of ellipticity constants valid almost everywhere on `U`.  The high-contrast
paper instead carries a sample `a` of the coefficient law, an almost everywhere
class, and reads its coarse block response `𝐀(U; a)`, the variational coarse
block of `s.introduction`, through the variational block matrix of the class.
This file connects the two.

The connection is uniform in the domain, and that is what makes it usable on a
subdivision.  A sample has a measurable representative that is elliptic at
*every* point, and such a field is a Chapter 2 coefficient on every domain at
once, with the same representative and the same constants; so the parent cell
`U_t = q□_t` and all of its aligned children `U_k(z) = z + q□_k` may be equipped
simultaneously, each child coefficient being literally the restriction of the
parent one.  On each of them the Chapter 2 coarse block matrix is the paper's
own coarse block response: for the aligned cells this is the adapted response
`A_k(z) = 𝐀(U_k(z); a)` of the child cell.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open MeasureTheory

noncomputable section

variable {d : ℕ} {q : Mat d}

/-! ## A pointwise elliptic field is a coefficient on every domain -/

/-- A measurable field that is elliptic at every point of a domain is a Chapter 2
coefficient on that domain, with its own representative and its own constants
unchanged. -/
theorem exists_coeffOn_of_measurable {f : CoeffField d} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (hfm : Measurable f)
    (U : Book.Ch02.Domain d)
    (hell : ∀ x ∈ (U : Set (Vec d)), IsEllipticMatrix lam Lam (f x)) :
    ∃ b : Book.Ch02.CoeffOn U,
      b.toCoeffField = f ∧ b.lam = lam ∧ b.Lam = Lam ∧
        IsEllipticFieldOn lam Lam (U : Set (Vec d)) f := by
  classical
  have hmem : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), x ∈ (U : Set (Vec d)) := by
    simpa only [volumeMeasureOn] using
      MeasureTheory.ae_restrict_mem U.measurableSet
  refine
    ⟨{ toCoeffField := f
       lam := lam
       Lam := Lam
       lam_pos := hlam
       lam_le_Lam := hle
       aeStronglyMeasurable := ?_
       aeElliptic := by filter_upwards [hmem] with x hx using hell x hx },
      rfl, rfl, rfl,
      Recurrence.isEllipticFieldOn_of_measurable hfm hell U.measurableSet⟩
  intro i j
  refine Measurable.aestronglyMeasurable ?_
  have h : (fun x : Vec d => restrictCoeffField (U : Set (Vec d)) f x i j)
      = fun x => if x ∈ (U : Set (Vec d)) then f x i j else 0 := by
    funext x
    by_cases hx : x ∈ (U : Set (Vec d)) <;> simp [restrictCoeffField, hx]
  rw [h]
  exact Measurable.ite U.measurableSet
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hfm)) measurable_const

/-! ## The representative of a sample -/

/-- A sample of the coefficient law has a measurable representative, elliptic at
every point of a prescribed bounded set, that computes the coarse block response
of the sample on every set. -/
theorem exists_representative (a : CoeffSpace d) {S : Set (Vec d)}
    (hS : Bornology.IsBounded S) :
    ∃ (f : CoeffField d) (lam Lam : ℝ), 0 < lam ∧ lam ≤ Lam ∧ Measurable f ∧
      (∀ x ∈ S, IsEllipticMatrix lam Lam (f x)) ∧
      ∀ U : Set (Vec d), coarseBlock U a = coarseBlockMatrix U f := by
  obtain ⟨lam, Lam, f, hlam, hle, hfm, hell, hae⟩ :=
    exists_pointwise_elliptic_representative a.2 hS
  exact ⟨f, lam, Lam, hlam, hle, hfm, hell, fun U => coarseBlock_eq_of_ae_eq a hae⟩

/-! ## The Chapter 2 coarse block matrix is the coarse block response -/

/-- On a domain carrying an elliptic representative, the public Chapter 2 coarse
block matrix `𝐀(U; a)` agrees with the variational coarse block matrix of the
representative. -/
theorem coarseBlockMatrix_eq_of_isEllipticFieldOn [NeZero d] (U : Book.Ch02.Domain d)
    (b : Book.Ch02.CoeffOn U)
    (hEll : IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField) :
    Book.Ch02.coarseBlockMatrix U b =
      coarseBlockMatrix (U : Set (Vec d)) b.toCoeffField := by
  have hvol : 0 < (volume (U : Set (Vec d))).toReal :=
    Internal.Ch02.BookCh02.domain_volume_pos U
  obtain ⟨R, _sigma0, compat, hA, _hSInv, hS, hK, hSigma, _hCanon⟩ :=
    Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
      (U := (U : Set (Vec d))) U.isDomain hEll hvol
  have hdet : IsUnit (sigmaStarCoarse (U : Set (Vec d)) b.toCoeffField).det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := (U : Set (Vec d))) (a := b.toCoeffField) R U.isDomain hEll hvol compat hS
  exact Internal.Ch02.BookCh02.book_coarseBlockMatrix_eq_old_coarseBlockMatrix_of_data
    U b hA hS hK hSigma hdet

/-! ## The bridge on the adapted cells -/

end

end Response
end HighContrast
end HCPolySupport
