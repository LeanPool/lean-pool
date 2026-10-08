/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedAffineResponse

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.NormalizedResponseCell

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Exact doubled-response normalization on adapted cells

The constant-skew, scalar, and exact affine covariance formulas compose with
their distinct transformed primal and dual loads on every aligned cell.
-/

namespace HCPolySupport
namespace HighContrast

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- The exact skew, scalar, and affine normalizations compose with all loads
transformed. -/
theorem doubledResponseJ_normalizedReferenceCell [NeZero d]
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (t k : ℤ) (w : Fin d → ℤ) (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
    (P Q : BlockVec d) :
    Book.Ch02.doubledResponseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        (aRef.coeffOn (translateCube w (originCube d k)))
        (normalizedReferencePrimalLoad abar P)
        (normalizedReferenceDualLoad abar Q) =
      Book.Ch02.doubledResponseJ
        (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hS) k w)
        (a.coeffOn
          (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hS) k w)) P Q := by
  let S := symmPart abar
  let g := skewPart abar
  let c := specBound S⁻¹
  let alpha := Real.sqrt c
  let q := Selection.normalizedRoot S
  have hc : 0 < c := by simpa only [c, S] using normalizedRootScale_pos hS
  have hq : q.PosDef := by
    simpa only [q, S] using normalizedRoot_posDef_of_posDef hS
  change Book.Ch02.doubledResponseJ _ _
      (affineReferencePrimalLoad q
        (scalarNormalizedPrimalLoad alpha (skewCenteredPrimalLoad g P)))
      (affineReferenceDualLoad q
        (scalarNormalizedDualLoad alpha (skewCenteredDualLoad g Q))) = _
  rw [doubledResponseJ_affineResponseCell hq t k w
    (normalizedCenteredCoeff a abar hS) aRef]
  · calc
      Book.Ch02.doubledResponseJ (Response.adaptedDomainAt hq k w)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomainAt hq k w))
          (scalarNormalizedPrimalLoad alpha (skewCenteredPrimalLoad g P))
          (scalarNormalizedDualLoad alpha (skewCenteredDualLoad g Q)) =
        Book.Ch02.doubledResponseJ (Response.adaptedDomainAt hq k w)
          ((a.subSkew g (matTranspose_skewPart abar)).coeffOn
            (Response.adaptedDomainAt hq k w))
          (skewCenteredPrimalLoad g P) (skewCenteredDualLoad g Q) := by
            simpa only [normalizedCenteredCoeff, c, S, g, alpha] using
              doubledResponseJ_positiveScale c hc
                (a.subSkew g (matTranspose_skewPart abar))
                (Response.adaptedDomainAt hq k w)
                (skewCenteredPrimalLoad g P) (skewCenteredDualLoad g Q)
      _ = Book.Ch02.doubledResponseJ (Response.adaptedDomainAt hq k w)
          (a.coeffOn (Response.adaptedDomainAt hq k w)) P Q :=
        doubledResponseJ_subSkew a g (matTranspose_skewPart abar) P Q
  · simpa only [q, S] using haRef

end

end HighContrast
end HCPolySupport
