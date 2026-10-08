/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.EpsilonAffineCoefficientRealization
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedAffineResponse
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedNormalizedRootDoubledResponseSubadditivity
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyRows

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.EpsilonAffineDoubledResponseRealization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Exact doubled-response realization on a translated observation cube

The observation coefficient is identified locally with the microscopic
affine pullback.  Affine, scalar, skew, and translation covariance then give
an exact physical response on the corresponding translated adapted cell.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped Matrix

noncomputable section

variable {d : ℕ}

theorem translateSet_adaptedCellAt_eq_translate
    (z : Vec d) (q : Mat d) (k : ℤ) (w : Fin d → ℤ) :
    translateSet z (adaptedCellAt q k w) =
      adaptedCellTranslate q k (z + adaptedCellCenter q k w) := by
  ext x
  simp only [translateSet, adaptedCellAt_eq_adaptedCellTranslate,
    adaptedCellTranslate, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, by abel⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨adaptedCellCenter q k w + v, ⟨v, hv, rfl⟩, by abel⟩

/-- Exact realization of a locally identified observation response as the
physical response on the microscopic affine image of the cube. -/
theorem doubledResponseJ_observation_epsilonAffine_eq
    [NeZero d] {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (center : Vec d) (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (k : ℤ) (w : Fin d → ℤ)
    (aObs : Book.Ch02.CoeffOn
      (Book.Ch02.cubeDomain (translateCube w (originCube d k))))
    (hObs : aObs.toCoeffField =ᵐ[volumeMeasureOn
        (openCubeSet (translateCube w (originCube d k)))]
      fun x ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun y ↦ scaledCoeff epsilon a y - skewPart abar) (x + center))
    (P Q : BlockVec d) :
    Book.Ch02.doubledResponseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k))) aObs
        (normalizedReferencePrimalLoad abar P)
        (normalizedReferenceDualLoad abar Q) =
      Transport.coeffSpaceDoubledResponse
        (adaptedCellTranslate (epsilonAffineGrid epsilon abar) k
          (epsilon⁻¹ • matVecMul (matSqrt (symmPart abar)) center +
            adaptedCellCenter (epsilonAffineGrid epsilon abar) k w))
        a P Q := by
  let q := epsilonAffineGrid epsilon abar
  let z := epsilon⁻¹ • matVecMul (matSqrt (symmPart abar)) center
  let c := epsilonCoefficientScale epsilon
  let aTrans := realTranslateCoeff z a
  let aSkew := aTrans.subSkew (skewPart abar) (matTranspose_skewPart abar)
  let aMicro := epsilonAffinePhysicalCoeff epsilon hepsilon center a abar
  have hq : q.PosDef := by
    simpa only [q] using epsilonAffineGrid_posDef hepsilon hS
  obtain ⟨aRef, haRef⟩ := exists_adaptedReferenceCoeffFamily hq 0 aMicro
  let R := translateCube w (originCube d k)
  let U := Response.adaptedDomainAt hq k w
  have hreal := affineCoefficient_epsilonAffinePhysicalCoeff_ae
    hepsilon center a abar hS
  have hrealLocal :
      (fun x ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun y ↦ scaledCoeff epsilon a y - skewPart abar) (x + center)) =ᵐ[
          volumeMeasureOn (openCubeSet R)]
        affineCoefficient q
          ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
          (⇑aMicro.1 : CoeffField d) := by
    simpa only [q, aMicro] using! ae_restrict_of_ae hreal.symm
  have haRefLocal :
      affineCoefficient q
          ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
          (⇑aMicro.1 : CoeffField d) =ᵐ[
        volumeMeasureOn (openCubeSet R)]
          (aRef.coeffOn R).toCoeffField :=
    _root_.Filter.Eventually.of_forall fun x ↦ congrFun (haRef R).symm x
  have hObsRef : Book.Ch02.CoeffOn.AEEq aObs (aRef.coeffOn R) := by
    exact hObs.trans (hrealLocal.trans haRefLocal)
  let P0 := scalarNormalizedPrimalLoad (Real.sqrt c)
    (skewCenteredPrimalLoad (skewPart abar) P)
  let Q0 := scalarNormalizedDualLoad (Real.sqrt c)
    (skewCenteredDualLoad (skewPart abar) Q)
  have hP0 : affineReferencePrimalLoad q P0 =
      normalizedReferencePrimalLoad abar P := by
    simpa only [q, c, P0] using
      affine_scalar_skew_primalLoad_epsilon_eq_normalizedReference
        hepsilon abar hS P
  have hQ0 : affineReferenceDualLoad q Q0 =
      normalizedReferenceDualLoad abar Q := by
    simpa only [q, c, Q0] using
      affine_scalar_skew_dualLoad_epsilon_eq_normalizedReference
        hepsilon abar hS Q
  have hcov := doubledResponseJ_affineResponseCell hq 0 k w
    aMicro aRef haRef P0 Q0
  have hscale := doubledResponseJ_positiveScale c
    (epsilonCoefficientScale_pos hepsilon) aSkew U
      (skewCenteredPrimalLoad (skewPart abar) P)
      (skewCenteredDualLoad (skewPart abar) Q)
  have hskew := doubledResponseJ_subSkew (U := U) aTrans
    (skewPart abar) (matTranspose_skewPart abar) P Q
  calc
    Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R) aObs
        (normalizedReferencePrimalLoad abar P)
        (normalizedReferenceDualLoad abar Q) =
      Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R)
        (aRef.coeffOn R) (affineReferencePrimalLoad q P0)
          (affineReferenceDualLoad q Q0) := by
            rw [Book.Ch02.doubledResponseJ_eq_ofAEEq hObsRef, hP0, hQ0]
    _ = Book.Ch02.doubledResponseJ U (aMicro.coeffOn U) P0 Q0 := by
      simpa only [R, U] using hcov
    _ = Book.Ch02.doubledResponseJ U (aSkew.coeffOn U)
        (skewCenteredPrimalLoad (skewPart abar) P)
        (skewCenteredDualLoad (skewPart abar) Q) := by
      simpa only [aMicro, epsilonAffinePhysicalCoeff, aSkew, aTrans, c, z,
        P0, Q0] using hscale
    _ = Book.Ch02.doubledResponseJ U (aTrans.coeffOn U) P Q := hskew
    _ = Transport.coeffSpaceDoubledResponse (adaptedCellAt q k w) aTrans P Q := by
      simpa only [U, Response.adaptedDomainAt_carrier] using
        (Transport.coeffSpaceDoubledResponse_eq_doubledResponseJ U aTrans P Q).symm
    _ = Transport.coeffSpaceDoubledResponse
        (translateSet z (adaptedCellAt q k w)) a P Q := by
      exact (coeffSpaceDoubledResponse_translateSet_real
        z (adaptedCellAt q k w) a P Q).symm
    _ = Transport.coeffSpaceDoubledResponse
        (adaptedCellTranslate q k (z + adaptedCellCenter q k w)) a P Q := by
      rw [translateSet_adaptedCellAt_eq_translate]

end

end RowSupply
end HighContrast
end HCPolySupport
