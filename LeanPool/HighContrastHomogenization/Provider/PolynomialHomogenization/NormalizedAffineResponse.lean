/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedLoadCovariance
public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseCell

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.NormalizedAffineResponse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine covariance of the doubled response

An exact positive-definite affine map transports a cube coefficient family to
an adapted cell.  The doubled response is covariant only after transforming
the primal and dual loads in their distinct contragredient ways.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

private theorem quasiMeasurePreserving_matVecMul
    (q : Mat d) (hq : IsUnit q.det) :
    Measure.QuasiMeasurePreserving (matVecMul q) volume volume := by
  refine ⟨(continuous_matVecMul q).measurable, ?_⟩
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := q) hq.ne_zero
  change Measure.map (Matrix.toLin' q) volume ≪ volume
  rw [hmap]
  exact Measure.smul_absolutelyContinuous

private theorem affineCoefficient_ae_eq
    (q : Mat d) (hq : IsUnit q.det) {a b : CoeffField d}
    (hab : a =ᵐ[volume] b) :
    affineCoefficient q hq a =ᵐ[volume] affineCoefficient q hq b := by
  have hpull := (quasiMeasurePreserving_matVecMul q hq).tendsto_ae hab
  filter_upwards [hpull] with y hy
  change a (matVecMul q y) = b (matVecMul q y) at hy
  simp only [affineCoefficient_apply]
  rw [hy]

private theorem responseJ_affineResponseCell_of_ae
    {q : Mat d} (hq : q.PosDef) (t k : ℤ) (w : Fin d → ℤ)
    (a : CoeffSpace d)
    (aRef : Book.Ch02.CoeffOn
      (Book.Ch02.cubeDomain (translateCube w (originCube d k))))
    (haRef : aRef.toCoeffField =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)) : Set (Vec d))]
      affineCoefficient q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
        (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField)
    (p r : Vec d) :
    Book.Ch02.responseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k))) aRef
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) =
      Book.Ch02.responseJ (Response.adaptedDomainAt hq k w)
        (a.coeffOn (Response.adaptedDomainAt hq k w)) p r := by
  obtain ⟨bRef, hbRef⟩ := exists_adaptedReferenceCoeffFamily hq t a
  let R := translateCube w (originCube d k)
  have hae : Book.Ch02.CoeffOn.AEEq aRef (bRef.coeffOn R) := by
    refine haRef.trans ?_
    exact Filter.Eventually.of_forall fun y => (congrFun (hbRef R) y).symm
  calc
    Book.Ch02.responseJ (Book.Ch02.cubeDomain R) aRef
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) =
      Book.Ch02.responseJ (Book.Ch02.cubeDomain R) (bRef.coeffOn R)
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) :=
      Book.Ch02.responseJ_eq_ofAEEq hae _ _
    _ = Book.Ch02.responseJ (Response.adaptedDomainAt hq k w)
        (a.coeffOn (Response.adaptedDomainAt hq k w)) p r :=
      responseJ_affineResponseCell hq t k w a bRef hbRef p r

private theorem transpose_affineReference_ae
    {q : Mat d} (hq : q.PosDef) (t k : ℤ) (w : Fin d → ℤ)
    (a : CoeffSpace d)
    (aRef : Book.Ch02.CoeffOn
      (Book.Ch02.cubeDomain (translateCube w (originCube d k))))
    (haRef : aRef.toCoeffField =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)) : Set (Vec d))]
      affineCoefficient q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
        (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField) :
    aRef.transpose.toCoeffField =ᵐ[
      volumeMeasureOn
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)) : Set (Vec d))]
      affineCoefficient q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
        (a.transpose.coeffOn (Response.adaptedDomain hq t)).toCoeffField := by
  let hqdet := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have htranspose :
      (a.transpose.coeffOn (Response.adaptedDomain hq t)).toCoeffField =ᵐ[volume]
        fun x => matTranspose
          ((a.coeffOn (Response.adaptedDomain hq t)).toCoeffField x) := by
    simpa only [CoeffSpace.coeffOn_toCoeffField] using CoeffSpace.transpose_ae a
  have hpull := affineCoefficient_ae_eq q hqdet htranspose
  have hlocal :
      aRef.transpose.toCoeffField =ᵐ[
        volumeMeasureOn
          (Book.Ch02.cubeDomain (translateCube w (originCube d k)) : Set (Vec d))]
        affineCoefficient q hqdet
          (fun x => matTranspose
            ((a.coeffOn (Response.adaptedDomain hq t)).toCoeffField x)) := by
    filter_upwards [haRef] with y hy
    rw [Book.Ch02.CoeffOn.transpose_apply, hy,
      matTranspose_affineCoefficient_apply, affineCoefficient_apply]
  exact hlocal.trans (ae_restrict_of_ae hpull.symm)

/-- Doubled affine covariance on an aligned cell, with the distinct primal and
dual transformed loads. -/
theorem doubledResponseJ_affineResponseCell
    {q : Mat d} (hq : q.PosDef) (t k : ℤ) (w : Fin d → ℤ)
    (a : CoeffSpace d) (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField = affineCoefficient q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
        (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField)
    (P Q : BlockVec d) :
    Book.Ch02.doubledResponseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        (aRef.coeffOn (translateCube w (originCube d k)))
        (affineReferencePrimalLoad q P) (affineReferenceDualLoad q Q) =
      Book.Ch02.doubledResponseJ (Response.adaptedDomainAt hq k w)
        (a.coeffOn (Response.adaptedDomainAt hq k w)) P Q := by
  rcases P with ⟨p, r⟩
  rcases Q with ⟨rStar, pStar⟩
  let R := translateCube w (originCube d k)
  have href :
      (aRef.coeffOn R).toCoeffField =ᵐ[
        volumeMeasureOn (Book.Ch02.cubeDomain R : Set (Vec d))]
        affineCoefficient q
          ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
          (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField :=
    Filter.Eventually.of_forall fun y => congrFun (haRef R) y
  have hrefT := transpose_affineReference_ae hq t k w a (aRef.coeffOn R) href
  have hprimal := responseJ_affineResponseCell_of_ae
    hq t k w a (aRef.coeffOn R) href
  have hadjoint0 := responseJ_affineResponseCell_of_ae
    hq t k w a.transpose (aRef.coeffOn R).transpose hrefT
  have hadjoint (x y : Vec d) :
      Book.Ch02.responseJ (Response.adaptedDomainAt hq k w)
          (a.transpose.coeffOn (Response.adaptedDomainAt hq k w)) x y =
        Book.Ch02.responseJ (Response.adaptedDomainAt hq k w)
          ((a.coeffOn (Response.adaptedDomainAt hq k w)).transpose) x y :=
    Book.Ch02.responseJ_eq_ofAEEq
      (CoeffSpace.coeffOn_transpose_aeeq a (Response.adaptedDomainAt hq k w)) x y
  rw [Book.Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum,
    Book.Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum]
  simp only [affineReferencePrimalLoad, affineReferenceDualLoad]
  have hpSub :
      matVecMul (matTranspose q) p - matVecMul (matTranspose q) pStar =
        matVecMul (matTranspose q) (p - pStar) := by
    ext i
    simp only [matVecMul, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hrSub : matVecMul q⁻¹ rStar - matVecMul q⁻¹ r =
      matVecMul q⁻¹ (rStar - r) := by
    ext i
    simp only [matVecMul, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hpAdd :
    matVecMul (matTranspose q) pStar + matVecMul (matTranspose q) p =
        matVecMul (matTranspose q) (pStar + p) := by
    ext i
    simp only [matVecMul, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hrAdd : matVecMul q⁻¹ rStar + matVecMul q⁻¹ r =
      matVecMul q⁻¹ (rStar + r) := by
    ext i
    simp only [matVecMul, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp only [R] at hprimal hadjoint0
  rw [hpSub, hrSub, hpAdd, hrAdd, hprimal, hadjoint0, hadjoint]

end

end HighContrast
end HCPolySupport
