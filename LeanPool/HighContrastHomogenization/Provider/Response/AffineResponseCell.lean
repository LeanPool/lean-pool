/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellDomain
public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseSolution

/-!
# High-contrast homogenization: Provider.Response.AffineResponseCell

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine covariance on aligned response cells

Every aligned adapted cell is the grid image of the correspondingly translated
reference cube.  A single compatible reference coefficient family therefore
transports the Chapter 2 solutions, response values, and second variations on
all cells of an aligned subdivision.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem matVecMul_sub_vec (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]

private theorem exists_solution_affinePullbackOn {L : Mat d}
    (hL : IsUnit L.det) (U V : Book.Ch02.Domain d)
    (hV : matImage L⁻¹ (U : Set (Vec d)) = (V : Set (Vec d)))
    {a : Book.Ch02.CoeffOn U} {b : Book.Ch02.CoeffOn V}
    (hab : b.toCoeffField = affineCoefficient L hL a.toCoeffField)
    (u : Book.Ch02.Solution U a) :
    ∃ v : Book.Ch02.Solution V b,
      v.toH1.toFun = (fun y ↦ u.toH1.toFun (matVecMul L y)) ∧
      v.toH1.grad = (fun y ↦
        matVecMul (matTranspose L) (u.toH1.grad (matVecMul L y))) := by
  have hh1 := exists_h1Function_affinePullback hL U.measurableSet u.toH1
  rw [hV] at hh1
  obtain ⟨vH1, hvfun, hvgrad⟩ := hh1
  have hUV : matImage L (V : Set (Vec d)) = (U : Set (Vec d)) := by
    rw [← hV, matImage_matImage_inv hL]
  have hsol : IsSolenoidalOn (V : Set (Vec d))
      (fun x ↦ matVecMul (b.toCoeffField x) (vH1.grad x)) := by
    intro phi
    have hphiPull := exists_h10Function_affinePullback
      (Matrix.isUnit_nonsing_inv_det L hL) V.measurableSet phi
    rw [Matrix.nonsing_inv_nonsing_inv L hL, hUV] at hphiPull
    obtain ⟨psi, _hpsifun, hpsigrad⟩ := hphiPull
    let p : Vec d → ℝ := fun x ↦
      vecDot (matVecMul (a.toCoeffField x) (u.toH1.grad x))
        (psi.toH1Function.grad x)
    let r : Vec d → ℝ := fun y ↦
      vecDot (matVecMul (b.toCoeffField y) (vH1.grad y))
        (phi.toH1Function.grad y)
    have hrp : ∀ y, r y = p (matVecMul L y) := by
      intro y
      change vecDot (matVecMul (b.toCoeffField y) (vH1.grad y))
          (phi.toH1Function.grad y) =
        vecDot
          (matVecMul (a.toCoeffField (matVecMul L y))
            (u.toH1.grad (matVecMul L y)))
          (psi.toH1Function.grad (matVecMul L y))
      rw [hab, hvgrad, affineCoefficient_flux hL]
      rw [← vecDot_matVecMul_transpose]
      rw [hpsigrad]
      simp only [matVecMul_mul, Matrix.nonsing_inv_mul L hL, matVecMul_one]
    have hpzero : ∫ x in (U : Set (Vec d)), p x ∂volume = 0 := by
      simpa only [p] using u.isHarmonic.2 psi
    have hchange := setIntegral_matImage hL V.measurableSet p
    rw [hUV, hpzero, smul_eq_mul] at hchange
    have hrint : (∫ y in (V : Set (Vec d)), r y ∂volume) =
        ∫ y in (V : Set (Vec d)), p (matVecMul L y) ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall hrp)
    rw [← hrint] at hchange
    exact (mul_eq_zero.mp hchange.symm).resolve_left
      (abs_ne_zero.mpr hL.ne_zero)
  let v : Book.Ch02.Solution V b :=
    { toH1 := vH1
      isHarmonic := ⟨vH1.isPotentialOn, hsol⟩ }
  exact ⟨v, hvfun, hvgrad⟩

private theorem affineCoefficient_inv_affineCoefficient_apply {L : Mat d}
    (hL : IsUnit L.det) (a : CoeffField d) (x : Vec d) :
    affineCoefficient L⁻¹ (Matrix.isUnit_nonsing_inv_det L hL)
        (affineCoefficient L hL a) x = a x := by
  have hT : matTranspose L⁻¹ * matTranspose L = (1 : Mat d) := by
    have hLT : IsUnit (matTranspose L).det := by
      simpa [matTranspose] using Matrix.isUnit_det_transpose L hL
    have hinvT : matTranspose L⁻¹ = (matTranspose L)⁻¹ := by
      simpa [matTranspose] using (Matrix.transpose_nonsing_inv (A := L))
    rw [hinvT, Matrix.nonsing_inv_mul _ hLT]
  rw [affineCoefficient_apply, affineCoefficient_apply,
    Matrix.nonsing_inv_nonsing_inv L hL]
  rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]
  calc
    L * (L⁻¹ * a x * matTranspose L⁻¹) * matTranspose L =
        (L * L⁻¹) * a x * (matTranspose L⁻¹ * matTranspose L) := by
      simp only [Matrix.mul_assoc]
    _ = a x := by
      rw [Matrix.mul_nonsing_inv L hL, hT, Matrix.one_mul, Matrix.mul_one]

private theorem affineReferenceCell_coeff_eq {q : Mat d} (hq : q.PosDef)
    (t k : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField = affineCoefficient q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
        (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField) :
    (aRef.coeffOn (translateCube w (originCube d k))).toCoeffField =
      affineCoefficient q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
        (a.coeffOn (Response.adaptedDomainAt hq k w)).toCoeffField := by
  simpa only [CoeffSpace.coeffOn_toCoeffField] using
    haRef (translateCube w (originCube d k))

private theorem matImage_inv_adaptedDomainAt {q : Mat d} (hq : q.PosDef)
    (k : ℤ) (w : Fin d → ℤ) :
    matImage q⁻¹ (Response.adaptedDomainAt hq k w : Set (Vec d)) =
      (Book.Ch02.cubeDomain
        (translateCube w (originCube d k)) : Set (Vec d)) := by
  rw [Response.adaptedDomainAt_carrier, Book.Ch02.cubeDomain_coe,
    Recurrence.adaptedCellAt_eq_image]
  change matImage q⁻¹ (matImage q (standardCell d k w)) = _
  rw [matImage_inv_matImage
    ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)]
  rfl

/-- A solution on an aligned adapted cell pulls back to the matching translated
reference cube using the same compatible reference coefficient family as the
parent cell. -/
theorem exists_affineResponseCellSolution {q : Mat d} (hq : q.PosDef)
    (t k : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField = affineCoefficient q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
        (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField)
    (u : Book.Ch02.Solution (Response.adaptedDomainAt hq k w)
      (a.coeffOn (Response.adaptedDomainAt hq k w))) :
    ∃ uRef : Book.Ch02.Solution
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        (aRef.coeffOn (translateCube w (originCube d k))),
      uRef.toH1.toFun = (fun y ↦ u.toH1.toFun (matVecMul q y)) ∧
      uRef.toH1.grad = (fun y ↦
        matVecMul (matTranspose q) (u.toH1.grad (matVecMul q y))) := by
  apply exists_solution_affinePullbackOn
    ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
    (Response.adaptedDomainAt hq k w)
    (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
  · exact matImage_inv_adaptedDomainAt hq k w
  · exact affineReferenceCell_coeff_eq hq t k w a aRef haRef

private theorem exists_inverseAffineResponseCellSolution {q : Mat d}
    (hq : q.PosDef) (t k : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField = affineCoefficient q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
        (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField)
    (uRef : Book.Ch02.Solution
      (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
      (aRef.coeffOn (translateCube w (originCube d k)))) :
    ∃ u : Book.Ch02.Solution (Response.adaptedDomainAt hq k w)
        (a.coeffOn (Response.adaptedDomainAt hq k w)),
      u.toH1.toFun = (fun x ↦ uRef.toH1.toFun (matVecMul q⁻¹ x)) ∧
      u.toH1.grad = (fun x ↦
        matVecMul (matTranspose q⁻¹) (uRef.toH1.grad (matVecMul q⁻¹ x))) := by
  have hqdet : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have hcoeff := affineReferenceCell_coeff_eq hq t k w a aRef haRef
  have haInv : (a.coeffOn (Response.adaptedDomainAt hq k w)).toCoeffField =
      affineCoefficient q⁻¹ (Matrix.isUnit_nonsing_inv_det q hqdet)
        (aRef.coeffOn (translateCube w (originCube d k))).toCoeffField := by
    funext x
    rw [hcoeff]
    exact (affineCoefficient_inv_affineCoefficient_apply hqdet
      (a.coeffOn (Response.adaptedDomainAt hq k w)).toCoeffField x).symm
  apply exists_solution_affinePullbackOn
    (Matrix.isUnit_nonsing_inv_det q hqdet)
    (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
    (Response.adaptedDomainAt hq k w)
  · rw [Matrix.nonsing_inv_nonsing_inv q hqdet,
      ← matImage_inv_adaptedDomainAt hq k w, matImage_matImage_inv hqdet]
  · exact haInv

private theorem average_cellPullback_eq_adapted {q : Mat d}
    (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ) (f : Vec d → ℝ) :
    Book.Ch02.average
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        (fun y ↦ f (matVecMul q y)) =
      Book.Ch02.average (Response.adaptedDomainAt hq k w) f := by
  change volumeAverage (openCubeSet (translateCube w (originCube d k)))
      (fun y ↦ f (matVecMul q y)) = volumeAverage (adaptedCellAt q k w) f
  have himage : matImage q (openCubeSet (translateCube w (originCube d k))) =
      adaptedCellAt q k w := by
    rw [Recurrence.adaptedCellAt_eq_image]
    rfl
  rw [← himage]
  exact (volumeAverage_matImage
    ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
    (isOpen_openCubeSet (translateCube w (originCube d k))).measurableSet f).symm

private theorem responseValue_affineResponseCellSolution {q : Mat d}
    (hq : q.PosDef) (t k : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField = affineCoefficient q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
        (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField)
    (p r : Vec d)
    (u : Book.Ch02.Solution (Response.adaptedDomainAt hq k w)
      (a.coeffOn (Response.adaptedDomainAt hq k w)))
    (uRef : Book.Ch02.Solution
      (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
      (aRef.coeffOn (translateCube w (originCube d k))))
    (hgrad : uRef.toH1.grad = fun y ↦
      matVecMul (matTranspose q) (u.toH1.grad (matVecMul q y))) :
    Book.Ch02.responseValue
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        (aRef.coeffOn (translateCube w (originCube d k)))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) uRef =
      Book.Ch02.responseValue (Response.adaptedDomainAt hq k w)
        (a.coeffOn (Response.adaptedDomainAt hq k w)) p r u := by
  unfold Book.Ch02.responseValue Book.Ch02.responseIntegrand
  rw [hgrad, affineReferenceCell_coeff_eq hq t k w a aRef haRef]
  simp_rw [affineCoefficient_symmetric_energy, affineCoefficient_flux]
  have hp : ∀ y, vecDot (matVecMul (matTranspose q) p)
      (matVecMul q⁻¹
        (matVecMul ((a.coeffOn (Response.adaptedDomainAt hq k w)).toCoeffField
          (matVecMul q y)) (u.toH1.grad (matVecMul q y)))) =
      vecDot p (matVecMul
        ((a.coeffOn (Response.adaptedDomainAt hq k w)).toCoeffField (matVecMul q y))
        (u.toH1.grad (matVecMul q y))) := by
    intro y
    rw [vecDot_comm, vecDot_matVecMul_transpose, matVecMul_mul,
      Matrix.mul_nonsing_inv q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit),
      matVecMul_one, vecDot_comm]
  have hr : ∀ y, vecDot (matVecMul q⁻¹ r)
      (matVecMul (matTranspose q) (u.toH1.grad (matVecMul q y))) =
      vecDot r (u.toH1.grad (matVecMul q y)) := by
    intro y
    rw [vecDot_matVecMul_transpose, matVecMul_mul,
      Matrix.mul_nonsing_inv q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit), matVecMul_one]
  simp_rw [hp, hr]
  change Book.Ch02.average _ (fun y ↦
      Book.Ch02.responseIntegrand _ _ p r u (matVecMul q y)) =
    Book.Ch02.average _ (Book.Ch02.responseIntegrand _ _ p r u)
  exact average_cellPullback_eq_adapted hq k w _

private theorem responseValueSet_affineResponseCell {q : Mat d}
    (hq : q.PosDef) (t k : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField = affineCoefficient q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
        (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField)
    (p r : Vec d) :
    Book.Ch02.responseValueSet
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        (aRef.coeffOn (translateCube w (originCube d k)))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) =
      Book.Ch02.responseValueSet (Response.adaptedDomainAt hq k w)
        (a.coeffOn (Response.adaptedDomainAt hq k w)) p r := by
  ext m
  constructor
  · rintro ⟨uRef, rfl⟩
    obtain ⟨u, _hfun, hgradInv⟩ :=
      exists_inverseAffineResponseCellSolution hq t k w a aRef haRef uRef
    have hqdet := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
    have hqT : IsUnit (matTranspose q).det := by
      simpa [matTranspose] using Matrix.isUnit_det_transpose q hqdet
    have hinvT : matTranspose q⁻¹ = (matTranspose q)⁻¹ := by
      simpa [matTranspose] using (Matrix.transpose_nonsing_inv (A := q))
    have hgrad : uRef.toH1.grad = fun y ↦
        matVecMul (matTranspose q) (u.toH1.grad (matVecMul q y)) := by
      rw [hgradInv, hinvT]
      funext y
      simp only [matVecMul_mul, Matrix.mul_nonsing_inv _ hqT,
        Matrix.nonsing_inv_mul q hqdet, matVecMul_one]
    exact ⟨u, responseValue_affineResponseCellSolution
      hq t k w a aRef haRef p r u uRef hgrad⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨uRef, _hfun, hgrad⟩ :=
      exists_affineResponseCellSolution hq t k w a aRef haRef u
    exact ⟨uRef, (responseValue_affineResponseCellSolution
      hq t k w a aRef haRef p r u uRef hgrad).symm⟩

/-- The response functional on every aligned physical cell equals the response
on its translated reference cube at the dual transformed loads. -/
theorem responseJ_affineResponseCell {q : Mat d} (hq : q.PosDef)
    (t k : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField = affineCoefficient q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
        (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField)
    (p r : Vec d) :
    Book.Ch02.responseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        (aRef.coeffOn (translateCube w (originCube d k)))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) =
      Book.Ch02.responseJ (Response.adaptedDomainAt hq k w)
        (a.coeffOn (Response.adaptedDomainAt hq k w)) p r := by
  unfold Book.Ch02.responseJ
  rw [responseValueSet_affineResponseCell hq t k w a aRef haRef p r]

end

end HighContrast
end HCPolySupport
