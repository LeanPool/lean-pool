/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineH10
public import LeanPool.HighContrastHomogenization.Analytic.AffinePairing
public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseGeometry
public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNormCellAverage
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Averages
public import LeanPool.HighContrastHomogenization.Support.Probability.LocalEllipticitySlices

/-!
# High-contrast homogenization: Provider.Response.AffineResponseSolution

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section
/-!
# Affine covariance of Chapter 2 responses

The adapted cell is the image of its centered reference cube under the grid
matrix.  Pulling solutions back by this map transforms gradients by the
transpose and fluxes by the inverse.  The corresponding dual transformations
of the two response loads preserve every normalized variational value.
-/
namespace HCPolySupport
namespace HighContrast
open MeasureTheory
noncomputable section
variable {d : ℕ}
private theorem exists_solution_affinePullback {L : Mat d}
    (hL : IsUnit L.det) (U V : Book.Ch02.Domain d)
    (hV : matImage L⁻¹ (U : Set (Vec d)) = (V : Set (Vec d)))
    {a : Book.Ch02.CoeffOn U} {b : Book.Ch02.CoeffOn V}
    (hab : b.toCoeffField = affineCoefficient L hL a.toCoeffField)
    (u : Book.Ch02.Solution U a) :
    ∃ v : Book.Ch02.Solution V b,
      v.toH1.toFun = (fun y => u.toH1.toFun (matVecMul L y)) ∧
      v.toH1.grad = (fun y =>
        matVecMul (matTranspose L) (u.toH1.grad (matVecMul L y))) := by
  have hh1 := exists_h1Function_affinePullback hL U.measurableSet u.toH1
  rw [hV] at hh1
  obtain ⟨vH1, hvfun, hvgrad⟩ := hh1
  have hUV : matImage L (V : Set (Vec d)) = (U : Set (Vec d)) := by
    rw [← hV, matImage_matImage_inv hL]
  have hsol : IsSolenoidalOn (V : Set (Vec d))
      (fun x => matVecMul (b.toCoeffField x) (vH1.grad x)) := by
    intro phi
    have hphiPull := exists_h10Function_affinePullback
      (Matrix.isUnit_nonsing_inv_det L hL) V.measurableSet phi
    rw [Matrix.nonsing_inv_nonsing_inv L hL, hUV] at hphiPull
    obtain ⟨psi, _hpsifun, hpsigrad⟩ := hphiPull
    let p : Vec d → ℝ := fun x =>
      vecDot (matVecMul (a.toCoeffField x) (u.toH1.grad x))
        (psi.toH1Function.grad x)
    let r : Vec d → ℝ := fun y =>
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
/-- A physical Chapter 2 solution on an adapted cell pulls back to a solution
on the centered reference cube, with its exact transpose-transformed gradient. -/
theorem exists_affineResponseSolution {q : Mat d} (hq : q.PosDef) (t : ℤ)
    {a : Book.Ch02.CoeffOn (Response.adaptedDomain hq t)}
    {aRef : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d t))}
    (haRef : aRef.toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit) a.toCoeffField)
    (u : Book.Ch02.Solution (Response.adaptedDomain hq t) a) :
    ∃ uRef : Book.Ch02.Solution (Book.Ch02.cubeDomain (originCube d t)) aRef,
      uRef.toH1.toFun = (fun y => u.toH1.toFun (matVecMul q y)) ∧
      uRef.toH1.grad = (fun y =>
        matVecMul (matTranspose q) (u.toH1.grad (matVecMul q y))) := by
  apply exists_solution_affinePullback
    ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
    (Response.adaptedDomain hq t) (Book.Ch02.cubeDomain (originCube d t))
  · simpa only [Response.adaptedDomain_carrier, cubeDomain_originCube_coe] using
      matImage_inv_adaptedCell_eq_centeredCube hq t
  · exact haRef

/-- Every reference-cube solution is the pullback of an adapted-cell solution;
the inverse construction records the inverse-transpose gradient explicitly. -/
theorem exists_inverseAffineResponseSolution {q : Mat d} (hq : q.PosDef)
    (t : ℤ) {a : Book.Ch02.CoeffOn (Response.adaptedDomain hq t)}
    {aRef : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d t))}
    (haRef : aRef.toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit) a.toCoeffField)
    (uRef : Book.Ch02.Solution (Book.Ch02.cubeDomain (originCube d t)) aRef) :
    ∃ u : Book.Ch02.Solution (Response.adaptedDomain hq t) a,
      u.toH1.toFun = (fun x => uRef.toH1.toFun (matVecMul q⁻¹ x)) ∧
      u.toH1.grad = (fun x =>
        matVecMul (matTranspose q⁻¹) (uRef.toH1.grad (matVecMul q⁻¹ x))) := by
  have hqdet : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have haInv : a.toCoeffField = affineCoefficient q⁻¹
      (Matrix.isUnit_nonsing_inv_det q hqdet) aRef.toCoeffField := by
    funext x
    rw [haRef]
    exact (affineCoefficient_inv_affineCoefficient_apply hqdet a.toCoeffField x).symm
  apply exists_solution_affinePullback
    (Matrix.isUnit_nonsing_inv_det q hqdet)
    (Book.Ch02.cubeDomain (originCube d t)) (Response.adaptedDomain hq t)
  · rw [Matrix.nonsing_inv_nonsing_inv q hqdet]
    rfl
  · exact haInv

private theorem average_cubePullback_eq_adapted {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (f : Vec d → ℝ) :
    Book.Ch02.average (Book.Ch02.cubeDomain (originCube d t))
        (fun y => f (matVecMul q y)) =
      Book.Ch02.average (Response.adaptedDomain hq t) f := by
  rw [Book.Ch05.Section53.JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
  exact (average_adaptedDomain_eq_cubeAverage_pullback hq t f).symm

private theorem responseIntegrand_affine {q : Mat d} (hq : q.PosDef)
    (t : ℤ) {a : Book.Ch02.CoeffOn (Response.adaptedDomain hq t)}
    {aRef : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d t))}
    (haRef : aRef.toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit) a.toCoeffField)
    (p r : Vec d) (u : Book.Ch02.Solution (Response.adaptedDomain hq t) a)
    (uRef : Book.Ch02.Solution (Book.Ch02.cubeDomain (originCube d t)) aRef)
    (hgrad : uRef.toH1.grad = fun y =>
      matVecMul (matTranspose q) (u.toH1.grad (matVecMul q y))) :
    Book.Ch02.responseIntegrand (Book.Ch02.cubeDomain (originCube d t)) aRef
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) uRef =
      fun y => Book.Ch02.responseIntegrand (Response.adaptedDomain hq t) a p r u
        (matVecMul q y) := by
  funext y
  unfold Book.Ch02.responseIntegrand
  rw [congrFun hgrad y, congrFun haRef y,
    affineCoefficient_symmetric_energy,
    affineCoefficient_flux]
  have hp : vecDot (matVecMul (matTranspose q) p)
      (matVecMul q⁻¹
        (matVecMul (a.toCoeffField (matVecMul q y))
          (u.toH1.grad (matVecMul q y)))) =
      vecDot p (matVecMul (a.toCoeffField (matVecMul q y))
        (u.toH1.grad (matVecMul q y))) := by
    rw [vecDot_comm, vecDot_matVecMul_transpose, matVecMul_mul,
      Matrix.mul_nonsing_inv q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit), matVecMul_one,
      vecDot_comm]
  have hr : vecDot (matVecMul q⁻¹ r)
      (matVecMul (matTranspose q) (u.toH1.grad (matVecMul q y))) =
      vecDot r (u.toH1.grad (matVecMul q y)) := by
    rw [vecDot_matVecMul_transpose, matVecMul_mul,
      Matrix.mul_nonsing_inv q
        ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit), matVecMul_one]
  rw [hp, hr]

/-- Response values agree after transforming both loads by the dual affine
actions. -/
theorem responseValue_affineResponseSolution {q : Mat d} (hq : q.PosDef)
    (t : ℤ) {a : Book.Ch02.CoeffOn (Response.adaptedDomain hq t)}
    {aRef : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d t))}
    (haRef : aRef.toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit) a.toCoeffField)
    (p r : Vec d) (u : Book.Ch02.Solution (Response.adaptedDomain hq t) a)
    (uRef : Book.Ch02.Solution (Book.Ch02.cubeDomain (originCube d t)) aRef)
    (hgrad : uRef.toH1.grad = fun y =>
      matVecMul (matTranspose q) (u.toH1.grad (matVecMul q y))) :
    Book.Ch02.responseValue (Book.Ch02.cubeDomain (originCube d t)) aRef
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) uRef =
      Book.Ch02.responseValue (Response.adaptedDomain hq t) a p r u := by
  unfold Book.Ch02.responseValue
  rw [responseIntegrand_affine hq t haRef p r u uRef hgrad]
  exact average_cubePullback_eq_adapted hq t _

/-- The physical and reference variational value sets coincide at the dual
transformed loads. -/
theorem responseValueSet_affineResponse {q : Mat d} (hq : q.PosDef) (t : ℤ)
    {a : Book.Ch02.CoeffOn (Response.adaptedDomain hq t)}
    {aRef : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d t))}
    (haRef : aRef.toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit) a.toCoeffField)
    (p r : Vec d) :
    Book.Ch02.responseValueSet (Book.Ch02.cubeDomain (originCube d t)) aRef
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) =
      Book.Ch02.responseValueSet (Response.adaptedDomain hq t) a p r := by
  ext m
  constructor
  · rintro ⟨uRef, rfl⟩
    obtain ⟨u, _hfun, hgradInv⟩ :=
      exists_inverseAffineResponseSolution hq t haRef uRef
    have hqdet := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
    have hqT : IsUnit (matTranspose q).det := by
      simpa [matTranspose] using Matrix.isUnit_det_transpose q hqdet
    have hinvT : matTranspose q⁻¹ = (matTranspose q)⁻¹ := by
      simpa [matTranspose] using (Matrix.transpose_nonsing_inv (A := q))
    have hgrad : uRef.toH1.grad = fun y =>
        matVecMul (matTranspose q) (u.toH1.grad (matVecMul q y)) := by
      rw [hgradInv, hinvT]
      funext y
      simp only [matVecMul_mul, Matrix.mul_nonsing_inv _ hqT,
        Matrix.nonsing_inv_mul q hqdet, matVecMul_one]
    exact ⟨u, responseValue_affineResponseSolution hq t haRef p r u uRef hgrad⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨uRef, _hfun, hgrad⟩ := exists_affineResponseSolution hq t haRef u
    exact ⟨uRef,
      (responseValue_affineResponseSolution hq t haRef p r u uRef hgrad).symm⟩

/-- The Chapter 2 response functional is affine-covariant at the transformed
dual loads. -/
theorem responseJ_affineResponse {q : Mat d} (hq : q.PosDef) (t : ℤ)
    {a : Book.Ch02.CoeffOn (Response.adaptedDomain hq t)}
    {aRef : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d t))}
    (haRef : aRef.toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit) a.toCoeffField)
    (p r : Vec d) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d t)) aRef
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) =
      Book.Ch02.responseJ (Response.adaptedDomain hq t) a p r := by
  unfold Book.Ch02.responseJ
  rw [responseValueSet_affineResponse hq t haRef p r]

end

end HighContrast
end HCPolySupport
