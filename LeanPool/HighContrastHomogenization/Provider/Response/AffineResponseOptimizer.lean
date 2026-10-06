/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseSolution
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseCarriers
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.GradientUniqueness
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.EnergyDensities

/-!
# High-contrast homogenization: Provider.Response.AffineResponseOptimizer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine covariance of canonical response optimizers

Affine pullback transports a physical response maximizer to a maximizer on the
reference cube at the dual transformed loads.  Gradient uniqueness then
identifies the chosen reference maximizer almost everywhere.  This is the
natural strength for the raw Sobolev representatives, and it is sufficient to
identify their cutoff product after integration.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open Book.Ch05.Section53.JUpperBoundWeakNorms

noncomputable section

variable {d : ℕ}

private theorem matVecMul_sub_vec (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]

private theorem vecDot_dual_affine {q : Mat d} (hq : q.PosDef)
    (x y : Vec d) :
    vecDot (matVecMul (matTranspose q) x) (matVecMul q⁻¹ y) = vecDot x y := by
  rw [vecDot_comm, vecDot_matVecMul_transpose, matVecMul_mul,
    Matrix.mul_nonsing_inv q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit),
    matVecMul_one, vecDot_comm]

private theorem cubeAverage_congr_ae {Q : TriadicCube d}
    {f g : Vec d → ℝ}
    (h : f =ᵐ[volumeMeasureOn (cubeSet Q)] g) :
    cubeAverage Q f = cubeAverage Q g := by
  unfold cubeAverage
  congr 1
  exact integral_congr_ae h

/-- Pulling a physical response maximizer to the reference cube preserves its
maximizing property at the dual transformed loads. -/
theorem exists_affineResponseMaximizer {q : Mat d} (hq : q.PosDef) (t : ℤ)
    {a : Book.Ch02.CoeffOn (Response.adaptedDomain hq t)}
    {aRef : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d t))}
    (haRef : aRef.toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit) a.toCoeffField)
    (p r : Vec d) {u : Book.Ch02.Solution (Response.adaptedDomain hq t) a}
    (hu : Book.Ch02.IsResponseMaximizer (Response.adaptedDomain hq t) a p r u) :
    ∃ uRef : Book.Ch02.Solution (Book.Ch02.cubeDomain (originCube d t)) aRef,
      uRef.toH1.grad = (fun y ↦
        matVecMul (matTranspose q) (u.toH1.grad (matVecMul q y))) ∧
      Book.Ch02.IsResponseMaximizer
        (Book.Ch02.cubeDomain (originCube d t)) aRef
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) uRef := by
  obtain ⟨uRef, _hfun, hgrad⟩ :=
    exists_affineResponseSolution hq t haRef u
  refine ⟨uRef, hgrad, ?_⟩
  intro vRef
  obtain ⟨v, _hvfun, hvgradInv⟩ :=
    exists_inverseAffineResponseSolution hq t haRef vRef
  have hqdet : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have hqT : IsUnit (matTranspose q).det := by
    simpa [matTranspose] using Matrix.isUnit_det_transpose q hqdet
  have hinvT : matTranspose q⁻¹ = (matTranspose q)⁻¹ := by
    simpa [matTranspose] using (Matrix.transpose_nonsing_inv (A := q))
  have hvgrad : vRef.toH1.grad = fun y ↦
      matVecMul (matTranspose q) (v.toH1.grad (matVecMul q y)) := by
    rw [hvgradInv, hinvT]
    funext y
    simp only [matVecMul_mul, Matrix.mul_nonsing_inv _ hqT,
      Matrix.nonsing_inv_mul q hqdet, matVecMul_one]
  rw [responseValue_affineResponseSolution hq t haRef p r v vRef hvgrad,
    responseValue_affineResponseSolution hq t haRef p r u uRef hgrad]
  exact hu v

private theorem canonicalGradient_affineAE_of_isMaximizer {q : Mat d}
    (hq : q.PosDef) (t : ℤ)
    {a : Book.Ch02.CoeffOn (Response.adaptedDomain hq t)}
    {aRef : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d t))}
    (haRef : aRef.toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit) a.toCoeffField)
    (p r : Vec d) (u : Book.Ch02.Solution (Response.adaptedDomain hq t) a)
    (hu : Book.Ch02.IsResponseMaximizer (Response.adaptedDomain hq t) a p r u) :
    canonicalMaximizerGradientOnCube (originCube d t) aRef
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) =ᵐ[
      volumeMeasureOn (cubeSet (originCube d t))]
        fun y ↦ matVecMul (matTranspose q) (u.toH1.grad (matVecMul q y)) := by
  obtain ⟨uRef, hgrad, hmax⟩ :=
    exists_affineResponseMaximizer hq t haRef p r hu
  have hsame :=
    Book.Ch02.canonicalMaximizer_sameGradientAE_of_isResponseMaximizer hmax
  rw [Book.Ch02.Solution.SameGradientAE, hgrad] at hsame
  simpa only [canonicalMaximizerGradientOnCube,
    canonicalMaximizerSolutionOnCube, Book.Ch02.cubeDomain_coe,
    volumeMeasureOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using! hsame

private theorem affineResponseDefects_of_isMaximizer {q : Mat d}
    (hq : q.PosDef) (t : ℤ)
    {a : Book.Ch02.CoeffOn (Response.adaptedDomain hq t)}
    {aRef : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d t))}
    (haRef : aRef.toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit) a.toCoeffField)
    (p r p0 r0 : Vec d)
    (u : Book.Ch02.Solution (Response.adaptedDomain hq t) a)
    (hu : Book.Ch02.IsResponseMaximizer (Response.adaptedDomain hq t) a p r u) :
    (canonicalMaximizerGradientDefectOnCube (originCube d t) aRef
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
        (matVecMul (matTranspose q) p0) =ᵐ[
      volumeMeasureOn (cubeSet (originCube d t))]
        fun y ↦ matVecMul (matTranspose q)
          (u.toH1.grad (matVecMul q y) - p0)) ∧
    (canonicalMaximizerFluxDefectOnCube (originCube d t) aRef
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
        (matVecMul q⁻¹ r0) =ᵐ[
      volumeMeasureOn (cubeSet (originCube d t))]
        fun y ↦ matVecMul q⁻¹
          (matVecMul (a.toCoeffField (matVecMul q y))
            (u.toH1.grad (matVecMul q y)) - r0)) := by
  have hgrad := canonicalGradient_affineAE_of_isMaximizer
    hq t haRef p r u hu
  constructor
  · exact hgrad.mono fun y hy ↦ by
      unfold canonicalMaximizerGradientDefectOnCube
      rw [hy, ← matVecMul_sub_vec]
  · exact hgrad.mono fun y hy ↦ by
      unfold canonicalMaximizerFluxDefectOnCube
        canonicalMaximizerFluxOnCube
      rw [hy, haRef, affineCoefficient_flux,
        ← matVecMul_sub_vec]

/-- The reference canonical gradient and flux defects are the dual affine
pullbacks of the centered physical optimizer defects, almost everywhere on
the closed reference cube. -/
theorem centeredResponseOptimizerDefects_affineAE {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    {aRef : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d t))}
    (haRef : aRef.toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField)
    (p r p0 r0 : Vec d) :
    (canonicalMaximizerGradientDefectOnCube (originCube d t) aRef
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
        (matVecMul (matTranspose q) p0) =ᵐ[
      volumeMeasureOn (cubeSet (originCube d t))]
        fun y ↦ matVecMul (matTranspose q)
          ((Response.centeredResponseOptimizer (Response.adaptedDomain hq t) a p r).toH1.grad
            (matVecMul q y) - p0)) ∧
    (canonicalMaximizerFluxDefectOnCube (originCube d t) aRef
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
        (matVecMul q⁻¹ r0) =ᵐ[
      volumeMeasureOn (cubeSet (originCube d t))]
        fun y ↦ matVecMul q⁻¹
          (matVecMul ((a.coeffOn (Response.adaptedDomain hq t)).toCoeffField
              (matVecMul q y))
            ((Response.centeredResponseOptimizer
              (Response.adaptedDomain hq t) a p r).toH1.grad (matVecMul q y)) - r0)) :=
  affineResponseDefects_of_isMaximizer hq t haRef p r p0 r0
    (Response.centeredResponseOptimizer (Response.adaptedDomain hq t) a p r)
    (Response.centeredResponseOptimizer_isMaximizer
      (Response.adaptedDomain hq t) a p r)

private theorem cutoffProduct_affine_of_defects {q : Mat d}
    (hq : q.PosDef) (t : ℤ)
    {a : Book.Ch02.CoeffOn (Response.adaptedDomain hq t)}
    {aRef : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d t))}
    (p r p0 r0 : Vec d) (phi : Vec d → ℝ)
    (u : Book.Ch02.Solution (Response.adaptedDomain hq t) a)
    (hdef :
      (canonicalMaximizerGradientDefectOnCube (originCube d t) aRef
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
          (matVecMul (matTranspose q) p0) =ᵐ[
        volumeMeasureOn (cubeSet (originCube d t))]
          fun y ↦ matVecMul (matTranspose q)
            (u.toH1.grad (matVecMul q y) - p0)) ∧
      (canonicalMaximizerFluxDefectOnCube (originCube d t) aRef
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
          (matVecMul q⁻¹ r0) =ᵐ[
        volumeMeasureOn (cubeSet (originCube d t))]
          fun y ↦ matVecMul q⁻¹
            (matVecMul (a.toCoeffField (matVecMul q y))
              (u.toH1.grad (matVecMul q y)) - r0))) :
    cutoffProductTermOnCube (originCube d t) aRef
        (fun y ↦ phi (matVecMul q y))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
        (matVecMul (matTranspose q) p0) (matVecMul q⁻¹ r0) =
      Book.Ch02.average (Response.adaptedDomain hq t) (fun x ↦
        phi x * ((1 / 2 : ℝ) *
          vecDot (u.toH1.grad x - p0)
            (matVecMul (a.toCoeffField x) (u.toH1.grad x) - r0))) := by
  rw [average_adaptedDomain_eq_cubeAverage_pullback hq t]
  unfold cutoffProductTermOnCube centeredProductDensityOnCube
  apply cubeAverage_congr_ae
  filter_upwards [hdef.1, hdef.2] with y hygrad hyflux
  change phi (matVecMul q y) * ((1 / 2 : ℝ) *
      vecDot
        (canonicalMaximizerGradientDefectOnCube (originCube d t) aRef
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
          (matVecMul (matTranspose q) p0) y)
        (canonicalMaximizerFluxDefectOnCube (originCube d t) aRef
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
          (matVecMul q⁻¹ r0) y)) = _
  rw [hygrad, hyflux, vecDot_dual_affine hq]

/-- The reference cutoff product equals the normalized physical cutoff product
for the centered primal optimizer, with both loads and both centers transformed. -/
theorem cutoffProductTermOnCube_affineResponseOptimizer {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    {aRef : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d t))}
    (haRef : aRef.toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      (a.coeffOn (Response.adaptedDomain hq t)).toCoeffField)
    (phi : Vec d → ℝ) (p r p0 r0 : Vec d) :
    cutoffProductTermOnCube (originCube d t) aRef
        (fun y ↦ phi (matVecMul q y))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)
        (matVecMul (matTranspose q) p0) (matVecMul q⁻¹ r0) =
      Book.Ch02.average (Response.adaptedDomain hq t) (fun x ↦
        phi x * ((1 / 2 : ℝ) *
          vecDot
            ((Response.centeredResponseOptimizer
              (Response.adaptedDomain hq t) a p r).toH1.grad x - p0)
            (matVecMul ((a.coeffOn (Response.adaptedDomain hq t)).toCoeffField x)
              ((Response.centeredResponseOptimizer
                (Response.adaptedDomain hq t) a p r).toH1.grad x) - r0))) :=
  cutoffProduct_affine_of_defects hq t p r p0 r0 phi
    (Response.centeredResponseOptimizer (Response.adaptedDomain hq t) a p r)
    (centeredResponseOptimizerDefects_affineAE hq t a haRef p r p0 r0)

end

end HighContrast
end HCPolySupport
