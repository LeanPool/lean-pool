/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineBestFit
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCorrector
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientIterationGeometry

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineSlopeMap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite affine-solution best-fit slopes

This module restricts a finite affine-boundary solution to a smaller centered
cube and composes that scalar `L²` datum with the affine best-fit maps.  The
resulting coefficient and slope maps are algebraic linear maps.  No matrix
inverse or quantitative coefficient-space norm is introduced here.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open CubeCalderonZygmund

noncomputable section

private theorem triadicCube_ext {d : ℕ} {Q R : TriadicCube d}
    (hscale : Q.scale = R.scale) (hindex : Q.index = R.index) : Q = R := by
  cases Q
  cases R
  cases hscale
  cases hindex
  rfl

theorem originCube_mem_descendantsAtDepth_of_int_le
    {d : ℕ} {k m : ℤ} (hkm : k ≤ m) :
    originCube d k ∈
      descendantsAtDepth (originCube d m) (Int.toNat (m - k)) := by
  have hgap : (Int.toNat (m - k) : ℤ) = m - k :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hkm)
  have hcube :
      centralDescendant (originCube d m) (Int.toNat (m - k)) =
        originCube d k := by
    apply triadicCube_ext
    · rw [centralDescendant_scale]
      simp only [originCube]
      omega
    · funext i
      rw [centralDescendant_index]
      simp [originCube]
  rw [← hcube]
  exact centralDescendant_mem_descendantsAtDepth _ _

private theorem openCubeSet_originCube_subset_of_int_le
    {d : ℕ} {k m : ℤ} (hkm : k ≤ m) :
    openCubeSet (originCube d k) ⊆ openCubeSet (originCube d m) :=
  openCubeSet_subset_of_mem_descendantsAtDepth
    (originCube_mem_descendantsAtDepth_of_int_le (d := d) hkm)

/-- The affine-boundary solution on `Q_m`, restricted as an `H¹` function to
the inner cube `Q_k`. -/
@[expose]
noncomputable def finiteAffineSolutionInnerH1
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (e : Vec d) :
    H1Function
      (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) :=
  (finiteAffineSolution a m e).toH1.restrictToOpenSubcube
    (originCube_mem_descendantsAtDepth_of_int_le (d := d) hkm)

/-- Restriction leaves the selected finite solution's representative
unchanged. -/
@[simp] theorem finiteAffineSolutionInnerH1_toFun
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (e : Vec d) :
    (finiteAffineSolutionInnerH1 a k m hkm e).toFun =
      (finiteAffineSolution a m e).toH1.toFun :=
  rfl

/-- Restriction leaves the selected finite solution's weak gradient
unchanged. -/
@[simp] theorem finiteAffineSolutionInnerH1_grad
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (e : Vec d) :
    (finiteAffineSolutionInnerH1 a k m hkm e).grad =
      (finiteAffineSolution a m e).toH1.grad :=
  rfl

theorem finiteAffineSolutionInnerH1_toFun_add_ae
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (e e' : Vec d) :
    (finiteAffineSolutionInnerH1 a k m hkm (e + e')).toFun
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d))]
      fun x =>
        (finiteAffineSolutionInnerH1 a k m hkm e).toFun x +
          (finiteAffineSolutionInnerH1 a k m hkm e').toFun x := by
  have houter := finiteAffineSolution_toFun_add a m e e'
  have hinner := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
    (openCubeSet_originCube_subset_of_int_le (d := d) hkm)
    (by
      simpa only [volumeMeasureOn, Book.Ch02.cubeDomain_coe] using! houter)
  simpa only [volumeMeasureOn, Book.Ch02.cubeDomain_coe,
    finiteAffineSolutionInnerH1_toFun] using! hinner

theorem finiteAffineSolutionInnerH1_toFun_smul_ae
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (r : ℝ) (e : Vec d) :
    (finiteAffineSolutionInnerH1 a k m hkm (r • e)).toFun
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d))]
      fun x => r * (finiteAffineSolutionInnerH1 a k m hkm e).toFun x := by
  have houter := finiteAffineSolution_toFun_smul a m r e
  have hinner := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
    (openCubeSet_originCube_subset_of_int_le (d := d) hkm)
    (by
      simpa only [volumeMeasureOn, Book.Ch02.cubeDomain_coe] using! houter)
  simpa only [volumeMeasureOn, Book.Ch02.cubeDomain_coe,
    finiteAffineSolutionInnerH1_toFun] using! hinner

theorem h1_toScalarL2_eq_of_ae_eq
    {d : ℕ} {U : Set (Vec d)} (u v : H1Function U)
    (huv : u.toFun =ᵐ[volumeMeasureOn U] v.toFun) :
    u.toScalarL2 = v.toScalarL2 := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [H1Function.coeFn_toScalarL2 u, H1Function.coeFn_toScalarL2 v, huv]
    with x hu hv huvx
  rw [hu, hv, huvx]

/-- The inner-cube scalar `L²` realization of finite affine-boundary solutions,
linear in the boundary slope. -/
@[expose]
noncomputable def finiteAffineSolutionInnerL2LinearMap
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) :
    Vec d →ₗ[ℝ]
      ScalarL2
        (Book.Ch02.cubeDomain (originCube d k) : Set (Vec d)) where
  toFun e := (finiteAffineSolutionInnerH1 a k m hkm e).toScalarL2
  map_add' e e' := by
    rw [← H1Function.toScalarL2_add]
    apply h1_toScalarL2_eq_of_ae_eq
    simpa only [H1Function.add_toFun] using
      finiteAffineSolutionInnerH1_toFun_add_ae a k m hkm e e'
  map_smul' r e := by
    rw [← H1Function.toScalarL2_smul]
    apply h1_toScalarL2_eq_of_ae_eq
    simpa only [H1Function.smul_toFun, RingHom.id_apply] using
      finiteAffineSolutionInnerH1_toFun_smul_ae a k m hkm r e

/-- Application of the inner finite-solution `L²` map. -/
@[simp] theorem finiteAffineSolutionInnerL2LinearMap_apply
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (e : Vec d) :
    finiteAffineSolutionInnerL2LinearMap a k m hkm e =
      (finiteAffineSolutionInnerH1 a k m hkm e).toScalarL2 :=
  rfl

/-- Best affine coefficients on `Q_k` for the finite solution posed on
`Q_m`, linear in its boundary slope. -/
@[expose]
noncomputable def finiteAffineBestFitCoefficients
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) :
    Vec d →ₗ[ℝ] AffineCoefficients d :=
  (originCubeAffineBestFitCoefficients d k).comp
    (finiteAffineSolutionInnerL2LinearMap a k m hkm)

/-- Best affine intercept on `Q_k` for the finite solution posed on `Q_m`. -/
@[expose]
noncomputable def finiteAffineBestFitIntercept
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) :
    Vec d →ₗ[ℝ] ℝ :=
  (originCubeAffineBestFitIntercept d k).comp
    (finiteAffineSolutionInnerL2LinearMap a k m hkm)

/-- Best affine slope on `Q_k` for the finite solution posed on `Q_m`. -/
@[expose]
noncomputable def finiteAffineBestFitSlope
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) :
    Vec d →ₗ[ℝ] Vec d :=
  (originCubeAffineBestFitSlope d k).comp
    (finiteAffineSolutionInnerL2LinearMap a k m hkm)

/-- Application of the finite-solution best intercept map. -/
@[simp] theorem finiteAffineBestFitIntercept_apply
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (e : Vec d) :
    finiteAffineBestFitIntercept a k m hkm e =
      originCubeAffineBestFitIntercept d k
        (finiteAffineSolutionInnerL2LinearMap a k m hkm e) :=
  rfl

/-- Application of the finite-solution best slope map. -/
@[simp] theorem finiteAffineBestFitSlope_apply
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (e : Vec d) :
    finiteAffineBestFitSlope a k m hkm e =
      originCubeAffineBestFitSlope d k
        (finiteAffineSolutionInnerL2LinearMap a k m hkm e) :=
  rfl

/-- The finite-solution best coefficients attain the normalized affine error
on the inner cube. -/
theorem normalizedAffineCandidateError_finiteAffineBestFit_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (e : Vec d)
    (c : ℝ) (p : Vec d) :
    normalizedAffineCandidateError (originCube d k)
        (finiteAffineSolution a m e).toH1.toFun
        (finiteAffineBestFitIntercept a k m hkm e)
        (finiteAffineBestFitSlope a k m hkm e) ≤
      normalizedAffineCandidateError (originCube d k)
        (finiteAffineSolution a m e).toH1.toFun c p := by
  simpa only [finiteAffineSolutionInnerH1_toFun,
    finiteAffineBestFitIntercept_apply, finiteAffineBestFitSlope_apply,
    finiteAffineSolutionInnerL2LinearMap_apply] using
    normalizedAffineCandidateError_bestFit_le d k
      (finiteAffineSolutionInnerH1 a k m hkm e) c p

end

end HighContrast
end HCPolySupport
