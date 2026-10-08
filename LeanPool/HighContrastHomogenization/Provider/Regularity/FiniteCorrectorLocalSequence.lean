/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCorrector
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalLimit

/-!
# High-contrast homogenization: Provider.Regularity.FiniteCorrectorLocalSequence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite-corrector local sequences

The zero-trace parts of the selected affine Dirichlet solutions form an
unshifted sequence on the centered cube exhaustion.  This module records the
almost-everywhere linearity needed to pass that sequence to local limits.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

open MeasureTheory

/-- The finite zero-trace correction is additive in its slope almost
everywhere. -/
theorem finiteAffineCorrection_toFun_add_ae {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e e' : Vec d) :
    (finiteAffineCorrection a m (e + e')).toH1Function.toFun
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun x => (finiteAffineCorrection a m e).toH1Function.toFun x +
        (finiteAffineCorrection a m e').toH1Function.toFun x := by
  filter_upwards [finiteAffineSolution_toFun_add a m e e'] with x hx
  have hx' :
      vecDot (e + e') x +
          (finiteAffineCorrection a m (e + e')).toH1Function.toFun x =
        (vecDot e x +
            (finiteAffineCorrection a m e).toH1Function.toFun x) +
          (vecDot e' x +
            (finiteAffineCorrection a m e').toH1Function.toFun x) := by
    simpa only [finiteAffineSolution_toH1, H1Function.add_toFun,
      finiteAffineBoundaryH1_toFun] using hx
  have hcancel :
      vecDot (e + e') x +
          (finiteAffineCorrection a m (e + e')).toH1Function.toFun x =
        vecDot (e + e') x +
          ((finiteAffineCorrection a m e).toH1Function.toFun x +
            (finiteAffineCorrection a m e').toH1Function.toFun x) := by
    calc
      _ = (vecDot e x +
            (finiteAffineCorrection a m e).toH1Function.toFun x) +
          (vecDot e' x +
            (finiteAffineCorrection a m e').toH1Function.toFun x) := hx'
      _ = _ := by rw [vecDot_add_left]; ring
  exact add_left_cancel hcancel

/-- The finite zero-trace correction is homogeneous in its slope almost
everywhere. -/
theorem finiteAffineCorrection_toFun_smul_ae {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (c : ℝ) (e : Vec d) :
    (finiteAffineCorrection a m (c • e)).toH1Function.toFun
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun x => c * (finiteAffineCorrection a m e).toH1Function.toFun x := by
  filter_upwards [finiteAffineSolution_toFun_smul a m c e] with x hx
  have hx' :
      vecDot (c • e) x +
          (finiteAffineCorrection a m (c • e)).toH1Function.toFun x =
        c * (vecDot e x +
          (finiteAffineCorrection a m e).toH1Function.toFun x) := by
    simpa only [finiteAffineSolution_toH1, H1Function.add_toFun,
      finiteAffineBoundaryH1_toFun] using hx
  have hcancel :
      vecDot (c • e) x +
          (finiteAffineCorrection a m (c • e)).toH1Function.toFun x =
        vecDot (c • e) x +
          c * (finiteAffineCorrection a m e).toH1Function.toFun x := by
    calc
      _ = c * (vecDot e x +
          (finiteAffineCorrection a m e).toH1Function.toFun x) := hx'
      _ = _ := by rw [vecDot_smul_left]; ring
  exact add_left_cancel hcancel

/-- The weak gradient of the finite zero-trace correction is additive in its
slope almost everywhere. -/
theorem finiteAffineCorrection_grad_add_ae {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e e' : Vec d) :
    (finiteAffineCorrection a m (e + e')).toH1Function.grad
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun x => (finiteAffineCorrection a m e).toH1Function.grad x +
        (finiteAffineCorrection a m e').toH1Function.grad x := by
  filter_upwards [finiteAffineSolution_grad_add a m e e'] with x hx
  have hx' :
      (e + e') +
          (finiteAffineCorrection a m (e + e')).toH1Function.grad x =
        (e + (finiteAffineCorrection a m e).toH1Function.grad x) +
          (e' + (finiteAffineCorrection a m e').toH1Function.grad x) := by
    simpa only [finiteAffineSolution_toH1, H1Function.add_grad,
      finiteAffineBoundaryH1_grad] using hx
  have hcancel :
      (e + e') +
          (finiteAffineCorrection a m (e + e')).toH1Function.grad x =
        (e + e') +
          ((finiteAffineCorrection a m e).toH1Function.grad x +
            (finiteAffineCorrection a m e').toH1Function.grad x) := by
    calc
      _ = (e + (finiteAffineCorrection a m e).toH1Function.grad x) +
          (e' + (finiteAffineCorrection a m e').toH1Function.grad x) := hx'
      _ = _ := by abel
  exact add_left_cancel hcancel

/-- The weak gradient of the finite zero-trace correction is homogeneous in
its slope almost everywhere. -/
theorem finiteAffineCorrection_grad_smul_ae {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (c : ℝ) (e : Vec d) :
    (finiteAffineCorrection a m (c • e)).toH1Function.grad
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun x => c • (finiteAffineCorrection a m e).toH1Function.grad x := by
  filter_upwards [finiteAffineSolution_grad_smul a m c e] with x hx
  have hx' :
      c • e + (finiteAffineCorrection a m (c • e)).toH1Function.grad x =
        c • (e + (finiteAffineCorrection a m e).toH1Function.grad x) := by
    simpa only [finiteAffineSolution_toH1, H1Function.add_grad,
      finiteAffineBoundaryH1_grad] using hx
  have hcancel :
      c • e + (finiteAffineCorrection a m (c • e)).toH1Function.grad x =
        c • e + c • (finiteAffineCorrection a m e).toH1Function.grad x := by
    calc
      _ = c • (e + (finiteAffineCorrection a m e).toH1Function.grad x) := hx'
      _ = _ := by rw [smul_add]
  exact add_left_cancel hcancel

/-- The unshifted finite zero-trace corrections on the centered cube
exhaustion. -/
@[expose]
noncomputable def finiteAffineCorrectionLocalSequence {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (e : Vec d) :
    ∀ q : ℕ, H1Function (localGradientCube d q) :=
  fun q => by
    simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
      (finiteAffineCorrection a (q : ℤ) e).toH1Function

end

end HighContrast
end HCPolySupport
