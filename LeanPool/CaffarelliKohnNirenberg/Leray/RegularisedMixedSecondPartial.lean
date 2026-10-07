/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTransportDivergence
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTransportCutoff
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedConvolutionSmooth
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Symmetry of classical spatial second derivatives

Twice continuously differentiable scalar fields have commuting coordinate
second derivatives. This identifies the leading differentiated transport
term with the transport of a first derivative.
-/

public section

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Coordinate second derivatives commute for a twice continuously
differentiable scalar field. -/
theorem regularised_mixedSecondPartial_comm
    (v : Vec3 → ℝ) (hv : ContDiff ℝ 2 v)
    (x : Vec3) (i j : Fin 3) :
    fderiv ℝ (fun y : Vec3 => fderiv ℝ v y (CKN.basisVec i)) x
        (CKN.basisVec j) =
      fderiv ℝ (fun y : Vec3 => fderiv ℝ v y (CKN.basisVec j)) x
        (CKN.basisVec i) := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hv.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have happly (k l : Fin 3) :
      fderiv ℝ (fun y : Vec3 => fderiv ℝ v y (CKN.basisVec k)) x
          (CKN.basisVec l) =
        (fderiv ℝ (fderiv ℝ v) x (CKN.basisVec l)) (CKN.basisVec k) := by
    have hconst : DifferentiableAt ℝ (fun _ : Vec3 => CKN.basisVec k) x :=
      differentiableAt_const _
    have h := fderiv_clm_apply hfd hconst
    have h' := congrArg (fun F : Vec3 →L[ℝ] ℝ => F (CKN.basisVec l)) h
    simpa using h'
  rw [happly i j, happly j i]
  exact (hv.contDiffAt.isSymmSndFDerivAt (by norm_num))
    (CKN.basisVec j) (CKN.basisVec i)

end CKN.Leray

end
