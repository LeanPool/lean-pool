/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Shared symmetry of second spatial derivatives. -/

@[expose] public section

noncomputable section

open Homogenization MeasureTheory

namespace AVenhance.Infra.SpatialSecondDerivatives

/-- Smooth coordinate derivatives commute at every spatial point. -/
theorem coordinate_derivatives_commute {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y i) x j =
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y j) x i := by
  have hAt := hf.contDiffAt (x := x)
  have hC2 : ContDiffAt ℝ 2 f x := hAt.of_le (by norm_num)
  have hsymm := hC2.isSymmSndFDerivAt (by simp)
  have hc : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hCderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hAt.fderiv_right (m := 1) (by simp)
    exact hCderiv.differentiableAt (by norm_num)
  have hu0 : DifferentiableAt ℝ (fun _ : Vec 2 => basisVec i) x :=
    differentiableAt_const (basisVec i)
  have hu1 : DifferentiableAt ℝ (fun _ : Vec 2 => basisVec j) x :=
    differentiableAt_const (basisVec j)
  have hderiv0 : fderiv ℝ (fun y => fderiv ℝ f y (basisVec i)) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (basisVec i) := by
    have h := fderiv_clm_apply hc hu0
    simpa using h
  have hderiv1 : fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (basisVec j) := by
    have h := fderiv_clm_apply hc hu1
    simpa using h
  have hleft : AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad f y i) x j =
      fderiv ℝ (fderiv ℝ f) x (basisVec j) (basisVec i) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (basisVec i)) x (basisVec j) = _
    rw [hderiv0]
    rfl
  have hright : AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad f y j) x i =
      fderiv ℝ (fderiv ℝ f) x (basisVec i) (basisVec j) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) x (basisVec i) = _
    rw [hderiv1]
    rfl
  rw [hleft, hright]
  exact hsymm (basisVec j) (basisVec i)

end AVenhance.Infra.SpatialSecondDerivatives
