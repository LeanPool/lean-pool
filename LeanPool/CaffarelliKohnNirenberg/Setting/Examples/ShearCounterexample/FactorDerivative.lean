/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Factor derivative identities on space-time products. -/

public section
noncomputable section
open CKN.Foundation.Parabolic
namespace CKN

theorem spatialPartial_eq_joint_fderiv {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : Vec3 × ℝ) (i : Fin 3) :
    spatialPartial (show ParabolicPoint → ℝ from g) i z =
      fderiv ℝ g z (basisVec i, 0) := by
  let G : Vec3 → Vec3 × ℝ := fun x => (x, z.2)
  have hG : HasFDerivAt G
      ((ContinuousLinearMap.id ℝ Vec3).prod (0 : Vec3 →L[ℝ] ℝ)) z.1 := by
    exact (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) z.2 z.1)
  have hF : HasFDerivAt g (fderiv ℝ g z) z :=
    (hg.differentiable (by simp) z).hasFDerivAt
  have hc := hF.comp z.1 hG
  have hfun : (fun x : Vec3 => g (x, z.2)) = g ∘ G := rfl
  change (fderiv ℝ (fun x : Vec3 => g (x, z.2)) z.1) (basisVec i) = _
  rw [hfun, hc.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]

theorem timePartial_eq_joint_fderiv {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : Vec3 × ℝ) :
    timePartial (show ParabolicPoint → ℝ from g) z = fderiv ℝ g z (0, 1) := by
  let G : ℝ → Vec3 × ℝ := fun t => (z.1, t)
  have hG : HasFDerivAt G
      ((0 : ℝ →L[ℝ] Vec3).prod (ContinuousLinearMap.id ℝ ℝ)) z.2 := by
    exact (hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hF : HasFDerivAt g (fderiv ℝ g z) z :=
    (hg.differentiable (by simp) z).hasFDerivAt
  have hc := hF.comp z.2 hG
  have hfun : (fun t : ℝ => g (z.1, t)) = g ∘ G := rfl
  change (fderiv ℝ (fun t : ℝ => g (z.1, t)) z.2) 1 = _
  rw [hfun, hc.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]

end CKN
