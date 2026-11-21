/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # The quadratic confinement potential -/

public section

namespace CutoffRigidity


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic confinement potential of rate `ρ`. -/
@[expose] noncomputable def quadraticLangevinPotential (ρ : ℝ) (x : E) : ℝ :=
  ρ / 2 * ‖x‖ ^ 2

/-- Actual gradient of the quadratic potential. -/
theorem gradient_quadraticLangevinPotential (ρ : ℝ) (x : E) :
    gradient (quadraticLangevinPotential ρ) x = ρ • x := by
  have hd := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul (ρ / 2)
  simp only [two_smul] at hd
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left]
  unfold quadraticLangevinPotential
  rw [hd.fderiv, real_inner_smul_left]
  simp only [smul_apply, add_apply, smul_eq_mul]
  change ρ / 2 * (inner ℝ x z + inner ℝ x z) = ρ * inner ℝ x z
  ring

/-- The actual derivative functional of the quadratic potential. -/
theorem fderiv_quadraticLangevinPotential (ρ : ℝ) (x : E) :
    fderiv ℝ (quadraticLangevinPotential ρ) x = ρ • innerSL ℝ x := by
  ext z
  rw [← inner_gradient_left, gradient_quadraticLangevinPotential, real_inner_smul_left]
  rfl

/-- Its actual Hessian is exactly the curvature quadratic form. -/
theorem hessian_quadraticLangevinPotential (ρ : ℝ) (x z : E) :
    fderiv ℝ (fderiv ℝ (quadraticLangevinPotential ρ)) x z z = ρ * ‖z‖ ^ 2 := by
  have hfun : fderiv ℝ (quadraticLangevinPotential (E := E) ρ) =
      fun x : E => ρ • innerSL ℝ x :=
    by
      funext x
      exact fderiv_quadraticLangevinPotential ρ x
  have hd := ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt (x := x)).const_smul ρ
  have hd' : HasFDerivAt (fun y : E => ρ • innerSL ℝ y) (ρ • innerSL ℝ) x := by
    convert! hd using 1
  rw [hfun, hd'.fderiv]
  simp only [smul_apply, smul_eq_mul]
  change ρ * inner ℝ z z = _
  rw [real_inner_self_eq_norm_sq]

omit [CompleteSpace E] in
/-- Smoothness of the actual quadratic potential. -/
theorem contDiff_quadraticLangevinPotential (ρ : ℝ) :
    ContDiff ℝ 2 (quadraticLangevinPotential (E := E) ρ) := by
  unfold quadraticLangevinPotential
  have hn : ContDiff ℝ 2 (fun x : E => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  exact (contDiff_const (c := ρ / 2)).mul hn

end CutoffRigidity
