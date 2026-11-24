/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic.Ring

/-!
# The real Hessian and the Levi quadratic form

The Hessian in this file is the actual second Fréchet derivative of a real-valued
function.  The Levi quadratic form uses the normalization
`(D²u(v,v) + D²u(Iv,Iv))/4`.  For a C² function its value is one quarter of the
ordinary Laplacian along the corresponding complex affine line.

No equivalence with plurisubharmonicity is assumed in this file.
-/

@[expose] public section

noncomputable section

open Laplacian

namespace SGPT.Foundations.Analysis

section RealHessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The real Hessian, evaluated on two vectors. -/
def realHessian (u : E → ℝ) (x v w : E) : ℝ :=
  iteratedFDeriv ℝ 2 u x ![v, w]

theorem realHessian_eq_fderiv (u : E → ℝ) (x v w : E) :
    realHessian u x v w = fderiv ℝ (fderiv ℝ u) x v w := by
  simp [realHessian, iteratedFDeriv_two_apply]

@[simp] theorem realHessian_const (c : ℝ) (x v w : E) :
    realHessian (fun _ : E ↦ c) x v w = 0 := by
  simp [realHessian, iteratedFDeriv_const_of_ne two_ne_zero]

theorem realHessian_add {u v : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a b : E) :
    realHessian (u + v) x a b = realHessian u x a b + realHessian v x a b := by
  simp [realHessian, iteratedFDeriv_add_apply hu hv]

theorem realHessian_smul {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (c : ℝ) (a b : E) :
    realHessian (c • u) x a b = c * realHessian u x a b := by
  simp [realHessian, iteratedFDeriv_const_smul_apply hu]

@[simp] theorem realHessian_neg (u : E → ℝ) (x a b : E) :
    realHessian (-u) x a b = -realHessian u x a b := by
  simp [realHessian, iteratedFDeriv_neg_apply]

@[simp] theorem realHessian_zero_left (u : E → ℝ) (x b : E) :
    realHessian u x 0 b = 0 := by
  simp [realHessian_eq_fderiv]

@[simp] theorem realHessian_zero_right (u : E → ℝ) (x a : E) :
    realHessian u x a 0 = 0 := by
  simp [realHessian_eq_fderiv]

theorem realHessian_smul_left (u : E → ℝ) (x a b : E) (c : ℝ) :
    realHessian u x (c • a) b = c * realHessian u x a b := by
  simp [realHessian_eq_fderiv]

theorem realHessian_smul_right (u : E → ℝ) (x a b : E) (c : ℝ) :
    realHessian u x a (c • b) = c * realHessian u x a b := by
  simp [realHessian_eq_fderiv]

/-- Translation and linear pullback of the genuine second derivative. -/
theorem realHessian_comp_affine {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (A : F →L[ℝ] E) (x : E) (z a b : F) :
    realHessian (fun y ↦ u (x + A y)) z a b =
      realHessian u (x + A z) (A a) (A b) := by
  have hshift : ContDiff ℝ 2 (fun y : E ↦ u (x + y)) :=
    hu.comp (contDiff_const.add contDiff_id)
  have h := congrArg (fun B ↦ B ![a, b])
    (A.iteratedFDeriv_comp_right hshift z (i := 2) le_rfl)
  have hvec : (fun i ↦ A (![a, b] i)) = ![A a, A b] := by
    ext i
    fin_cases i <;> rfl
  simpa only [realHessian, Function.comp_def,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left, hvec] using h

end RealHessian

section NormSquare

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Hessian of the squared norm is twice the real inner product. -/
theorem realHessian_norm_sq (x a b : H) :
    realHessian (fun y : H ↦ ‖y‖ ^ 2) x a b = 2 * inner ℝ a b := by
  rw [realHessian_eq_fderiv, fderiv_norm_sq,
    fderiv_const_smul (innerSL ℝ).differentiableAt]
  simp
  rfl

end NormSquare

section LeviForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E]

/-- The Levi quadratic form of a real-valued function. -/
def leviForm (u : E → ℝ) (x v : E) : ℝ :=
  (realHessian u x v v + realHessian u x (Complex.I • v) (Complex.I • v)) / 4

@[simp] theorem leviForm_const (c : ℝ) (x v : E) :
    leviForm (fun _ : E ↦ c) x v = 0 := by
  simp [leviForm]

@[simp] theorem leviForm_zero (u : E → ℝ) (x : E) : leviForm u x 0 = 0 := by
  simp [leviForm]

theorem leviForm_add {u v : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a : E) :
    leviForm (u + v) x a = leviForm u x a + leviForm v x a := by
  simp only [leviForm, realHessian_add hu hv]
  ring

theorem leviForm_smul {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (c : ℝ) (a : E) :
    leviForm (c • u) x a = c * leviForm u x a := by
  simp only [leviForm, realHessian_smul hu]
  ring

@[simp] theorem leviForm_neg (u : E → ℝ) (x a : E) :
    leviForm (-u) x a = -leviForm u x a := by
  simp only [leviForm, realHessian_neg]
  ring

variable [IsScalarTower ℝ ℂ E]

/-- Multiplication by a fixed vector, viewed as a real continuous linear map. -/
def complexLineLinear (v : E) : ℂ →L[ℝ] E :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight v).restrictScalars ℝ

@[simp] theorem complexLineLinear_apply (v : E) (z : ℂ) :
    complexLineLinear v z = z • v := rfl

/-- The Hessian chain rule along a complex affine line. -/
theorem realHessian_complexLine {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (x v : E) (z a b : ℂ) :
    realHessian (fun t : ℂ ↦ u (x + t • v)) z a b =
      realHessian u (x + z • v) (a • v) (b • v) := by
  exact realHessian_comp_affine hu (complexLineLinear v) x z a b

/-- The ordinary real Laplacian along a complex line is four times the Levi form. -/
theorem laplacian_complexLine {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (x v : E) (z : ℂ) :
    Δ (fun t : ℂ ↦ u (x + t • v)) z = 4 * leviForm u (x + z • v) v := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  change realHessian (fun t : ℂ ↦ u (x + t • v)) z 1 1 +
    realHessian (fun t : ℂ ↦ u (x + t • v)) z Complex.I Complex.I = _
  rw [realHessian_complexLine hu, realHessian_complexLine hu]
  simp only [one_smul, leviForm]
  ring

theorem laplacian_complexLine_nonneg_iff {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (x v : E) (z : ℂ) :
    0 ≤ Δ (fun t : ℂ ↦ u (x + t • v)) z ↔ 0 ≤ leviForm u (x + z • v) v := by
  rw [laplacian_complexLine hu]
  exact mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 4)

end LeviForm

section NormSquareLevi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E]

/-- The squared norm has positive definite Levi form with this normalization. -/
theorem leviForm_norm_sq (x v : E) :
    leviForm (fun y : E ↦ ‖y‖ ^ 2) x v = ‖v‖ ^ 2 := by
  simp only [leviForm, realHessian_norm_sq, real_inner_self_eq_norm_sq,
    norm_smul, Complex.norm_I, one_mul]
  ring

theorem leviForm_norm_sq_nonneg (x v : E) :
    0 ≤ leviForm (fun y : E ↦ ‖y‖ ^ 2) x v := by
  rw [leviForm_norm_sq]
  positivity

theorem leviForm_norm_sq_pos (x : E) {v : E} (hv : v ≠ 0) :
    0 < leviForm (fun y : E ↦ ‖y‖ ^ 2) x v := by
  rw [leviForm_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hv)

end NormSquareLevi

end SGPT.Foundations.Analysis
