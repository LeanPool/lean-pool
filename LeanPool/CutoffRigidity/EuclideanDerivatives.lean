/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.NormNum

/-! # Gradient and coordinate differentiation on Euclidean space -/

public section

namespace CutoffRigidity

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Continuity of the actual gradient requires only C¹ regularity. -/
theorem continuous_gradient_of_c1 {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) := by
  let R : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact R.continuous.comp ((hf.fderiv_right (m := 0) (by norm_num)).continuous)

/-- Actual differentiation in a standard Euclidean coordinate direction. -/
@[expose] noncomputable def coordinateDerivative (i : Fin d) (f : E → ℝ) (x : E) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- A coordinate derivative of a `C^(n+1)` function is `C^n`. -/
theorem contDiff_coordinateDerivative {n : WithTop ℕ∞} {f : E → ℝ}
    (hf : ContDiff ℝ (n + 1) f) (i : Fin d) :
    ContDiff ℝ n (coordinateDerivative i f) := by
  exact (hf.fderiv_right le_rfl).clm_apply (contDiff_const (c := EuclideanSpace.single i 1))

/-- The first coordinate derivatives of a C² function are genuinely C¹. -/
theorem c1_coordinateDerivative_of_c2 {f : E → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin d) :
    ContDiff ℝ 1 (coordinateDerivative i f) := by
  apply contDiff_coordinateDerivative
  convert hf using 1
  norm_num

/-- C¹ functions have continuous actual coordinate derivatives. -/
theorem continuous_coordinateDerivative_of_c1 {f : E → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin d) :
    Continuous (coordinateDerivative i f) := by
  have h : ContDiff ℝ 0 (coordinateDerivative i f) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  exact h.continuous

/-- Linearity of actual coordinate derivatives on differentiable functions. -/
theorem coordinateDerivative_add_classical {f g : E → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin d) :
    coordinateDerivative i (fun x => f x + g x) =
      fun x => coordinateDerivative i f x + coordinateDerivative i g x := by
  ext x
  simp only [coordinateDerivative, fderiv_fun_add (hf x) (hg x), add_apply]

/-- Scalar linearity of actual coordinate derivatives. -/
theorem coordinateDerivative_smul_classical {f : E → ℝ}
    (hf : Differentiable ℝ f) (r : ℝ) (i : Fin d) :
    coordinateDerivative i (fun x => r * f x) = fun x => r * coordinateDerivative i f x := by
  ext x
  simp only [coordinateDerivative, fderiv_const_mul (hf x), smul_apply, smul_eq_mul]

end CutoffRigidity
