/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Hessian curvature gives a strongly monotone gradient

For the actual `C²` potential in `cutcur-lean.tex`, the lower bound
`Hess V ≥ ρ I` implies strong monotonicity of the actual gradient. This is the
curvature input for the synchronous-coupling upper Wasserstein estimate.

The proof restricts the gradient to the line joining two points, subtracts
its linear curvature contribution, and uses the scalar mean value theorem.
The relation between the derivative of the gradient and the second Fréchet
derivative is proved through the actual Riesz representation map.
-/

public section

namespace CutoffRigidity

/-- A lower bound on the symmetric quadratic part of the derivative makes
an actual differentiable vector field strongly monotone. -/
theorem strongly_monotone_of_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : E → E} (hG : Differentiable ℝ G) (rate : ℝ)
    (hbound : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ inner ℝ (fderiv ℝ G x z) z)
    (x y : E) :
    rate * ‖x - y‖ ^ 2 ≤ inner ℝ (G x - G y) (x - y) := by
  let z := x - y
  let F : ℝ → ℝ := fun s => inner ℝ (G (y + s • z)) z - rate * s * ‖z‖ ^ 2
  have hFd (s : ℝ) : HasDerivAt F
      (inner ℝ (fderiv ℝ G (y + s • z) z) z - rate * ‖z‖ ^ 2) s := by
    have hline : HasDerivAt (fun u : ℝ => y + u • z) z s := by
      simpa using ((hasDerivAt_id s).smul_const z).const_add y
    have hcomp := (hG (y + s • z)).hasFDerivAt.comp_hasDerivAt s hline
    have hinner := hcomp.inner ℝ (hasDerivAt_const s z)
    have hlinear : HasDerivAt (fun u : ℝ => rate * u * ‖z‖ ^ 2)
        (rate * ‖z‖ ^ 2) s := by
      simpa using ((hasDerivAt_id s).const_mul rate).mul_const (‖z‖ ^ 2)
    convert hinner.sub hlinear using 1
    · rfl
    · simp only [inner_zero_right, zero_add]
  have hmono : Monotone F := monotone_of_hasDerivAt_nonneg hFd fun s =>
    sub_nonneg.mpr (hbound (y + s • z) z)
  have h := hmono (show (0 : ℝ) ≤ 1 by norm_num)
  have hxy : y + z = x := by simp [z]
  simp only [F, zero_smul, add_zero, mul_zero, zero_mul, sub_zero, one_smul,
    hxy, mul_one] at h
  rw [inner_sub_left]
  dsimp [z] at h ⊢
  linarith

/-- A `C²` scalar potential has a differentiable actual Hilbert-space gradient. -/
theorem differentiable_gradient_of_contDiff_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) : Differentiable ℝ (gradient V) := by
  have hderiv : Differentiable ℝ (fderiv ℝ V) :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    |>.differentiable.comp hderiv

/-- Differentiating the actual Riesz representation of the gradient identifies
its quadratic derivative with the actual Hessian quadratic form. -/
theorem inner_fderiv_gradient_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {V : E → ℝ} {x z : E} (hV' : DifferentiableAt ℝ (fderiv ℝ V) x) :
    inner ℝ (fderiv ℝ (gradient V) x z) z = fderiv ℝ (fderiv ℝ V) x z z := by
  let R : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have heq : gradient V = fun y => R (fderiv ℝ V y) := rfl
  rw [heq, fderiv_fun_comp x R.differentiableAt hV', R.fderiv]
  change inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fderiv ℝ V) x z)) z = _
  exact InnerProductSpace.toDual_symm_apply

/-- The actual Hessian lower bound `Hess V ≥ rate I` implies strong
monotonicity of the actual gradient. This discharges the deterministic
curvature input of synchronous contraction for `C²` potentials. -/
theorem gradient_strongly_monotone_of_hessian_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x y : E) :
    rate * ‖x - y‖ ^ 2 ≤ inner ℝ (gradient V x - gradient V y) (x - y) := by
  apply strongly_monotone_of_derivative_bound (differentiable_gradient_of_contDiff_two hV) rate
  intro u z
  rw [inner_fderiv_gradient_apply
    (((hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) u)]
  exact hHess u z

end CutoffRigidity
