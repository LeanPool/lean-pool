/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Tactic

/-!
# Affine rigidity from a vanishing Hessian

The Euclidean rigidity argument of Section 1.6 and Lemma `lem_rig` in
`cutcur-lean.tex` uses that a function with identically vanishing Hessian is
affine. Here the Hessian is the actual Fréchet derivative of the actual
Fréchet derivative, with explicit differentiability assumptions. The proof
uses the mean value theorem twice: first the derivative is constant, and
then the function agrees with its affine linearization at zero.

The Bochner argument that forces this Hessian to vanish is not established
by this file.
-/

public section

namespace CutoffRigidity

/-- A vanishing second Fréchet derivative makes the first derivative constant. -/
theorem fderiv_eq_fderiv_zero_of_second_fderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hfderiv : Differentiable ℝ (fderiv ℝ f))
    (hHess : ∀ x, fderiv ℝ (fderiv ℝ f) x = 0) (x : E) :
    fderiv ℝ f x = fderiv ℝ f 0 :=
  is_const_of_fderiv_eq_zero hfderiv hHess x 0

/-- A differentiable function with constant derivative equals its affine
linearization at zero, by the mean value theorem. -/
theorem eq_affine_of_constant_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {L : E →L[ℝ] ℝ} (hf : Differentiable ℝ f)
    (hderiv : ∀ x, fderiv ℝ f x = L) (x : E) :
    f x = f 0 + L x := by
  have heq : f = fun y => f 0 + L y := by
    apply eq_of_fderiv_eq hf (L.differentiable.const_add (f 0))
      (fun y => by rw [fderiv_const_add, L.fderiv, hderiv y]) 0
    simp
  exact congrFun heq x

/-- A twice differentiable function with zero Hessian is affine. -/
theorem eq_affine_of_second_fderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : Differentiable ℝ f)
    (hfderiv : Differentiable ℝ (fderiv ℝ f))
    (hHess : ∀ x, fderiv ℝ (fderiv ℝ f) x = 0) (x : E) :
    f x = f 0 + fderiv ℝ f 0 x := by
  apply eq_affine_of_constant_fderiv hf
  exact fderiv_eq_fderiv_zero_of_second_fderiv_eq_zero hfderiv hHess

/-- The Euclidean `C²` version of the zero-Hessian affine rigidity step. -/
theorem eq_affine_of_contDiff_two_of_hessian_zero
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hHess : ∀ x, fderiv ℝ (fderiv ℝ f) x = 0)
    (x : EuclideanSpace ℝ (Fin d)) :
    f x = f 0 + fderiv ℝ f 0 x := by
  exact eq_affine_of_second_fderiv_eq_zero (hf.differentiable (by norm_num))
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) hHess x

/-- The same affine representation written using the actual Euclidean gradient,
as in the paper's description of affine eigenfunctions. -/
theorem eq_affine_inner_gradient_of_contDiff_two_of_hessian_zero
    {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hHess : ∀ x, fderiv ℝ (fderiv ℝ f) x = 0)
    (x : EuclideanSpace ℝ (Fin d)) :
    f x = f 0 + inner ℝ (gradient f 0) x := by
  rw [inner_gradient_left]
  exact eq_affine_of_contDiff_two_of_hessian_zero hf hHess x

end CutoffRigidity
