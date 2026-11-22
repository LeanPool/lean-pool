/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Ring
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.Analysis.Matrix.Normed

/-! # Jacobi's formula for Gram determinants

The derivative of a determinant at the identity is the trace of the derivative. For a family of
bilinear forms `β z`, orthonormal at `z` along a family `f`, this gives the derivative of the Gram
determinant along any family `e = Q f`, and of its square root (the Riemannian volume density).
-/

@[expose] public section

open scoped Matrix.Norms.Operator

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Jacobi's formula at the identity: if `N z = 1`, then `d(det N) = tr dN`. -/
theorem hasFDerivAt_det_of_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {N : E → Matrix n n ℝ} {N' : n → n → E →L[ℝ] ℝ} {z : E}
    (hN : ∀ i j, HasFDerivAt (fun x => N x i j) (N' i j) z) (h1 : N z = 1) :
    HasFDerivAt (fun x => (N x).det) (∑ i, N' i i) z := by
  let derivative : E →L[ℝ] n → n → ℝ :=
    ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.pi (N' i))
  have hEntries : HasFDerivAt (fun x i j ↦ N x i j) derivative z :=
    hasFDerivAt_pi.mpr fun i ↦ hasFDerivAt_pi.mpr (hN i)
  let toMatrix : (n → n → ℝ) ≃L[ℝ] Matrix n n ℝ := Matrix.ofContinuousLinearEquiv ℝ
  have hToMatrix : (toMatrix : (n → n → ℝ) → Matrix n n ℝ) = Matrix.of :=
    Matrix.coe_ofContinuousLinearEquiv ℝ
  have hValue (x : E) : toMatrix (fun i j ↦ N x i j) = N x := by
    refine (congrFun hToMatrix _).trans ?_
    ext i j
    rfl
  have hMatrix : HasFDerivAt N (toMatrix.toContinuousLinearMap.comp derivative) z :=
    (toMatrix.hasFDerivAt.comp z hEntries).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x ↦ (hValue x).symm)
  have hDet := Matrix.hasFDerivAt_det_one (n := n) (𝕜 := ℝ)
  rw [← h1] at hDet
  exact (hDet.comp z hMatrix).congr_fderiv (by
    ext v
    change Matrix.trace (toMatrix (derivative v)) = _
    rw [hToMatrix, sum_apply]
    rfl)

/-- Derivative of a bilinear-form-valued map evaluated at fixed vectors. -/
theorem hasFDerivAt_bilin_apply_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {β : E → F →L[ℝ] F →L[ℝ] ℝ} {z : E} (hβ : DifferentiableAt ℝ β z) (a b : F) :
    HasFDerivAt (fun x => β x a b)
      ((ContinuousLinearMap.apply ℝ ℝ b).comp
        ((ContinuousLinearMap.apply ℝ (F →L[ℝ] ℝ) a).comp (fderiv ℝ β z))) z := by
  have h := (hβ.hasFDerivAt.clm_apply (hasFDerivAt_const a z)).clm_apply (hasFDerivAt_const b z)
  convert h using 1
  ext w
  simp

/-- Jacobi's formula for a Gram determinant: if the forms `β z` are orthonormal along `f` at `z`
and `e = Q f`, then `d(det (β (e j) (e k)))[w] = det · Σₗ dβ[w](f l, f l)`. -/
theorem hasFDerivAt_det_gram {n : Type*} [Fintype n] [DecidableEq n] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {β : E → F →L[ℝ] F →L[ℝ] ℝ} {z : E} (hβ : DifferentiableAt ℝ β z)
    (e f : n → F) (Q : Matrix n n ℝ) (he : ∀ j, e j = ∑ l, Q j l • f l)
    (hf : ∀ l m, β z (f l) (f m) = if l = m then 1 else 0) :
    HasFDerivAt (fun x => (Matrix.of fun j k => β x (e j) (e k)).det)
      ((Matrix.of fun j k => β z (e j) (e k)).det •
        ∑ l, (ContinuousLinearMap.apply ℝ ℝ (f l)).comp
          ((ContinuousLinearMap.apply ℝ (F →L[ℝ] ℝ) (f l)).comp (fderiv ℝ β z))) z := by
  set Gf : E → Matrix n n ℝ := fun x => Matrix.of fun l m => β x (f l) (f m) with hGf
  have hgram : ∀ x, (Matrix.of fun j k => β x (e j) (e k)) = Q * Gf x * Q.transpose := by
    intro x
    ext j k
    simp only [Matrix.of_apply, he, map_sum, map_smul, FunLike.coe_sum,
      Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.transpose_apply, hGf]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hdet : ∀ x, (Matrix.of fun j k => β x (e j) (e k)).det = Q.det ^ 2 * (Gf x).det := by
    intro x
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hone : Gf z = 1 := by
    ext l m
    simp [hGf, hf, Matrix.one_apply]
  have hJ := (hasFDerivAt_det_of_eq_one (fun l m => hasFDerivAt_bilin_apply_const hβ (f l) (f m))
    hone).const_mul (Q.det ^ 2)
  have hfun : (fun x => (Matrix.of fun j k => β x (e j) (e k)).det) =
      fun x => Q.det ^ 2 * (Gf x).det := funext hdet
  rw [hfun]
  refine hJ.congr_fderiv ?_
  rw [hdet, hone, Matrix.det_one, mul_one]

end CutoffRigidity
