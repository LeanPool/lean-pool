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

/-! # Jacobi's formula for Gram determinants

The derivative of a determinant at the identity is the trace of the derivative. For a family of
bilinear forms `β z`, orthonormal at `z` along a family `f`, this gives the derivative of the Gram
determinant along any family `e = Q f`, and of its square root (the Riemannian volume density).
-/

@[expose] public section

open Finset Equiv

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Jacobi's formula at the identity: if `N z = 1`, then `d(det N) = tr dN`. -/
theorem hasFDerivAt_det_of_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {N : E → Matrix n n ℝ} {N' : n → n → E →L[ℝ] ℝ} {z : E}
    (hN : ∀ i j, HasFDerivAt (fun x => N x i j) (N' i j) z) (h1 : N z = 1) :
    HasFDerivAt (fun x => (N x).det) (∑ i, N' i i) z := by
  have hfun : (fun x => (N x).det) =
      fun x => ∑ σ : Perm n, ((Perm.sign σ : ℤ) : ℝ) * ∏ i, N x (σ i) i := by
    funext x
    exact Matrix.det_apply' (N x)
  rw [hfun]
  have hd := HasFDerivAt.fun_sum (u := (univ : Finset (Perm n)))
    (fun σ _ => ((HasFDerivAt.finsetProd (u := univ)
      (fun i _ => hN (σ i) i)).const_mul ((Perm.sign σ : ℤ) : ℝ)))
  convert hd using 1
  rw [Finset.sum_eq_single (1 : Perm n)]
  · simp [h1]
  · intro σ _ hσ
    rw [Finset.sum_eq_zero]
    · simp
    intro k _
    by_cases hfix : ∀ j, j ≠ k → σ j = j
    · exfalso
      apply hσ
      ext j
      by_cases hjk : j = k
      · subst hjk
        by_contra hne
        have h2 := hfix (σ j) hne
        exact hne (σ.injective h2)
      · simpa using hfix j hjk
    · push Not at hfix
      obtain ⟨j, hjk, hj⟩ := hfix
      rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨hjk, mem_univ j⟩)]
      · simp
      · simp [h1, hj]
  · intro h
    exact absurd (mem_univ _) h

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
