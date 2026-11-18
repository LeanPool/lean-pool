/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.LocalInverse
public import LeanPool.KLS.FunctionalInequalities.Analysis.ContinuousHessian
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Regularity
public import Mathlib.LinearAlgebra.Determinant

/-!
# The inverse of the gradient of a strictly convex function

If `hessianMatrix u x` is positive definite, the derivative of `∇u` at `x` is an isomorphism whose
standard-basis matrix is the
transpose of `hessianMatrix u x`. For `C^{k+1}` strictly convex `u`, `k ≠ 0`, with positive definite
Hessian everywhere, `invFun ∇u`
is `C^k` on the range of `∇u`, and `D(invFun ∇u)(∇u x) ∘ D∇u(x) = id`. Regularity of the inverse
needs one more derivative of `u`;
no regularity of `u` is bootstrapped.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis

section DerivativeIsomorphism

open Set Function FunctionalInequalities
open scoped Topology RealInnerProductSpace

/--
If `hessianMatrix u x` is positive definite, the derivative of `∇u` at `x` is a continuous linear
isomorphism. In the
standard basis its matrix is the transpose of `hessianMatrix u x` (by
`hessian_coordinate_gradient_fderiv`), so its
determinant is positive. -/
theorem exists_gradient_deriv_equiv_of_posDef {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hp : (Probability.Stein.hessianMatrix u x).PosDef) :
    ∃ A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = fderiv ℝ (gradient u) x := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let J := fderiv ℝ (gradient u) x
  have hm :
    LinearMap.toMatrix b b J.toLinearMap = (Probability.Stein.hessianMatrix u x).transpose := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change (J (EuclideanSpace.basisFun (Fin n) ℝ j)) i = Probability.Stein.hessianMatrix u x j i
    exact (Analysis.hessian_coordinate_gradient_fderiv u x j i).symm
  have hd : J.det ≠ 0 := by
    change LinearMap.det J.toLinearMap ≠ 0
    rw [← LinearMap.det_toMatrix b, hm, Matrix.det_transpose]
    exact hp.det_pos.ne'
  exact ⟨J.toContinuousLinearEquivOfDetNeZero hd, rfl⟩

/-- A `C^{k+1}` function has a `C^k` gradient. -/
theorem contDiff_gradient_of_contDiff_succ {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {k : WithTop ℕ∞} {u : E → ℝ}
    (hu : ContDiff ℝ (k + 1) u) : ContDiff ℝ k (gradient u) := by
  exact
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hu.fderiv_right le_rfl)

/--
If `u` is `C^{k+1}`, `k ≠ 0`, strictly convex and has a positive definite Hessian everywhere, then
`invFun ∇u` is `C^k`
on the range of `∇u`. `C^k` regularity of the inverse requires `C^{k+1}` regularity of `u`; nothing
is bootstrapped. -/
theorem contDiffOn_invFun_gradient_of_posDef {n : ℕ} {k : WithTop ℕ∞} (hk : k ≠ 0)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ (k + 1) u)
    (hs : StrictConvexOn ℝ univ u) (hp : ∀ x, (Probability.Stein.hessianMatrix u x).PosDef) :
    ContDiffOn ℝ k (invFun (gradient u)) (range (gradient u)) := by
  have hg := contDiff_gradient_of_contDiff_succ hu
  have hi := Analysis.injective_gradient_of_strictConvexOn (hu.differentiable (by simp)) hs
  choose A hA using fun x => exists_gradient_deriv_equiv_of_posDef u x (hp x)
  apply contDiffOn_invFun_of_injective_of_hasFDerivAt_equiv hk hg hi A
  intro x
  rw [hA x]
  exact (hg.differentiable hk x).hasFDerivAt

end DerivativeIsomorphism

section InverseDerivative

open Set Function Filter FunctionalInequalities
open scoped Topology

/--
For a `C²` strictly convex `u` with positive definite Hessian at `x`, `D(invFun ∇u)(∇u x) ∘ D∇u(x) =
id`. -/
theorem fderiv_invFun_gradient_comp_fderiv {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) (hs : StrictConvexOn ℝ univ u) (x : EuclideanSpace ℝ (Fin n))
    (hp : (Probability.Stein.hessianMatrix u x).PosDef) :
    (fderiv ℝ (invFun (gradient u)) (gradient u x)).comp (fderiv ℝ (gradient u) x) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  have hg : ContDiff ℝ 1 (gradient u) := contDiff_gradient_of_contDiff_succ hu
  have hi := Analysis.injective_gradient_of_strictConvexOn (hu.differentiable (by norm_num)) hs
  obtain ⟨A, hA⟩ := exists_gradient_deriv_equiv_of_posDef u x hp
  have hd :
    HasFDerivAt (gradient u) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) x := by
    rw [hA]
    exact (hg.differentiable (by norm_num) x).hasFDerivAt
  have hv := hasFDerivAt_invFun_of_injective hg.contDiffAt hi A hd
  rw [hv.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  change A.symm (fderiv ℝ (gradient u) x v) = v
  rw [← hA]
  exact A.symm_apply_apply v

end InverseDerivative

end FunctionalInequalities.Analysis
