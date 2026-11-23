/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianDifferentialOperators

/-! # Genuine gradient/Hessian calculus in the source smooth domain

Gradient differentiability is derived from C² functions and the actual metric.
The finite squared tensor norm is the sum of squares of all Hessian entries.
-/
@[expose] public section
open Bundle
open scoped Manifold ContDiff
namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]

/-- The first Bochner derivative identity with all gradient-regularity
obligations derived from the source scalar C² assumption. -/
theorem mvfderiv_manifoldGradient_norm_sq_of_C2 {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y => ‖manifoldGradient I f y‖^2) x v =
      2*manifoldHessian I f x v (manifoldGradient I f x) :=
  mvfderiv_manifoldGradient_norm_sq I
    ((contMDiff_manifoldGradient hf x).mdifferentiableAt one_ne_zero) v

/-- The squared Hessian norm is the sum of squared pairings in any orthonormal basis. -/
theorem manifoldHessianNormSq_eq_sum_sq {ι : Type*} [Fintype ι] (f : M → ℝ) (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    manifoldHessianNormSq I f x = ∑ i, ∑ j, (manifoldHessian I f x (b i) (b j)) ^ 2 := by
  rw [manifoldHessianNormSq_eq_trace_adjoint, LinearMap.trace_eq_sum_inner _ b]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  exact Finset.sum_congr rfl (fun i _ ↦ (b.sum_sq_inner_left _).symm)

end CutoffRigidity
