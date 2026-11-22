/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianParallelFields
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Actual Riemannian gradient, Hessian and Laplacian

The gradient is the Riesz representative of the genuine manifold derivative.
The Hessian is its actual Levi-Civita covariant derivative paired with the
metric. These definitions introduce no Bochner, integration-by-parts or
parallelism hypothesis. This module develops pointwise analytic ingredients;
it does not yet assert the integrated weighted Bochner identity.
-/
@[expose] public section
open Bundle
open scoped Manifold ContDiff
namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]
  [FiniteDimensional ℝ E]

/-- The Riesz gradient of a scalar function for the given Riemannian metric. -/
noncomputable def manifoldGradient (f : M → ℝ) (x : M) : TangentSpace I x :=
  (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm (mvfderiv I f x)

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)] in
theorem inner_manifoldGradient (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    inner ℝ (manifoldGradient I f x) v = mvfderiv I f x v := by
  exact congrArg (fun L : StrongDual ℝ (TangentSpace I x) => L v)
    ((InnerProductSpace.toDual ℝ (TangentSpace I x)).apply_symm_apply (mvfderiv I f x))

/-- The bilinear form given by the covariant derivative of the gradient. -/
noncomputable def manifoldHessian (f : M → ℝ) (x : M)
    (v w : TangentSpace I x) : ℝ :=
  inner ℝ (CovariantDerivative.leviCivitaConnection I M (manifoldGradient I f) x v) w

/-- The metric trace of the Hessian with the divergence-of-gradient sign. -/
noncomputable def manifoldLaplacian (f : M → ℝ) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
    manifoldHessian I f x ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
      ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)

/-- The squared Hilbert–Schmidt norm of the Hessian in an orthonormal basis. -/
noncomputable def manifoldHessianNormSq (f : M → ℝ) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
    ‖CovariantDerivative.leviCivitaConnection I M (manifoldGradient I f) x
      ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)‖^2

/-- The Riemannian Laplacian with drift minus the gradient of the weight potential. -/
noncomputable def manifoldLangevinOperator (V f : M → ℝ) (x : M) : ℝ :=
  manifoldLaplacian I f x-inner ℝ (manifoldGradient I V x) (manifoldGradient I f x)

/-- Actual zero Hessian is exactly actual parallelism of the Riesz gradient. -/
theorem manifoldHessian_eq_zero_iff (f : M → ℝ) (x : M) :
    (∀ v w : TangentSpace I x, manifoldHessian I f x v w=0) ↔
      CovariantDerivative.leviCivitaConnection I M (manifoldGradient I f) x=0 := by
  constructor
  · intro hh
    ext v
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    exact hh v _
  · intro hh v w
    simp [manifoldHessian,hh]

/-- The trace definition is independent of the chosen orthonormal frame. -/
theorem manifoldLaplacian_eq_trace (f : M → ℝ) (x : M) :
    manifoldLaplacian I f x = LinearMap.trace ℝ (TangentSpace I x)
      (CovariantDerivative.leviCivitaConnection I M (manifoldGradient I f) x).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (TangentSpace I x))]
  simp only [manifoldLaplacian,manifoldHessian,real_inner_comm]
  rfl

theorem manifoldHessianNormSq_nonneg (f : M → ℝ) (x : M) :
    0 ≤ manifoldHessianNormSq I f x := by
  apply Finset.sum_nonneg
  intro i hi
  exact sq_nonneg _

/-- Vanishing of the genuine squared Hessian tensor norm forces the actual
Levi-Civita derivative to vanish, without a parallelism premise. -/
theorem manifoldHessianNormSq_eq_zero_iff (f : M → ℝ) (x : M) :
    manifoldHessianNormSq I f x=0 ↔
      CovariantDerivative.leviCivitaConnection I M (manifoldGradient I f) x=0 := by
  let A := CovariantDerivative.leviCivitaConnection I M (manifoldGradient I f) x
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  constructor
  · intro hh
    have hsum : (∑ i, ‖A (b i)‖^2)=0 := hh
    have hbas : ∀ i, A (b i)=0 := by
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖A (b j)‖)).mp hsum i
        (Finset.mem_univ i)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
    apply ContinuousLinearMap.ext
    intro v
    rw [← b.sum_repr v,map_sum]
    change (∑ i, A (b.repr v i • b i)) = 0
    simp only [map_smul,hbas,smul_zero,Finset.sum_const_zero]
  · intro hh
    simp [manifoldHessianNormSq,hh]

/-- The squared tensor norm is the intrinsic trace of A* A, hence independent
of the standard orthonormal basis used to define its finite sum. -/
theorem manifoldHessianNormSq_eq_trace_adjoint (f : M → ℝ) (x : M) :
    manifoldHessianNormSq I f x =
      LinearMap.trace ℝ (TangentSpace I x)
        (((CovariantDerivative.leviCivitaConnection I M (manifoldGradient I f) x).adjoint.comp
          (CovariantDerivative.leviCivitaConnection I M (manifoldGradient I f) x)).toLinearMap) :=
            by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (TangentSpace I x))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,real_inner_self_eq_norm_sq]

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)] in
theorem manifoldGradient_mul {f g : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) :
    manifoldGradient I (f*g) x = f x • manifoldGradient I g x + g x • manifoldGradient I f x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_manifoldGradient,mvfderiv_mul hf hg]
  simp only [add_apply,smul_apply,smul_eq_mul,
    inner_add_left,inner_smul_left,inner_manifoldGradient,starRingEnd_apply,star_trivial]

/-- The genuine first Bochner calculation: the derivative of the gradient's
squared norm is twice Hessian applied to that gradient. The explicit domain
is differentiability of the actual Riesz-gradient section. -/
theorem mvfderiv_manifoldGradient_norm_sq
    {f : M → ℝ} {x : M}
    (hgrad : MDifferentiableAt I I.tangent (T% (manifoldGradient I f)) x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y => ‖manifoldGradient I f y‖^2) x v =
      2*manifoldHessian I f x v (manifoldGradient I f x) := by
  let X : (y : M) → TangentSpace I y := FiberBundle.extend E v
  have hh := (CovariantDerivative.isMetricCompatible_leviCivitaConnection I
    (M := M)).mvfderiv_inner_eq X hgrad hgrad
  have hv : X x=v := by simp [X]
  simp only [hv] at hh
  simp only [real_inner_self_eq_norm_sq] at hh
  rw [hh,manifoldHessian]
  rw [real_inner_comm (manifoldGradient I f x)]
  ring

end CutoffRigidity
