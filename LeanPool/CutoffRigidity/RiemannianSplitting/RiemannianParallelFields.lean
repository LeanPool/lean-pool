/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Parallel fields in the Riemannian splitting argument

A constant directional derivative gives linear growth along integral curves.
Metric compatibility and parallelism make the differential of the pointwise Gram function vanish.
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff


namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The ordinary scalar chain rule along an actual manifold integral curve. -/
theorem hasDerivAt_scalar_integralCurve
    {X : (x : M) → TangentSpace I x} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ X) {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ, ℝ) f) (t : ℝ) :
    HasDerivAt (fun s ↦ f (γ s)) (mvfderiv I f (γ t) (X (γ t))) t := by
  have h := ((hf (γ t)).hasMFDerivAt.comp t (hγ t)).hasFDerivAt
  convert! h.hasDerivAt using 1
  change (mfderiv I 𝓘(ℝ, ℝ) f (γ t)) (X (γ t)) =
    (mfderiv I 𝓘(ℝ, ℝ) f (γ t)) ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)) 1)
  simp

/-- A scalar function with constant directional derivative grows linearly along
an actual globally defined integral curve. -/
theorem scalar_integralCurve_eq_add
    {X : (x : M) → TangentSpace I x} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ X) {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ, ℝ) f) {c : ℝ}
    (hc : ∀ x, mvfderiv I f x (X x) = c) (t : ℝ) :
    f (γ t) = f (γ 0) + c * t := by
  have hd : ∀ s, HasDerivAt (fun r ↦ f (γ r) - c * r) 0 s := by
    intro s
    have hs := hasDerivAt_scalar_integralCurve hγ hf s
    rw [hc] at hs
    convert! hs.sub ((hasDerivAt_id s).const_mul c) using 1; simp
  have he := is_const_of_deriv_eq_zero
    (fun s ↦ (hd s).differentiableAt) (fun s ↦ (hd s).deriv) t 0
  simpa using (sub_eq_iff_eq_add.mp he)

variable [IsManifold I 2 M]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [FiniteDimensional ℝ E]

/-- Metric compatibility and actual parallelism force the differential of the
pointwise Gram function to vanish in every tangent direction. -/
theorem mvfderiv_inner_parallel_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X Y : (x : M) → TangentSpace I x}
    (hX : MDifferentiable I I.tangent (T% X))
    (hY : MDifferentiable I I.tangent (T% Y))
    (hpX : ∀ x, cov X x = 0) (hpY : ∀ x, cov Y x = 0)
    (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ inner ℝ (X y) (Y y)) x v = 0 := by
  let Z : (y : M) → TangentSpace I y := FiberBundle.extend E v
  have h := hcov.mvfderiv_inner_eq Z (hX x) (hY x)
  simpa [Z, hpX, hpY] using h

end CutoffRigidity
