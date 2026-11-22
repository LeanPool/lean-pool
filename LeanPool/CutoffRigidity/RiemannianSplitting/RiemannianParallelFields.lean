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

These are genuine tangent-bundle calculations used in the proof of `lem_rig`.
Parallelism is vanishing of the actual covariant derivative, rather than an
assumed product decomposition. Metric compatibility makes Gram functions
constant along integral curves; torsion freeness makes parallel fields commute.
For a gradient field, a global integral curve consequently meets the zero
level exactly once. Existence of global curves and the product isometry are
separate obligations, not conclusions of this module.
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

/-- Gram functions of parallel fields are constant along every actual integral
curve, with no assumption of an existing splitting. -/
theorem inner_parallel_integralCurve
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X Y Z : (x : M) → TangentSpace I x}
    (hX : MDifferentiable I I.tangent (T% X))
    (hY : MDifferentiable I I.tangent (T% Y))
    (hpX : ∀ x, cov X x = 0) (hpY : ∀ x, cov Y x = 0)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ Z) (t : ℝ) :
    inner ℝ (X (γ t)) (Y (γ t)) = inner ℝ (X (γ 0)) (Y (γ 0)) := by
  have hf : MDifferentiable I 𝓘(ℝ, ℝ) (fun y ↦ inner ℝ (X y) (Y y)) :=
    fun y ↦ MDifferentiableAt.inner_bundle (E := TangentSpace I) (hX y) (hY y)
  simpa using scalar_integralCurve_eq_add hγ hf
    (fun x ↦ mvfderiv_inner_parallel_eq_zero cov hcov hX hY hpX hpY x (Z x)) t

/-- A parallel gradient grows linearly along its actual global integral curve.
The gradient hypothesis is the intrinsic Riesz characterization of `df`. -/
theorem parallel_gradient_integralCurve_eq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X : (x : M) → TangentSpace I x}
    (hX : MDifferentiable I I.tangent (T% X)) (hpX : ∀ x, cov X x = 0)
    {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ X) (t : ℝ) :
    f (γ t) = f (γ 0) + ‖X (γ 0)‖ ^ 2 * t := by
  have hnorm (s : ℝ) : inner ℝ (X (γ s)) (X (γ s)) = ‖X (γ 0)‖ ^ 2 := by
    rw [inner_parallel_integralCurve cov hcov hX hX hpX hpX hγ s,
      real_inner_self_eq_norm_sq]
  have hd : ∀ s, HasDerivAt (fun r ↦ f (γ r) - ‖X (γ 0)‖ ^ 2 * r) 0 s := by
    intro s
    have hs := hasDerivAt_scalar_integralCurve hγ hf s
    rw [hgrad, hnorm] at hs
    convert! hs.sub ((hasDerivAt_id s).const_mul (‖X (γ 0)‖ ^ 2)) using 1; simp
  have he := is_const_of_deriv_eq_zero
    (fun s ↦ (hd s).differentiableAt) (fun s ↦ (hd s).deriv) t 0
  simpa using (sub_eq_iff_eq_add.mp he)

/-- Every globally defined flow line of a nonzero parallel gradient meets the
zero level exactly once. Global existence is not an assumption of splitting. -/
theorem parallel_gradient_integralCurve_unique_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    {X : (x : M) → TangentSpace I x}
    (hX : MDifferentiable I I.tangent (T% X)) (hpX : ∀ x, cov X x = 0)
    {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ X) (hne : X (γ 0) ≠ 0) :
    ∃! t : ℝ, f (γ t) = 0 := by
  have hc : 0 < ‖X (γ 0)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have he := parallel_gradient_integralCurve_eq cov hcov hX hpX hf hgrad hγ
  refine ⟨-f (γ 0) / ‖X (γ 0)‖ ^ 2, ?_, ?_⟩
  · change f (γ (-f (γ 0) / ‖X (γ 0)‖ ^ 2)) = 0
    rw [he (-f (γ 0) / ‖X (γ 0)‖ ^ 2)]
    field_simp
    ring
  · intro t ht
    rw [he t] at ht
    apply (eq_div_iff (ne_of_gt hc)).mpr
    linarith

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- Parallel vector fields commute for the actual Levi-Civita connection. -/
theorem mlieBracket_parallel_eq_zero
    {X Y : (x : M) → TangentSpace I x}
    (hX : MDifferentiable I I.tangent (T% X))
    (hY : MDifferentiable I I.tangent (T% Y))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    (hpY : ∀ x, CovariantDerivative.leviCivitaConnection I M Y x = 0) :
    VectorField.mlieBracket I X Y = 0 := by
  funext x
  have h := (CovariantDerivative.torsion_eq_zero_iff _).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)
    (hX x) (hY x)
  simpa [hpX, hpY] using h.symm

end CutoffRigidity
