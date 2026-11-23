/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Parallel fields in the Riemannian splitting argument

A constant directional derivative gives linear growth along integral curves.
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

end CutoffRigidity
