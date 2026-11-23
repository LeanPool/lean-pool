/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Statements
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianDifferentialOperators

/-! # Workstream A interface: the three geometric inputs of the rigidity argument

`WeightedIBP`, `WeightedBochnerIneq` and `WeightedCutoffs` are the three geometric statements
(integration by parts for `μ = e^{-V} vol`, the curvature-dimension consequence
`Γ₂ ≥ ‖Hess‖² + ρ Γ`, and existence of smooth cutoffs on a complete manifold) from which the
rigidity of first eigenfunctions is deduced in `CutoffRigidity.Riemann.WeightedRigidity`.
They are stated for the Challenge objects `mgrad`, `carre`, `carre2`, `mgenerator`.
-/

@[expose] public section

open Bundle MeasureTheory Filter
open scoped Manifold ContDiff ENNReal Topology

namespace CutCur

section Interface

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- Squared Hilbert–Schmidt norm of the Levi-Civita Hessian `∇ ∇ f` at `x`
(`∑ᵢ ‖∇_{eᵢ} ∇f‖²` in an orthonormal basis). -/
noncomputable def mHessNormSq (f : M → ℝ) (x : M) : ℝ :=
  CutoffRigidity.manifoldHessianNormSq 𝓘(ℝ, F) f x

/-- Smoothness of a real function on `M`. -/
abbrev MSmooth (f : M → ℝ) : Prop := ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- The gradient pairs with a tangent vector by applying the manifold derivative. -/
theorem mgrad_inner (f : M → ℝ) (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    inner ℝ (mgrad F f x) v = mvfderiv 𝓘(ℝ, F) f x v :=
  TauCeti.Manifold.inner_mgradient v

/-- **(G1) Integration by parts** for the weighted measure: `∫ Γ(u,v) dμ = -∫ u 𝓛v dμ` whenever
`u, v` are smooth and `u` has compact support. -/
def WeightedIBP [MeasurableSpace M] (μ : Measure M) (V : M → ℝ) : Prop :=
  ∀ u v : M → ℝ, MSmooth F u → MSmooth F v → HasCompactSupport u →
    ∫ x, carre F u v x ∂μ = -∫ x, u x * mgenerator F V v x ∂μ

/-- **(G2) Bochner inequality** consequence of `CD(ρ,∞)`: `Γ₂(f) ≥ ‖Hess f‖² + ρ Γ(f)`. -/
def WeightedBochnerIneq (V : M → ℝ) (ρ : ℝ) : Prop :=
  ∀ f : M → ℝ, MSmooth F f → ∀ x, mHessNormSq F f x + ρ * carre F f f x ≤ carre2 F V f x

/-- **(G0) Regularity** of the Challenge operators on smooth functions: `Γ(f,g)` and `𝓛f` are
smooth and the Hessian norm is continuous. -/
def WeightedRegular (V : M → ℝ) : Prop :=
  (∀ f g : M → ℝ, MSmooth F f → MSmooth F g → MSmooth F (carre F f g)) ∧
  (∀ f : M → ℝ, MSmooth F f → MSmooth F (mgenerator F V f)) ∧
  (∀ f : M → ℝ, MSmooth F f → Continuous (mHessNormSq F f))

/-- **(G3) Cutoffs**: smooth compactly supported `[0,1]`-valued functions with gradient norm
at most `1/(n+1)`, eventually equal to `1` at every point. -/
def WeightedCutoffs (M : Type) [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)] : Prop :=
  ∃ χ : ℕ → M → ℝ, (∀ n, MSmooth F (χ n) ∧ HasCompactSupport (χ n) ∧
      ∀ x, 0 ≤ χ n x ∧ χ n x ≤ 1 ∧ ‖mgrad F (χ n) x‖ ≤ 1 / ((n : ℝ) + 1)) ∧
    ∀ x, ∀ᶠ n in atTop, χ n x = 1

end Interface

end CutCur
