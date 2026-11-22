/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Moments.Variance

/-! # Definitions for Gaussian splitting of weighted Riemannian manifolds -/

open MeasureTheory ProbabilityTheory Set
open scoped ContDiff Manifold

@[expose] public noncomputable section

namespace CutCur

/-- The Euclidean space `ℝ^d`. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

section Riemannian

open Bundle

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- The Riemannian gradient: the Riesz representative of the differential. -/
def mgrad (f : M → ℝ) (x : M) : TangentSpace 𝓘(ℝ, F) x := (InnerProductSpace.toDual ℝ
  (TangentSpace 𝓘(ℝ, F) x)).symm (mvfderiv 𝓘(ℝ, F) f x)

/-- The Laplace–Beltrami operator: the trace of the Levi-Civita Hessian `∇(grad f)`. -/
def mlaplacian (f : M → ℝ) (x : M) : ℝ := ∑ i, inner ℝ (CovariantDerivative.leviCivitaConnection
  𝓘(ℝ, F) M (mgrad F f) x
  (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)) (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F)
    x) i)

/-- The generator (1.27) `𝓛f = Δf - ⟨∇V, ∇f⟩`. -/
def mgenerator (V f : M → ℝ) (x : M) : ℝ := mlaplacian F f x - inner ℝ (mgrad F V x) (mgrad F f x)

/-- The carré du champ `Γ(f,g) = ⟨∇f, ∇g⟩`. -/
def carre (f g : M → ℝ) (x : M) : ℝ := inner ℝ (mgrad F f x) (mgrad F g x)

/-- The iterated carré du champ `Γ₂(f) = ½ 𝓛Γ(f,f) - Γ(f, 𝓛f)`. -/
def carre2 (V f : M → ℝ) (x : M) : ℝ := mgenerator F V (carre F f f) x / 2 - carre F f (mgenerator
  F V f) x

/-- The Bakry–Émery curvature-dimension condition `CD(ρ,∞)`: `Γ₂(f) ≥ ρ Γ(f)` for every smooth `f`
  (equivalently `Ric + Hess V ≥ ρ g`). -/
def CD (ρ : ℝ) (V : M → ℝ) : Prop := ∀ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f → ∀ x, ρ * carre F
  f f x ≤ carre2 F V f x

/-- The Riemannian volume density `√det(gᵢⱼ)` of the inverse of the chart at `x₀`, at the chart
  point `z`, computed in an orthonormal basis of the model space. -/
def chartVolumeDensity (x₀ : M) (z : F) : ℝ := Real.sqrt (Matrix.det (Matrix.of fun i j =>
  inner ℝ (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (chartAt F x₀).symm z (stdOrthonormalBasis ℝ F i) :
    TangentSpace 𝓘(ℝ, F) ((chartAt F x₀).symm z))
  (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (chartAt F x₀).symm z (stdOrthonormalBasis ℝ F j))))

/-- `μ = e^{-V} vol_g`: in every chart, `μ` has density `e^{-V} √det(gᵢⱼ)` with respect to
  Lebesgue measure. -/
def IsWeightedVolume [MeasurableSpace M] (μ : Measure M) (V : M → ℝ) : Prop := ∀ x₀ : M,
  (μ.restrict (chartAt F x₀).source).map (chartAt F x₀) =
  (volume.restrict (chartAt F x₀).target).withDensity fun z => ENNReal.ofReal (Real.exp (-V
    ((chartAt F x₀).symm z)) * chartVolumeDensity F x₀ z)

/-- The spectral gap of `-𝓛` in `L²(μ)` (optimal Poincaré constant over smooth compactly supported
  test functions). -/
def mSpectralGap [MeasurableSpace M] (μ : Measure M) : ℝ := sInf {r : ℝ | ∃ f : M → ℝ, ContMDiff
  𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧ HasCompactSupport f ∧
  0 < variance f μ ∧ r = (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ}

/-- Smooth `L²(μ)` eigenfunctions of `-𝓛` with eigenvalue `lam`. -/
def IsMEigenfunction [MeasurableSpace M] (μ : Measure M) (V : M → ℝ) (lam : ℝ) (f : M → ℝ) : Prop :=
  ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧ MemLp f 2 μ ∧ ∀ x, mgenerator F V f x = -lam * f x

/-- `k₁ = dim E₁`, `E₁ ⊆ L²(μ)` the eigenspace of `-𝓛` for `λ₁`. -/
def mFirstEigenDim [MeasurableSpace M] (μ : Measure M) (V : M → ℝ) : ℕ := Module.finrank ℝ
  (Submodule.span ℝ
  {u : M →₂[μ] ℝ | ∃ f, IsMEigenfunction F μ V (mSpectralGap F μ) f ∧ f =ᵐ[μ] u})

end Riemannian

end CutCur
