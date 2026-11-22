/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Extra.SplitPotential

/-! # Gaussian splitting and first eigenfunctions -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Bundle
open scoped ENNReal NNReal ContDiff Manifold

namespace CutoffRigidity.Paper

section Riemannian

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- The product splitting and eigenfunction conclusions of the Gaussian splitting theorem. -/
theorem riemannian_gaussian_splitting_base {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : CutCur.IsWeightedVolume F μ V) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hCD : CutCur.CD F ρ V) (hgap : CutCur.mSpectralGap F μ = ρ) :
    let k := CutCur.mFirstEigenDim F μ V
    ∃ (F' : Type) (_ : NormedAddCommGroup F') (_ : InnerProductSpace ℝ F')
      (_ : FiniteDimensional ℝ F') (N : Type) (_ : EMetricSpace N) (_ : ChartedSpace F' N)
      (_ : IsManifold 𝓘(ℝ, F') ∞ N) (_ : RiemannianBundle (fun y : N => TangentSpace 𝓘(ℝ, F') y))
      (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, F') ∞ F' (fun y : N => TangentSpace 𝓘(ℝ, F') y))
      (_ : IsRiemannianManifold 𝓘(ℝ, F') N) (_ : MeasurableSpace F') (_ : BorelSpace F')
      (_ : MeasurableSpace N) (_ : BorelSpace N)
      (V' : N → ℝ) (μ' : Measure N)
      (Φ : M ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, CutCur.Rd k).prod 𝓘(ℝ, F')⟯ CutCur.Rd k × N),
      (ContMDiff 𝓘(ℝ, F') 𝓘(ℝ, ℝ) ∞ V' ∧ IsProbabilityMeasure μ' ∧
        CutCur.IsWeightedVolume F' μ' V' ∧ CutCur.CD F' ρ V') ∧
      (∀ x y, edist x y ^ 2 = edist (Φ x).1 (Φ y).1 ^ 2 + edist (Φ x).2 (Φ y).2 ^ 2) ∧
      μ.map Φ = (multivariateGaussian 0 (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).prod μ' ∧
      (∀ f, CutCur.IsMEigenfunction F μ V ρ f → ∃ a : CutCur.Rd k,
        (∀ x, f x = inner ℝ a (Φ x).1) ∧ ‖a‖ ^ 2 = ρ * ∫ x, f x ^ 2 ∂μ) ∧
      ∀ f g (a b : CutCur.Rd k), CutCur.IsMEigenfunction F μ V ρ f →
        CutCur.IsMEigenfunction F μ V ρ g →
        (∀ x, f x = inner ℝ a (Φ x).1) → (∀ x, g x = inner ℝ b (Φ x).1) →
        ∫ x, f x * g x ∂μ = 0 → inner ℝ a b = 0 := by
  obtain ⟨F', normed, metric, finite, N, distance, charts, smooth, bundle, smoothBundle,
    riemannian, measurableF, borelF, measurableN, borelN, V', μ', Φ,
    ⟨hSmooth, hProb, hVolume, hCurvature, _, _⟩, hDistance, _, hMeasure, hEigen, hOrthogonal⟩ :=
    riemannian_gaussian_splitting F hV hμ hρ hCD hgap
  exact ⟨F', normed, metric, finite, N, distance, charts, smooth, bundle, smoothBundle,
    riemannian, measurableF, borelF, measurableN, borelN, V', μ', Φ,
    ⟨hSmooth, hProb, hVolume, hCurvature⟩, hDistance, hMeasure, hEigen, hOrthogonal⟩

end Riemannian

end CutoffRigidity.Paper
