/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

module

public import LeanPool.CutoffRigidity.GaussianTransport.LowerBound
public import LeanPool.CutoffRigidity.RiemannianSplitting.Extra.SplitPotential

/-! # Quadratic transport at Riemannian curvature equality -/

@[expose] public section

open MeasureTheory ProbabilityTheory Bundle
open scoped ENNReal ContDiff Manifold RealInnerProductSpace

namespace CutoffRigidity.Paper

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- At curvature equality the splitting supplies a Gaussian projection. A law with the
Ornstein–Uhlenbeck moments in that projection satisfies the quadratic transport lower bound. -/
theorem riemannian_transport_lower_of_moments {V : M → ℝ}
    (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V) {μ : Measure M} [IsProbabilityMeasure μ]
    (hμ : CutCur.IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CutCur.CD F ρ V) (hgap : CutCur.mSpectralGap F μ = ρ) :
    let k := CutCur.mFirstEigenDim F μ V
    ∃ p : M → CutCur.Rd k, LipschitzWith 1 p ∧
      μ.map p = multivariateGaussian 0 (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) ∧
      ∀ (ν : Measure M) [IsProbabilityMeasure ν] {t : ℝ}, 0 ≤ t → ∀ x₀ : M,
        (∀ a : CutCur.Rd k, ∫ y, ⟪a, p y⟫ ∂ν = Real.exp (-ρ * t) * ⟪a, p x₀⟫) →
        Integrable (fun y => ‖p y‖ ^ 2) ν →
        (∫ y, ‖p y‖ ^ 2 ∂ν =
          Real.exp (-2 * ρ * t) * ‖p x₀‖ ^ 2 + k / ρ * (1 - Real.exp (-2 * ρ * t))) →
        ENNReal.ofReal (ρ * (Real.exp (-2 * ρ * t) * ‖p x₀‖ ^ 2) +
          k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) ≤
        ENNReal.ofReal ρ * TauCeti.transportCost (fun z => edist z.1 z.2 ^ 2) ν μ := by
  intro k
  obtain ⟨F', _, _, _, N, _, _, _, _, _, _, _, _, _, _, V', μ', Φ, hproperties,
    hdist, _, hmap, _, _⟩ := riemannian_gaussian_splitting F hV hμ hρ hCD hgap
  let data : Riemann.SplitData M N k ρ μ :=
    { Φ := Φ
      μ' := μ'
      prob' := hproperties.2.1
      aemeasurable := (Φ.contMDiff.continuous.fst.measurable.prodMk
        Φ.contMDiff.continuous.snd.measurable).aemeasurable
      dist_sq := hdist
      map_eq := hmap }
  exact ⟨data.proj, data.lipschitz_proj, data.map_proj_eq,
    fun ν _ _ ht x₀ hmean hint hsecond => data.lower_of_moments hρ ht x₀ ν hmean hint hsecond⟩

end CutoffRigidity.Paper
