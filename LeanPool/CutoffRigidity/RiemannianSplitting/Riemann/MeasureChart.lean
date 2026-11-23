/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedVolume
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-! # The weighted volume in an arbitrary smooth chart

If `μ` has density `e^{-V} √det g` in the charts `chartAt x₀` (`IsWeightedVolume`), then it has
density `e^{-V∘Ξ⁻¹} chartDensity Ξ` in any chart `Ξ` with smooth inverse of order one.
-/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- Density of the weighted measure in a chart with a `C¹` inverse. -/
theorem map_chart_density [LindelofSpace M] {V : M → ℝ} {μ : Measure M}
    (hμ : IsWeightedVolume F μ V) (Ξ : OpenPartialHomeomorph M F)
    (hΞ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ.symm Ξ.target) :
    (μ.restrict Ξ.source).map Ξ = (volume.restrict Ξ.target).withDensity
      fun w ↦ ENNReal.ofReal (Real.exp (-V (Ξ.symm w)) * chartDensity Ξ w) := by
  rw [eq_riemannianVolume_withDensity F hμ]
  simpa only [chartDensity_eq_jacobian] using map_canonical_weighted_volume_chart F V Ξ hΞ


end CutCur
