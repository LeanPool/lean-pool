/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPGreen
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedSigmaCompact

/-! # Integration by parts for the finite weighted volume measure -/

@[expose] public section

open Bundle Function MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- Integration by parts for the finite weighted volume measure. -/
theorem weightedIBP_of_isWeightedVolume {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M}
    (hμ : IsWeightedVolume F μ V) [IsFiniteMeasure μ] : WeightedIBP F μ V := by
  let : SigmaCompactSpace M := sigmaCompactSpace_of_finite_weightedVolume F hV hμ
  exact weightedIBP_of_isWeightedVolume_of_sigmaCompact F hV hμ

end CutCur
