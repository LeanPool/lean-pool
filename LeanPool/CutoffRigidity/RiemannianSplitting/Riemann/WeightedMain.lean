/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedRigidity
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedSupport
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPDensity

/-! # Parallel gradient of first eigenfunctions (conditional on the geometric inputs) -/

@[expose] public section

open Bundle MeasureTheory Filter
open scoped Manifold ContDiff ENNReal Topology

namespace CutCur

section Main

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- Conditional form of `manifold_eigenfunction_parallel_gradient`: every smooth `L²` eigenfunction
of `-𝓛` with eigenvalue `ρ ≥ 0` has parallel gradient, given integration by parts, the Bochner
inequality, regularity, cutoffs and the chart density facts. -/
theorem manifold_eigenfunction_parallel_gradient_of_geometry {V : M → ℝ} (hV : MSmooth F V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hB : WeightedBochnerIneq F V ρ)
    (hC : WeightedCutoffs F M)
    (hcont : ∀ x₀ : M, ContinuousOn (chartVolumeDensity F x₀) (chartAt F x₀).target)
    (hpd : ∀ (x₀ : M) (z : F), z ∈ (chartAt F x₀).target → 0 < chartVolumeDensity F x₀ z)
    {f : M → ℝ} (hf : IsMEigenfunction F μ V ρ f) (x : M) :
    CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x = 0 :=
  parallel_gradient_of_geometry F hρ hIBP hReg hB hC
    (fun _ hU hne => measure_pos_of_isWeightedVolume F hV hμ hcont hpd hU hne)
    hf.1 hf.2.1 (fun y => by simpa using hf.2.2 y) x

/-- Same, with the chart density facts discharged. -/
theorem manifold_eigenfunction_parallel_gradient_of_inputs {V : M → ℝ} (hV : MSmooth F V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hB : WeightedBochnerIneq F V ρ)
    (hC : WeightedCutoffs F M)
    {f : M → ℝ} (hf : IsMEigenfunction F μ V ρ f) (x : M) :
    CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x = 0 :=
  manifold_eigenfunction_parallel_gradient_of_geometry F hV hμ hρ hIBP hReg hB hC
    (continuousOn_chartVolumeDensity F) (fun x₀ _ hz => chartVolumeDensity_pos F x₀ hz) hf x

end Main

end CutCur
