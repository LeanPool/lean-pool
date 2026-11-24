/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionConvolutionSmoothness
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionConvolutionMonotonicity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionConvolutionTranspose
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.TestFunctionRadialApproximateIdentity

/-!
# Local decreasing smooth PSH regularization of a positive-Levi distribution

The adapted radial kernels give a canonical regularization on the inner
neighborhood.  Smoothness and disc-PSH positivity follow from differentiating
the translated kernel, monotonicity follows from the radial Levi preimage, and
weak convergence follows by combining the convolution transpose identity with
the test-function approximate identity.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology

namespace SGPT.Foundations.Analysis.Pending

open AdaptedRadialKernel
open FirstPass

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {x : E}

/-- The cutoff-supported test function occurring in the distributional
transpose identity is the same ambient test function as the compact-buffered
radial convolution used by the approximate-identity theorem. -/
theorem AdaptedRadialKernelData.ofSupportedIn_convolution_eq_radialConvolution
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ)
    (φ : 𝓓(D.inner, ℝ)) :
    TestFunction.ofSupportedIn D.cutoffCompact_subset
        (D.convolutionTestFunctionSupportedIn j φ) =
      TestFunction.ofSupportedIn D.compact_subset
        (D.testFunctionRadialConvolutionSupportedIn j φ) := by
  apply TestFunction.ext
  intro y
  change D.convolutionTestFunctionSupportedIn j φ y =
    D.testFunctionRadialConvolutionSupportedIn j φ y
  rw [D.convolutionTestFunctionSupportedIn_apply,
    D.testFunctionRadialConvolutionSupportedIn_apply]
  rfl

/-- The adapted radial convolution test functions converge after inclusion in
the ambient test-function space. -/
theorem AdaptedRadialKernelData.tendsto_ambientConvolutionTestFunction
    (D : AdaptedRadialKernelData μ Ω x) (φ : 𝓓(D.inner, ℝ)) :
    Tendsto
        (fun j ↦ TestFunction.ofSupportedIn D.cutoffCompact_subset
          (D.convolutionTestFunctionSupportedIn j φ))
        atTop (𝓝 (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ))) := by
  simpa only [D.ofSupportedIn_convolution_eq_radialConvolution] using
    (D.tendsto_ofSupportedIn_testFunctionRadialConvolutionSupportedIn φ)

/-- A distribution with nonnegative constant-direction Levi derivatives has a
decreasing sequence of globally smooth disc-PSH regularizations on an inner
neighborhood, converging weakly to the actual restricted distribution. -/
theorem exists_local_decreasing_psh_regularization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E} {T : 𝓓'(Ω, ℝ)}
    (hT : HasNonnegativeDistributionalLevi T) (x : E) (hx : x ∈ Ω) :
    ∃ (U : Opens E) (hUΩ : U ≤ Ω) (f : ℕ → E → ℝ), x ∈ U ∧
      IsDecreasingSmoothPshApproximation μ (restrictDistribution T hUΩ) f := by
  let D : AdaptedRadialKernelData μ Ω x :=
    Classical.choice (exists_adaptedRadialKernelData μ hx)
  refine ⟨D.inner, D.inner_le, fun j ↦ D.distributionRegularizedValue T j,
    D.center_mem, ?_⟩
  refine ⟨fun j ↦ D.distributionRegularizedValue_contDiff T j,
    fun j ↦ D.discPshOn_distributionRegularizedValue T hT j, ?_, ?_⟩
  · intro z hz a b hab
    exact D.distributionRegularizedValue_antitone T hT hab (subset_closure hz)
  · intro φ
    have hpairing := Filter.Tendsto.comp T.continuous.continuousAt
      (D.tendsto_ambientConvolutionTestFunction φ)
    rw [restrictDistribution_apply]
    refine hpairing.congr fun n ↦ ?_
    exact (D.distribution_convolution_transpose T n φ).symm

end SGPT.Foundations.Analysis.Pending
