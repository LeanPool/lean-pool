/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.AdaptedKernelSupportShrink
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ConvolutionIteratedJets
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Adapted radial kernels form a test-function approximate identity

Convolution with the adapted normalized radial kernels converges in every
Fréchet seminorm on one fixed compact-support space.  Derivatives are moved to
the test function by commutativity of scalar convolution and the arbitrary-order
convolution formula.  The remaining estimate is the standard normalized-kernel
distance bound applied to a uniformly continuous iterated derivative.
-/

@[expose] public section

noncomputable section

open Set Function Filter Metric MeasureTheory TopologicalSpace
open scoped ContDiff Convolution Distributions Topology

namespace SGPT.Foundations.Analysis.Pending

open AdaptedRadialKernel
open FirstPass

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {x : E}

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The lifted bilinear map used by the iterated convolution formula is scalar
multiplication on the corresponding space of continuous multilinear maps. -/
theorem convolutionRightIteratedCLM_lsmul (r : ℕ) :
    convolutionRightIteratedCLM (G := E)
        (ContinuousLinearMap.lsmul ℝ ℝ) r =
      (ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] (E [×r]→L[ℝ] ℝ) →L[ℝ] (E [×r]→L[ℝ] ℝ)) := by
  apply ContinuousLinearMap.ext
  intro c
  apply ContinuousLinearMap.ext
  intro A
  ext m
  rfl

/-- The zero extension of a test function on the inner domain, bundled in the
fixed compact-support space used by all radial convolutions. -/
noncomputable def AdaptedRadialKernelData.includedTestFunctionSupportedIn
    (D : AdaptedRadialKernelData μ Ω x) (φ : 𝓓(D.inner, ℝ)) :
    ContDiffMapSupportedIn E ℝ ⊤ D.compact :=
  .of_support_subset φ.contDiff fun _y hy ↦
    D.closure_inner_subset_compact
      (subset_closure (φ.tsupport_subset (subset_tsupport φ hy)))

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
@[simp]
theorem AdaptedRadialKernelData.includedTestFunctionSupportedIn_apply
    (D : AdaptedRadialKernelData μ Ω x) (φ : 𝓓(D.inner, ℝ)) (y : E) :
    D.includedTestFunctionSupportedIn φ y = φ y :=
  rfl

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The fixed-support representative agrees with mathlib's test-function
inclusion into the ambient domain. -/
theorem AdaptedRadialKernelData.includedTestFunctionSupportedIn_eq_monoCLM
    (D : AdaptedRadialKernelData μ Ω x) (φ : 𝓓(D.inner, ℝ)) :
    ((D.includedTestFunctionSupportedIn φ : E → ℝ)) =
      (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) := by
  exact (testFunction_inclusion_coe D.inner_le φ).symm

/-- Every derivative of the test-function convolution is convolution of the
same kernel with the corresponding derivative of the zero-extended test
function. -/
theorem AdaptedRadialKernelData.iteratedFDeriv_testFunctionRadialConvolution
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ)
    (φ : 𝓓(D.inner, ℝ)) (r : ℕ) :
    iteratedFDeriv ℝ r (D.testFunctionRadialConvolution j φ) =
      D.kernel j ⋆[(ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] (E [×r]→L[ℝ] ℝ) →L[ℝ] (E [×r]→L[ℝ] ℝ)), μ]
        iteratedFDeriv ℝ r (fun y : E ↦ φ y) := by
  have hmulflip :
      (ContinuousLinearMap.lsmul ℝ ℝ).flip =
        ContinuousLinearMap.lsmul ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact mul_comm b a
  have hflip : D.testFunctionRadialConvolution j φ =
      D.kernel j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
        (fun y : E ↦ φ y) := by
    rw [AdaptedRadialKernelData.testFunctionRadialConvolution,
      ← convolution_flip, hmulflip]
  rw [hflip]
  funext y
  rw [iteratedFDeriv_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (D.kernel_contDiff j).continuous.locallyIntegrable
    φ.hasCompactSupport φ.contDiff r y,
    convolutionRightIteratedCLM_lsmul]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Every iterated derivative of a test function, viewed on the whole ambient
vector space by zero extension, is uniformly continuous. -/
theorem TestFunction.uniformContinuous_iteratedFDeriv
    {U : Opens E} (φ : 𝓓(U, ℝ)) (r : ℕ) :
    UniformContinuous (iteratedFDeriv ℝ r (fun y : E ↦ φ y)) := by
  let g : E → (E [×r]→L[ℝ] ℝ) :=
    iteratedFDeriv ℝ r (fun y : E ↦ φ y)
  have hnextCont : Continuous
      (iteratedFDeriv ℝ (r + 1) (fun y : E ↦ φ y)) :=
    φ.contDiff.continuous_iteratedFDeriv (by
      exact WithTop.coe_le_coe.mpr
        (le_top : ((r + 1 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hnextCompact : HasCompactSupport
      (iteratedFDeriv ℝ (r + 1) (fun y : E ↦ φ y)) :=
    φ.hasCompactSupport.iteratedFDeriv (r + 1)
  obtain ⟨C, hC⟩ :=
    hnextCont.bounded_above_of_compact_support hnextCompact
  have hC0 : 0 ≤ C :=
    (norm_nonneg (iteratedFDeriv ℝ (r + 1)
      (fun y : E ↦ φ y) 0)).trans (hC 0)
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  let δ : ℝ := ε / (C + 1)
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hC1
  refine ⟨δ, hδ, ?_⟩
  intro a b hab
  have hgdiff : ∀ y ∈ (univ : Set E), DifferentiableAt ℝ g y := by
    intro y hy
    exact (φ.contDiff.differentiable_iteratedFDeriv (by
      exact WithTop.coe_lt_coe.mpr
        (ENat.natCast_lt_top r))).differentiableAt
  have hDbound : ∀ y ∈ (univ : Set E), ‖fderiv ℝ g y‖ ≤ C := by
    intro y hy
    simpa only [g, norm_fderiv_iteratedFDeriv] using hC y
  have hmean := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    hgdiff hDbound (mem_univ b) (mem_univ a)
  rw [dist_eq_norm]
  calc
    ‖g a - g b‖ = ‖g b - g a‖ := norm_sub_rev _ _
    _ ≤ C * ‖a - b‖ := by simpa [norm_sub_rev] using hmean
    _ ≤ (C + 1) * ‖a - b‖ := by
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (C + 1) * δ := by
      apply mul_lt_mul_of_pos_left _ hC1
      simpa only [dist_eq_norm] using hab
    _ = ε := by
      dsimp only [δ]
      exact mul_div_cancel₀ ε hC1.ne'

/-- The bundled fixed-support convolution has the same arbitrary-order
derivative formula as its underlying function. -/
theorem AdaptedRadialKernelData.iteratedFDeriv_testFunctionRadialConvolutionSupportedIn
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ)
    (φ : 𝓓(D.inner, ℝ)) (r : ℕ) :
    iteratedFDeriv ℝ r
        (fun y : E ↦ D.testFunctionRadialConvolutionSupportedIn j φ y) =
      D.kernel j ⋆[(ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] (E [×r]→L[ℝ] ℝ) →L[ℝ] (E [×r]→L[ℝ] ℝ)), μ]
        iteratedFDeriv ℝ r (fun y : E ↦ φ y) := by
  exact D.iteratedFDeriv_testFunctionRadialConvolution j φ r

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The fixed-support representative and the zero-extended test function have
identical iterated derivatives. -/
theorem AdaptedRadialKernelData.iteratedFDeriv_includedTestFunctionSupportedIn
    (D : AdaptedRadialKernelData μ Ω x) (φ : 𝓓(D.inner, ℝ)) (r : ℕ) :
    iteratedFDeriv ℝ r
        (fun y : E ↦ D.includedTestFunctionSupportedIn φ y) =
      iteratedFDeriv ℝ r (fun y : E ↦ φ y) := by
  rfl

/-- For each derivative order, convolution by the adapted kernel converges
uniformly to the corresponding derivative of the test function. -/
theorem AdaptedRadialKernelData.eventually_structureMapCLM_dist_lt
    (D : AdaptedRadialKernelData μ Ω x) (φ : 𝓓(D.inner, ℝ))
    (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop,
      ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ r
          (D.testFunctionRadialConvolutionSupportedIn j φ) -
        ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ r
          (D.includedTestFunctionSupportedIn φ)‖ < ε := by
  let g : E → (E [×r]→L[ℝ] ℝ) :=
    iteratedFDeriv ℝ r (fun y : E ↦ φ y)
  have hguc : UniformContinuous g :=
    SGPT.Foundations.Analysis.Pending.TestFunction.uniformContinuous_iteratedFDeriv φ r
  obtain ⟨δ, hδ, hgδ⟩ :=
    (Metric.uniformContinuous_iff.mp hguc) (ε / 2) (half_pos hε)
  filter_upwards [D.eventually_kernel_support_subset_ball hδ] with j hj
  have hnorm :
      ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ r
          (D.testFunctionRadialConvolutionSupportedIn j φ) -
        ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ r
          (D.includedTestFunctionSupportedIn φ)‖ ≤ ε / 2 := by
    rw [BoundedContinuousFunction.norm_le (half_pos hε).le]
    intro y
    change ‖iteratedFDeriv ℝ r
          (fun q : E ↦ D.testFunctionRadialConvolutionSupportedIn j φ q) y -
        iteratedFDeriv ℝ r
          (fun q : E ↦ D.includedTestFunctionSupportedIn φ q) y‖ ≤ ε / 2
    rw [D.iteratedFDeriv_testFunctionRadialConvolutionSupportedIn j φ r,
      D.iteratedFDeriv_includedTestFunctionSupportedIn φ r]
    rw [← dist_eq_norm]
    apply MeasureTheory.dist_convolution_le (half_pos hε).le hj
      (D.kernel_nonneg j) (D.kernel_integral_one j)
      hguc.continuous.aestronglyMeasurable
    intro q hq
    exact (hgδ (by simpa only [mem_ball] using hq)).le
  exact hnorm.trans_lt (half_lt_self hε)

/-- The adapted radial convolutions converge to the zero-extended test
function in the `C^∞` Fréchet topology of one fixed compact-support space. -/
theorem AdaptedRadialKernelData.tendsto_testFunctionRadialConvolutionSupportedIn
    (D : AdaptedRadialKernelData μ Ω x) (φ : 𝓓(D.inner, ℝ)) :
    Tendsto
      (fun j : ℕ ↦ D.testFunctionRadialConvolutionSupportedIn j φ)
      atTop (𝓝 (D.includedTestFunctionSupportedIn φ)) := by
  rw [(ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM
    (𝕜 := ℝ)).isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
  intro r
  change Tendsto
    (fun j : ℕ ↦ ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ r
      (D.testFunctionRadialConvolutionSupportedIn j φ))
    atTop
    (𝓝 (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ r
      (D.includedTestFunctionSupportedIn φ)))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ :=
    (eventually_atTop.mp (D.eventually_structureMapCLM_dist_lt φ r hε))
  refine ⟨N, fun j hj ↦ ?_⟩
  exact (dist_eq_norm
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ r
      (D.testFunctionRadialConvolutionSupportedIn j φ))
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ r
      (D.includedTestFunctionSupportedIn φ))).symm ▸ hN j hj

/-- After the continuous inclusion of the fixed-support space, the same
approximate identity converges in the ambient test-function space. -/
theorem AdaptedRadialKernelData.tendsto_ofSupportedIn_testFunctionRadialConvolutionSupportedIn
    (D : AdaptedRadialKernelData μ Ω x) (φ : 𝓓(D.inner, ℝ)) :
    Tendsto
      (fun j : ℕ ↦ TestFunction.ofSupportedIn D.compact_subset
        (D.testFunctionRadialConvolutionSupportedIn j φ))
      atTop
      (𝓝 (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ))) := by
  have htarget :
      TestFunction.ofSupportedIn D.compact_subset
          (D.includedTestFunctionSupportedIn φ) =
        (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) := by
    ext y
    exact congrFun (D.includedTestFunctionSupportedIn_eq_monoCLM φ) y
  rw [← htarget]
  exact (TestFunction.continuous_ofSupportedIn D.compact_subset).continuousAt.tendsto.comp
    (D.tendsto_testFunctionRadialConvolutionSupportedIn φ)

end SGPT.Foundations.Analysis.Pending
