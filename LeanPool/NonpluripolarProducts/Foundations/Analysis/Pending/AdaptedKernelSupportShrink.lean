/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionRegularization

/-!
# Shrinking support of adapted radial kernels

The normalized radial kernels are described by a shrinking ball in adapted
complex coordinates.  The inverse coordinate equivalence converts that
description into the original norm: eventually the support is contained in
every prescribed ball about the origin.
-/

@[expose] public section

noncomputable section

open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology Pointwise Convolution Distributions

namespace SGPT.Foundations.Analysis.Pending

open AdaptedRadialKernel
open FirstPass

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {x : E}

/-- The support of the adapted normalized kernels shrinks to the origin in the
original norm, not only in the auxiliary coordinate norm. -/
theorem AdaptedRadialKernelData.eventually_kernel_support_subset_ball
    (D : AdaptedRadialKernelData μ Ω x) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j : ℕ in atTop, Function.support (D.kernel j) ⊆ ball 0 δ := by
  let A := adaptedComplexModelEquiv (E := E)
  have hradius : Tendsto
      (fun j : ℕ ↦ ‖A.symm.toContinuousLinearMap‖ *
        (shrinkingBump (E := ComplexModel (Module.finrank ℂ E))
          D.radius D.radius_pos j).rOut)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul
        (tendsto_shrinkingBump_rOut
          (E := ComplexModel (Module.finrank ℂ E)) D.radius D.radius_pos))
  have hevent : ∀ᶠ j : ℕ in atTop,
      ‖A.symm.toContinuousLinearMap‖ *
          (shrinkingBump (E := ComplexModel (Module.finrank ℂ E))
            D.radius D.radius_pos j).rOut < δ :=
    (tendsto_order.mp hradius).2 δ hδ
  filter_upwards [hevent] with j hj
  intro y hy
  rw [mem_ball, dist_zero_right]
  have hcoord : ‖A y‖ ≤ D.radius / ((j : ℝ) + 1) := by
    exact D.kernel_tsupport_subset j (subset_tsupport (D.kernel j) hy)
  calc
    ‖y‖ = ‖A.symm (A y)‖ := by rw [A.symm_apply_apply]
    _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖A y‖ :=
      A.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖A.symm.toContinuousLinearMap‖ *
        (D.radius / ((j : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hcoord (norm_nonneg _)
    _ = ‖A.symm.toContinuousLinearMap‖ *
        (shrinkingBump (E := ComplexModel (Module.finrank ℂ E))
          D.radius D.radius_pos j).rOut := rfl
    _ < δ := hj

/-- Convolution of a test function on the inner domain with one adapted
radial kernel.  This is the uncut convolution that appears after transposing
the distributional regularization pairing. -/
noncomputable def AdaptedRadialKernelData.testFunctionRadialConvolution
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (φ : 𝓓(D.inner, ℝ)) : E → ℝ :=
  (fun z : E ↦ φ z) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] D.kernel j

/-- The buffered compact set contains every test-function convolution, for
every scale.  The first summand lies in the inner domain and the second lies
in the adapted radius ball, exactly matching `coordinate_buffer`. -/
theorem AdaptedRadialKernelData.testFunctionRadialConvolution_support_subset
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (φ : 𝓓(D.inner, ℝ)) :
    Function.support (D.testFunctionRadialConvolution j φ) ⊆ D.compact := by
  intro y hy
  have hyadd : y ∈ Function.support (fun z : E ↦ φ z) +
      Function.support (D.kernel j) :=
    MeasureTheory.support_convolution_subset
      (ContinuousLinearMap.lsmul ℝ ℝ) hy
  rcases hyadd with ⟨z, hz, w, hw, rfl⟩
  have hzinner : z ∈ closure (D.inner : Set E) :=
    subset_closure (φ.tsupport_subset (subset_tsupport _ hz))
  have hcoord : ‖adaptedComplexModelEquiv w‖ ≤ D.radius := by
    refine (D.kernel_tsupport_subset j (subset_tsupport _ hw)).trans ?_
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by norm_num
    exact div_le_self D.radius_pos.le hj
  exact D.coordinate_buffer z hzinner (z + w) (by simpa using hcoord)

/-- Test-function convolution with an adapted kernel is globally smooth. -/
theorem AdaptedRadialKernelData.testFunctionRadialConvolution_contDiff
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (φ : 𝓓(D.inner, ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (D.testFunctionRadialConvolution j φ) :=
  (D.kernel_hasCompactSupport j).contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous.locallyIntegrable
    (D.kernel_contDiff j)

/-- The radial convolution bundled in the single fixed-support Fréchet space
associated with the buffered compact set. -/
noncomputable def AdaptedRadialKernelData.testFunctionRadialConvolutionSupportedIn
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (φ : 𝓓(D.inner, ℝ)) :
    ContDiffMapSupportedIn E ℝ ⊤ D.compact :=
  .of_support_subset (D.testFunctionRadialConvolution_contDiff j φ)
    (D.testFunctionRadialConvolution_support_subset j φ)

@[simp]
theorem AdaptedRadialKernelData.testFunctionRadialConvolutionSupportedIn_apply
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (φ : 𝓓(D.inner, ℝ)) (y : E) :
    D.testFunctionRadialConvolutionSupportedIn j φ y =
      D.testFunctionRadialConvolution j φ y :=
  rfl

end SGPT.Foundations.Analysis.Pending
