/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryJointWeyl.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryJointRadialKernel

/-!
# Correspondence auxiliary joint weyl

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `configurationWeakCauchyRiemann_has_holomorphic_representative`.
-/

@[expose] public section
open MeasureTheory Set Real
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section
variable {n : ℕ}

private theorem configuration_real_kernel_convolution_assoc (f g : Configuration n → ℝ) (U :
    Configuration n → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hu : LocallyIntegrable U volume) (x : Configuration n) :
    ((f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) x =
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U)) x := by
  have hUn : LocallyIntegrable (fun y => ‖U y‖) volume := by
    intro y
    obtain ⟨s, hs, hi⟩ := hu y
    exact ⟨s, hs, hi.norm⟩
  have hfcn : HasCompactSupport (fun y => ‖f y‖) := hfc.comp_left norm_zero
  have hgcn : HasCompactSupport (fun y => ‖g y‖) := hgc.comp_left norm_zero
  have hgn : ConvolutionExists (fun y => ‖g y‖) (fun y => ‖U y‖)
      (ContinuousLinearMap.mul ℝ ℝ) volume := hgcn.convolutionExists_left _ hg.norm hUn
  have hgnc : Continuous ((fun y => ‖g y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun y => ‖U y‖))
      :=
    hgcn.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hg.norm hUn
  apply convolution_assoc
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (L₂ := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
    (L₃ := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
    (L₄ := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
  · intros a b c
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
    ring
  · exact hf.aestronglyMeasurable
  · exact hg.aestronglyMeasurable
  · exact hu.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (hfc.convolutionExists_left _ hf hg.locallyIntegrable)
  · exact Filter.Eventually.of_forall hgn
  · exact hfcn.convolutionExists_left _ hf.norm hgnc.locallyIntegrable x

private theorem configuration_real_kernel_convolution_comm (f g : Configuration n → ℝ) :
    (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =
      (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := by
  funext x
  rw [convolution_lsmul, convolution_lsmul_swap]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => mul_comm _ _)

/-- The two-component mollification is exactly the usual real-scalar
convolution of the actual complex function. -/
theorem configurationComplexMollification_eq_convolution (φ : Configuration n → ℝ) (U :
    Configuration n → ℂ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hu : LocallyIntegrable U volume) :
    configurationComplexMollification φ U = (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) := by
  funext x
  have hi := (hc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hφ hu x).integrable
  apply Complex.ext
  · have hr := Complex.reCLM.integral_comp_comm hi
    simp only [configurationComplexMollification, convolution_lsmul, Complex.ofReal_re,
        Complex.ofReal_im,
      Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero,
          add_zero, smul_eq_mul]
    simpa only [ContinuousLinearMap.lsmul_apply, Complex.reCLM_apply, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using hr
  · have hi' := Complex.imCLM.integral_comp_comm hi
    simp only [configurationComplexMollification, convolution_lsmul, Complex.ofReal_re,
        Complex.ofReal_im,
      Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, one_mul,
          smul_eq_mul]
    simpa only [ContinuousLinearMap.lsmul_apply, Complex.imCLM_apply, Complex.real_smul,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero] using hi'

theorem configurationRadial_convolution_holomorphic_eq
    (F : Configuration n → ℂ) (hF : Differentiable ℂ F) :
    (configurationRadialSmoothingKernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) = F := by
  funext x
  rw [convolution_lsmul]
  exact configurationRadialSmoothing_mean_value n F hF x

/-- Weyl's lemma for the planar Cauchy–Riemann distribution: every locally
integrable weak solution has a genuinely entire representative. -/
theorem configurationWeakCauchyRiemann_has_holomorphic_representative (U : Configuration n → ℂ)
    (hu : LocallyIntegrable U volume)
    (htest : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → ∀ j : Fin n,
      (∫ y, (U y).re * fderiv ℝ θ y (realCoordinateDirection j) - (U y).im * fderiv ℝ θ y
          (imaginaryCoordinateDirection j)) = 0 ∧
      (∫ y, (U y).im * fderiv ℝ θ y (realCoordinateDirection j) + (U y).re * fderiv ℝ θ y
          (imaginaryCoordinateDirection j)) = 0) :
    ∃ F : Configuration n → ℂ, Differentiable ℂ F ∧ U =ᵐ[volume] F := by
  let ψ := configurationRadialSmoothingKernel n
  have hψ : ContDiff ℝ ∞ ψ := configurationRadialSmoothingKernel_contDiff n
  have hψc : HasCompactSupport ψ := configurationRadialSmoothingKernel_compact n
  have hhol (φ : Configuration n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
      Differentiable ℂ (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) := by
    rw [← configurationComplexMollification_eq_convolution φ U hφ.continuous hc hu]
    exact configurationComplexMollification_holomorphic U hu htest φ hφ hc
  let F := ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U
  have hF : Differentiable ℂ F := hhol ψ hψ hψc
  have he (φ : Configuration n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) =
        (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) := by
    calc
      _ = ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) :=
        (configurationRadial_convolution_holomorphic_eq _ (hhol φ hφ hc)).symm
      _ = (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U
          := by
        funext x
        exact (configuration_real_kernel_convolution_assoc ψ φ U hψ.continuous hφ.continuous hψc hc
            hu x).symm
      _ = (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U
          := by
        rw [configuration_real_kernel_convolution_comm]
      _ = _ := by
        funext x
        exact configuration_real_kernel_convolution_assoc φ ψ U hφ.continuous hψ.continuous hc hψc
            hu x
  refine ⟨F, hF, ?_⟩
  have hb : ∀ᶠ m in Filter.atTop, (lsiMollifier (Configuration n) m).rOut ≤ 2 * (lsiMollifier
      (Configuration n) m).rIn := by
    exact Filter.Eventually.of_forall (fun m => by simp [lsiMollifier]; linarith)
  have ha := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) (lsiMollifier_radius_tendsto (Configuration n)) hb hu
  filter_upwards [ha] with x hx
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (lsiMollifier_radius_tendsto (Configuration n)) hF.continuous x
  have ht' : Filter.Tendsto
      (fun m => ((lsiMollifier (Configuration n) m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          volume] U) x)
      Filter.atTop (𝓝 (F x)) := ht.congr' (Filter.Eventually.of_forall (fun m =>
        (congrFun (he ((lsiMollifier (Configuration n) m).normed volume)
          (lsiMollifier (Configuration n) m).contDiff_normed (lsiMollifier (Configuration n)
              m).hasCompactSupport_normed) x).symm))
  exact tendsto_nhds_unique hx ht'

end
end GinibrePoincare
