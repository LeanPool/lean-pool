/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzConvolutionGeneralBound

/-!
# Derivatives of Schwartz convolution

Spatial differentiation may be moved from a convolution onto its
Schwartz kernel.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap Convolution

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic LineDeriv

/-- A line derivative of scalar-kernel/vector-field Schwartz convolution
equals convolution with the corresponding derivative of the kernel. -/
theorem regularised_schwartz_convolution_lineDeriv
    (κ : 𝓢(L2Vec3, ℂ)) (ψ : 𝓢(L2Vec3, ComplexVec3)) (m : L2Vec3) :
    ∂_{m} (SchwartzMap.convolution
      (ContinuousLinearMap.lsmul ℂ ℂ) κ ψ) =
      SchwartzMap.convolution
        (ContinuousLinearMap.lsmul ℂ ℂ) (∂_{m} κ) ψ := by
  have hFourier : 𝓕 (∂_{m} (SchwartzMap.convolution
      (ContinuousLinearMap.lsmul ℂ ℂ) κ ψ)) =
      𝓕 (SchwartzMap.convolution
        (ContinuousLinearMap.lsmul ℂ ℂ) (∂_{m} κ) ψ) := by
    have hg : (fun x : L2Vec3 => inner ℝ x m).HasTemperateGrowth := by
      fun_prop
    rw [SchwartzMap.fourier_lineDerivOp_eq,
      SchwartzMap.fourier_convolution,
      SchwartzMap.fourier_convolution,
      SchwartzMap.fourier_lineDerivOp_eq]
    ext ξ i
    simp [SchwartzMap.pairing_apply_apply,
      SchwartzMap.smulLeftCLM_apply_apply hg, mul_assoc]
  have := congrArg (fun f : 𝓢(L2Vec3, ComplexVec3) => 𝓕⁻ f) hFourier
  simpa only [fourierInv_fourier_eq] using this

end CKN.Leray

end
