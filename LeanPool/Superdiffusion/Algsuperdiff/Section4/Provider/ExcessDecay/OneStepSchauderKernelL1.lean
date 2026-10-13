/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderKernel

/-!
# OneStepSchauderKernelL1

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Derivative scaling laws for the scaled radial mollifier

The interior Schauder estimates differentiate the reproducing
convolution once (gradient) or twice (Hessian) and move both derivatives onto
the **kernel**.  This module supplies the pointwise scaling laws that step
rests on:

* `hasFDerivAt_radialKernelScaled` — `∇K_ε(z) = ((εᵈ)⁻¹ · ε⁻¹) • ∇K(ε⁻¹ • z)`;
* `hasFDerivAt_fderiv_radialKernelScaled` —
  `D²K_ε(z) = ((εᵈ)⁻¹ · ε⁻¹ · ε⁻¹) • D²K(ε⁻¹ • z)`;
* `norm_fderiv_fderiv_radialKernelScaled` — the second of these read in norm.

Against the `ε^d` change-of-variables Jacobian of an integration in `z`, the
`(ε^d)⁻¹` of the rescaling cancels, leaving exactly the `ε⁻¹` (resp. `ε⁻²`)
that becomes the `1/r` (resp. `1/r²`) of the interior estimates.
-/

-- ==== the kernel gradient in `L¹` ====
open scoped Real
open MeasureTheory Metric

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable (d : ℕ)

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### The derivative of the scaled kernel -/

/-- **Derivative of the scaled kernel.**  `K_ε(z) = (εᵈ)⁻¹ · radialKernel d (ε⁻¹ • z)`
has derivative
`((εᵈ)⁻¹ · ε⁻¹) • fderiv radialKernel (ε⁻¹ • z)` (const factor times the chain rule for the linear
dilation `ε⁻¹ • ·`). -/
theorem hasFDerivAt_radialKernelScaled {ε : ℝ} (z : 𝔼) :
    HasFDerivAt (radialKernelScaled d ε)
      (((ε ^ d)⁻¹ * ε⁻¹) • fderiv ℝ (radialKernel d) (ε⁻¹ • z)) z := by
  have hlin : HasFDerivAt (fun w : 𝔼 => ε⁻¹ • w)
      (ε⁻¹ • ContinuousLinearMap.id ℝ 𝔼) z := by
    simpa using! (hasFDerivAt_id z).const_smul (ε⁻¹ : ℝ)
  have hK : HasFDerivAt (radialKernel d) (fderiv ℝ (radialKernel d) (ε⁻¹ • z)) (ε⁻¹ • z) :=
    ((radialKernel_contDiff (d := d) (n := 1)).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun w : 𝔼 => radialKernel d (ε⁻¹ • w))
      ((fderiv ℝ (radialKernel d) (ε⁻¹ • z)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ 𝔼)) z :=
    hK.comp z hlin
  have hmul := hcomp.const_mul (ε ^ d)⁻¹
  have hfun : (fun w : 𝔼 => (ε ^ d)⁻¹ * radialKernel d (ε⁻¹ • w)) = radialKernelScaled d ε := by
    funext w; rw [radialKernelScaled_apply]
  rw [hfun] at hmul
  have heqCLM : ((ε ^ d)⁻¹ : ℝ) • ((fderiv ℝ (radialKernel d) (ε⁻¹ • z)).comp
        (ε⁻¹ • ContinuousLinearMap.id ℝ 𝔼))
      = ((ε ^ d)⁻¹ * ε⁻¹) • fderiv ℝ (radialKernel d) (ε⁻¹ • z) := by
    ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_smul]
  rw [heqCLM] at hmul
  exact hmul

/-! ### Integrability and the `L¹` scaling law

The integrated form of the scaling law is not carried in this module; what is
available here is the pointwise identity above. -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== the kernel Hessian in `L¹` ====
open scoped Real
open MeasureTheory Metric

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable (d : ℕ)

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### The second derivative of the scaled kernel -/

/-- **Second derivative of the scaled kernel.** `fderiv K_ε = fun w => ((εᵈ)⁻¹·ε⁻¹) •
∇radialKernel(ε⁻¹•w)` (from `hasFDerivAt_radialKernelScaled`), and differentiating that
once more (chain rule for the linear dilation `ε⁻¹ • ·`) gives `D²K_ε(z) =
((εᵈ)⁻¹·ε⁻¹·ε⁻¹) • D²radialKernel (ε⁻¹ • z)`. -/
theorem hasFDerivAt_fderiv_radialKernelScaled {ε : ℝ} (z : 𝔼) :
    HasFDerivAt (fderiv ℝ (radialKernelScaled d ε))
      (((ε ^ d)⁻¹ * ε⁻¹ * ε⁻¹) • fderiv ℝ (fderiv ℝ (radialKernel d)) (ε⁻¹ • z)) z := by
  -- `fderiv K_ε` as an explicit function.
  have hΦ : fderiv ℝ (radialKernelScaled d ε)
      = fun w => ((ε ^ d)⁻¹ * ε⁻¹) • fderiv ℝ (radialKernel d) (ε⁻¹ • w) := by
    funext w; exact (hasFDerivAt_radialKernelScaled d w).fderiv
  rw [hΦ]
  -- differentiate `fun w => c • G(ε⁻¹•w)` with `G = ∇radialKernel`.
  have hlin : HasFDerivAt (fun w : 𝔼 => ε⁻¹ • w)
      (ε⁻¹ • ContinuousLinearMap.id ℝ 𝔼) z := by
    simpa using! (hasFDerivAt_id z).const_smul (ε⁻¹ : ℝ)
  have hGdiff : DifferentiableAt ℝ (fderiv ℝ (radialKernel d)) (ε⁻¹ • z) :=
    (((radialKernel_contDiff (d := d) (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
      (by simp)).differentiableAt
  have hcomp : HasFDerivAt (fun w : 𝔼 => fderiv ℝ (radialKernel d) (ε⁻¹ • w))
      ((fderiv ℝ (fderiv ℝ (radialKernel d)) (ε⁻¹ • z)).comp
        (ε⁻¹ • ContinuousLinearMap.id ℝ 𝔼)) z :=
    hGdiff.hasFDerivAt.comp z hlin
  have hΨ := hcomp.const_smul ((ε ^ d)⁻¹ * ε⁻¹)
  have heqCLM : ((ε ^ d)⁻¹ * ε⁻¹ : ℝ) • ((fderiv ℝ (fderiv ℝ (radialKernel d)) (ε⁻¹ • z)).comp
        (ε⁻¹ • ContinuousLinearMap.id ℝ 𝔼))
      = ((ε ^ d)⁻¹ * ε⁻¹ * ε⁻¹) • fderiv ℝ (fderiv ℝ (radialKernel d)) (ε⁻¹ • z) := by
    ext v w
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    ring
  rw [heqCLM] at hΨ
  exact hΨ

/-- The norm of the scaled kernel's second derivative:
`‖D²K_ε(z)‖ = (εᵈ)⁻¹ · ε⁻¹ · ε⁻¹ · ‖D²radialKernel(ε⁻¹•z)‖`. -/
theorem norm_fderiv_fderiv_radialKernelScaled {ε : ℝ} (hε : 0 < ε) (z : 𝔼) :
    ‖fderiv ℝ (fderiv ℝ (radialKernelScaled d ε)) z‖ =
      (ε ^ d)⁻¹ * ε⁻¹ * ε⁻¹ * ‖fderiv ℝ (fderiv ℝ (radialKernel d)) (ε⁻¹ • z)‖ := by
  let : NormSMulClass ℝ (𝔼 →L[ℝ] 𝔼 →L[ℝ] ℝ) :=
    NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := 𝔼 →L[ℝ] 𝔼 →L[ℝ] ℝ)
  rw [(hasFDerivAt_fderiv_radialKernelScaled d z).fderiv, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

/-! ### Integrability and the `L¹` scaling law

The integrated form of the scaling law is not carried in this module; what is
available here is the pointwise identity above. -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

