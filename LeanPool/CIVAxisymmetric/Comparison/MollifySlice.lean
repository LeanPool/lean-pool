/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Mollifier
public import LeanPool.CIVAxisymmetric.Comparison.Commutator

/-! ### Uniform bound -/

public section

open MeasureTheory
open CKN
open scoped Convolution
open scoped ENNReal

noncomputable section

namespace CIV

variable {m : ℕ}

/-- The spatial mollification of a time-dependent function, at a fixed time slice.

`mollifySlice m ε q (x, τ) = ∫_y η_ε(x - y) q(y, τ) dy` where `η_ε` is the rescaled
mollifier kernel of radius `ε`. -/
@[expose] def mollifySlice (m : ℕ) (ε : ℝ) (q : Vec m × ℝ → ℝ) (z : Vec m × ℝ) : ℝ :=
  ∫ y, mollifierKernel m ε (z.1 - y) * q (y, z.2)



theorem abs_mollifySlice_le {ε : ℝ} (hε : 0 < ε) {τ : ℝ} {q : Vec m × ℝ → ℝ} {M : ℝ}
    (h_meas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (h_bdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ M) (x : Vec m) :
    |mollifySlice m ε q (x, τ)| ≤ M := by
  set f := fun y : Vec m => mollifierKernel m ε (x - y)
  set g := fun y : Vec m => q (y, τ)
  have hf_int : Integrable f volume :=
    (integrable_comp_sub_left (mollifierKernel m ε) x).mpr (integrable_mollifierKernel hε)
  have hg_meas : AEStronglyMeasurable g volume := h_meas
  have hg_bdd : ∀ᵐ y ∂volume, ‖g y‖ ≤ M := by
    filter_upwards [h_bdd] with y hy
    simpa [Real.norm_eq_abs] using hy
  have h_int : Integrable (fun y => f y * g y) volume :=
    hf_int.mul_bdd hg_meas (c := M) hg_bdd
  have h_bound : (fun y => |f y * g y|) ≤ᵐ[volume] fun y => f y * M := by
    filter_upwards [h_bdd] with y hy
    have hη : 0 ≤ f y := mollifierKernel_nonneg hε (x - y)
    rw [abs_mul, abs_of_nonneg hη]
    gcongr
  have h_int_M : Integrable (fun y => f y * M) volume := by
    simpa using hf_int.mul_const M
  have h_abs_int : Integrable (fun y => |f y * g y|) volume := h_int.abs
  calc
    |mollifySlice m ε q (x, τ)| = |∫ y, f y * g y| := rfl
    _ ≤ ∫ y, |f y * g y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, f y * M := integral_mono_ae h_abs_int h_int_M h_bound
    _ = ∫ y, M * f y := by
      refine integral_congr_ae ?_
      filter_upwards with y
      exact mul_comm _ _
    _ = M * ∫ y, f y := by rw [integral_const_mul]
    _ = M * ∫ y, mollifierKernel m ε y := by
      rw [integral_sub_left_eq_self (mollifierKernel m ε) volume x]
    _ = M * 1 := by rw [integral_mollifierKernel hε]
    _ = M := by simp

/-! ### Bridge to the convolution API -/

/-- The mollified slice equals the convolution of the time-slice with the kernel.
The kernel sits in the right slot because `∫ η_ε(x - y) q(y, τ) dy` has the kernel
evaluated at `x - y`. -/
lemma mollifySlice_eq_convolution (ε : ℝ) (τ : ℝ) (q : Vec m × ℝ → ℝ) (x : Vec m) :
    mollifySlice m ε q (x, τ) =
      ((fun y => q (y, τ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] mollifierKernel m ε) x := by
  simp [mollifySlice, convolution_def, ContinuousLinearMap.lsmul_apply, mul_comm]

/-! ### Local integrability of bounded a.e.-measurable functions -/

/-- A bounded a.e.-measurable function on `Vec m` is locally integrable. -/
lemma locallyIntegrable_of_bounded {f : Vec m → ℝ} {M : ℝ}
    (hf_meas : AEStronglyMeasurable f volume)
    (hf_bdd : ∀ᵐ y ∂volume, |f y| ≤ M) : LocallyIntegrable f volume := by
  intro x
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
  have hk : IsCompact (Metric.closedBall x 1) := isCompact_closedBall x 1
  have hk_finite : volume (Metric.closedBall x 1) ≠ ∞ := hk.measure_ne_top
  have h_bdd_k : ∀ᵐ y ∂(volume.restrict (Metric.closedBall x 1)), ‖f y‖ ≤ M := by
    filter_upwards [ae_restrict_of_ae hf_bdd] with y hy
    simpa [Real.norm_eq_abs] using hy
  exact Measure.integrableOn_of_bounded hk_finite hf_meas h_bdd_k

/-! ### Smoothness in the spatial variable -/

theorem contDiff_mollifySlice {ε : ℝ} (hε : 0 < ε) (τ : ℝ) (q : Vec m × ℝ → ℝ) (M : ℝ)
    (h_meas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (h_bdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ M) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec m => mollifySlice m ε q (x, τ)) := by
  have h_loc : LocallyIntegrable (fun y => q (y, τ)) volume :=
    locallyIntegrable_of_bounded h_meas h_bdd
  have h_comp : HasCompactSupport (mollifierKernel m ε) :=
    hasCompactSupport_mollifierKernel hε
  have h_conv_eq : (fun x : Vec m => mollifySlice m ε q (x, τ)) =
      ((fun y => q (y, τ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] mollifierKernel m ε) := by
    ext x; exact mollifySlice_eq_convolution ε τ q x
  rw [h_conv_eq]
  exact h_comp.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) h_loc
    (contDiff_mollifierKernel ε)

/-! ### Derivative formula -/

theorem fderiv_mollifySlice {ε : ℝ} (hε : 0 < ε) (τ : ℝ) (q : Vec m × ℝ → ℝ) (M : ℝ)
    (h_meas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (h_bdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ M) (x : Vec m) (v : Vec m) :
    fderiv ℝ (fun x' : Vec m => mollifySlice m ε q (x', τ)) x v =
      ∫ y, fderiv ℝ (mollifierKernel m ε) (x - y) v * q (y, τ) := by
  have h_loc : LocallyIntegrable (fun y => q (y, τ)) volume :=
    locallyIntegrable_of_bounded h_meas h_bdd
  have h_contDiff_one : ContDiff ℝ 1 (mollifierKernel m ε) :=
    contDiff_mollifierKernel ε |>.of_le (by simp)
  have h_comp : HasCompactSupport (mollifierKernel m ε) :=
    hasCompactSupport_mollifierKernel hε
  have h_fderiv : HasFDerivAt
      ((fun y => q (y, τ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] mollifierKernel m ε)
      (((fun y => q (y, τ)) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR (Vec m), volume]
        fderiv ℝ (mollifierKernel m ε)) x) x :=
    h_comp.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) h_loc h_contDiff_one x
  have h_eq : (fun x' : Vec m => mollifySlice m ε q (x', τ)) =
      ((fun y => q (y, τ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] mollifierKernel m ε) := by
    ext x'; exact mollifySlice_eq_convolution ε τ q x'
  rw [h_eq]
  have h_fderiv_eq : fderiv ℝ
      ((fun y => q (y, τ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] mollifierKernel m ε) x =
      (((fun y => q (y, τ)) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR (Vec m), volume]
        fderiv ℝ (mollifierKernel m ε)) x) :=
    h_fderiv.fderiv
  rw [h_fderiv_eq,
    convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) h_loc (h_comp.fderiv ℝ)
      (h_contDiff_one.continuous_fderiv one_ne_zero)]
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]

end CIV
