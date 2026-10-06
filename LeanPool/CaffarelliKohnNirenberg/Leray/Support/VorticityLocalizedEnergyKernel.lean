/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpConvolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Spatial convolution with smooth compact kernels

For a smooth compactly supported kernel `k` on `ℝ³` and a spatial field `h`,
the convolution `k ⋆ h` is smooth, its partial derivatives are the
convolutions with the partial derivatives of `k`, it is bounded in `L²` by
`‖k‖₁ ‖h‖₂`, and it satisfies the whole-space integration by parts identity.
These are the spatial tools of the energy argument in
`lem:localized-vorticity-energy` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN

open CKN.Foundation.Parabolic

/-- Convolution of a spatial field `h` with a kernel `k`. -/
@[expose]
def vlConv (k h : Vec3 → ℝ) : Vec3 → ℝ :=
  convolution k h (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The partial derivative of a kernel in the coordinate direction `j`. -/
@[expose]
def vlDeriv (k : Vec3 → ℝ) (j : Fin 3) : Vec3 → ℝ :=
  fun y => fderiv ℝ k y (CKN.basisVec j)

/-- Smooth compactly supported kernels. -/
@[expose]
def IsVlKernel (k : Vec3 → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) k ∧ HasCompactSupport k

theorem vlConv_apply (k h : Vec3 → ℝ) (x : Vec3) :
    vlConv k h x = ∫ t, k t * h (x - t) := by
  simp [vlConv, convolution_def]

theorem IsVlKernel.continuous {k : Vec3 → ℝ} (hk : IsVlKernel k) : Continuous k :=
  hk.1.continuous

theorem IsVlKernel.integrable {k : Vec3 → ℝ} (hk : IsVlKernel k) :
    Integrable k volume :=
  hk.continuous.integrable_of_hasCompactSupport hk.2

theorem IsVlKernel.deriv {k : Vec3 → ℝ} (hk : IsVlKernel k) (j : Fin 3) :
    IsVlKernel (vlDeriv k j) := by
  refine ⟨?_, hk.2.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)⟩
  exact (hk.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem IsVlKernel.sub {k l : Vec3 → ℝ} (hk : IsVlKernel k) (hl : IsVlKernel l) :
    IsVlKernel (k - l) :=
  ⟨hk.1.sub hl.1, hk.2.sub hl.2⟩

theorem IsVlKernel.smul {k : Vec3 → ℝ} (hk : IsVlKernel k) (c : ℝ) :
    IsVlKernel (c • k) :=
  ⟨contDiff_const.smul hk.1, hk.2.smul_left⟩

theorem vlDeriv_sub {k l : Vec3 → ℝ} (hk : IsVlKernel k) (hl : IsVlKernel l) (j : Fin 3) :
    vlDeriv (k - l) j = vlDeriv k j - vlDeriv l j := by
  funext y
  simp only [vlDeriv, Pi.sub_apply]
  rw [fderiv_sub (hk.1.differentiable (by simp)).differentiableAt
    (hl.1.differentiable (by simp)).differentiableAt]
  rfl

/-- The convolution of a locally integrable field with a smooth compact kernel is
smooth. -/
theorem vlConv_contDiff {k h : Vec3 → ℝ} (hk : IsVlKernel k)
    (hh : LocallyIntegrable h volume) :
    ContDiff ℝ (⊤ : ℕ∞) (vlConv k h) :=
  hk.2.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hk.1 hh

/-- Differentiating a convolution differentiates the kernel. -/
theorem vlConv_fderiv_apply {k h : Vec3 → ℝ} (hk : IsVlKernel k)
    (hh : LocallyIntegrable h volume) (x : Vec3) (j : Fin 3) :
    fderiv ℝ (vlConv k h) x (CKN.basisVec j) = vlConv (vlDeriv k j) h x := by
  have hderiv := hk.2.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hk.1.of_le (by simp)) hh x
  rw [show vlConv k h = convolution k h (ContinuousLinearMap.lsmul ℝ ℝ) volume from rfl,
    hderiv.fderiv]
  have hexists := (hk.2.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Vec3)
    (hk.1.continuous_fderiv (by simp)) hh x
  rw [convolution_def, ContinuousLinearMap.integral_apply hexists, vlConv, convolution_def]
  rfl

/-- The convolution partial derivative, in `CKN` notation. -/
theorem vlConv_partial {k h : Vec3 → ℝ} (hk : IsVlKernel k)
    (hh : LocallyIntegrable h volume) (j : Fin 3) :
    vlDeriv (vlConv k h) j = vlConv (vlDeriv k j) h := by
  funext x
  exact vlConv_fderiv_apply hk hh x j

theorem vlConv_continuous {k h : Vec3 → ℝ} (hk : IsVlKernel k)
    (hh : LocallyIntegrable h volume) : Continuous (vlConv k h) :=
  (vlConv_contDiff hk hh).continuous

private theorem vlConv_abs_le {k h : Vec3 → ℝ} (x : Vec3) :
    |vlConv k h x| ≤ vlConv (fun y => |k y|) (fun y => |h y|) x := by
  rw [vlConv_apply, vlConv_apply]
  calc
    |∫ t, k t * h (x - t)| ≤ ∫ t, ‖k t * h (x - t)‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    _ = ∫ t, |k t| * |h (x - t)| := by
      congr 1
      funext t
      rw [Real.norm_eq_abs, abs_mul]

/-- Young's inequality in `L²` for a smooth compact kernel of any sign. -/
theorem vlConv_eLpNorm_le {k h : Vec3 → ℝ} (hk : IsVlKernel k)
    (hh : MemLp h 2 volume) :
    eLpNorm (vlConv k h) 2 volume ≤
      ENNReal.ofReal (∫ y, |k y|) * eLpNorm h 2 volume := by
  set c : ℝ := ∫ y, |k y| with hc_def
  have hc0 : 0 ≤ c := integral_nonneg fun y => abs_nonneg (k y)
  have habsInt : Integrable (fun y => |k y|) volume := hk.integrable.abs
  rcases hc0.eq_or_lt with hc | hcpos
  · -- a kernel with vanishing `L¹` norm is zero
    have hzero : ∀ y, k y = 0 := by
      have hae : (fun y => |k y|) =ᵐ[volume] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun y => abs_nonneg (k y)) habsInt).1 hc.symm
      have hcont : Continuous (fun y => |k y|) := hk.continuous.abs
      have heq := Continuous.ae_eq_iff_eq volume hcont continuous_const |>.1 hae
      intro y
      exact abs_eq_zero.1 (congrFun heq y)
    have hconv : vlConv k h = 0 := by
      funext x
      rw [vlConv_apply]
      simp [hzero]
    rw [hconv]
    simp
  · let κ : Vec3 → ℝ := fun y => c⁻¹ * |k y|
    have hκ_nonneg : ∀ y, 0 ≤ κ y := fun y =>
      mul_nonneg (inv_nonneg.2 hc0) (abs_nonneg _)
    have hκ_int : Integrable κ volume := habsInt.const_mul _
    have hκ_one : ∫ y, κ y = 1 := by
      simp only [κ]
      rw [integral_const_mul, ← hc_def, inv_mul_cancel₀ hcpos.ne']
    have hκ_meas : Measurable κ :=
      (measurable_const.mul hk.continuous.abs.measurable)
    have hyoung := CKN.young_convolution_nonneg_integral_one_of_aemeasurable
      (d := 3) (ρ := κ) (g := fun y => |h y|) (p := 2) (by norm_num) (by norm_num)
      hκ_nonneg hκ_int hκ_one hκ_meas
      (continuous_abs.measurable.comp_aemeasurable hh.aestronglyMeasurable.aemeasurable)
    have hscale : vlConv (fun y => |k y|) (fun y => |h y|) =
        c • convolution κ (fun y => |h y|) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      have hk' : (fun y => |k y|) = c • κ := by
        funext y
        simp only [κ, Pi.smul_apply, smul_eq_mul]
        rw [← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
      rw [vlConv, hk', smul_convolution]
    have hpoint : ∀ x, ‖vlConv k h x‖ ≤
        ‖(c • convolution κ (fun y => |h y|) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ := by
      intro x
      rw [← hscale, Real.norm_eq_abs, Real.norm_eq_abs]
      refine (vlConv_abs_le x).trans (le_abs_self _)
    calc
      eLpNorm (vlConv k h) 2 volume ≤
          eLpNorm (c • convolution κ (fun y => |h y|)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume :=
        eLpNorm_mono
          (vlConv_continuous hk (hh.locallyIntegrable (by norm_num))).aestronglyMeasurable
          hpoint
      _ = ‖c‖ₑ * eLpNorm (convolution κ (fun y => |h y|)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume :=
        eLpNorm_const_smul c _ 2 volume
      _ ≤ ‖c‖ₑ * eLpNorm (fun y => |h y|) 2 volume := by gcongr
      _ = ENNReal.ofReal c * eLpNorm h 2 volume := by
        rw [Real.enorm_eq_ofReal hc0]
        congr 1
        simpa [Real.norm_eq_abs] using eLpNorm_norm h hh.aestronglyMeasurable (p := 2)

theorem vlConv_memLp {k h : Vec3 → ℝ} (hk : IsVlKernel k)
    (hh : MemLp h 2 volume) : MemLp (vlConv k h) 2 volume := by
  exact (vlConv_eLpNorm_le hk hh).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hh.eLpNorm_lt_top)

/-- Integration by parts for kernel convolutions of `L²` fields. -/
theorem vlConv_integral_mul_deriv {k l h₁ h₂ : Vec3 → ℝ} (hk : IsVlKernel k)
    (hl : IsVlKernel l) (hh₁ : MemLp h₁ 2 volume) (hh₂ : MemLp h₂ 2 volume) (j : Fin 3) :
    ∫ x, vlConv k h₁ x * vlConv (vlDeriv l j) h₂ x =
      -∫ x, vlConv (vlDeriv k j) h₁ x * vlConv l h₂ x := by
  have hloc₁ : LocallyIntegrable h₁ volume := hh₁.locallyIntegrable (by norm_num)
  have hloc₂ : LocallyIntegrable h₂ volume := hh₂.locallyIntegrable (by norm_num)
  have h1 := vlConv_memLp hk hh₁
  have h2 := vlConv_memLp hl hh₂
  have h1' := vlConv_memLp (hk.deriv j) hh₁
  have h2' := vlConv_memLp (hl.deriv j) hh₂
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Vec3)) (f := vlConv k h₁) (g := vlConv l h₂)
    (v := CKN.basisVec j)
    (by
      simp_rw [vlConv_fderiv_apply hk hloc₁]
      exact h1'.integrable_mul h2)
    (by
      simp_rw [vlConv_fderiv_apply hl hloc₂]
      exact h1.integrable_mul h2')
    (h1.integrable_mul h2)
    (fun x _ => ((vlConv_contDiff hk hloc₁).differentiable (by simp)).differentiableAt)
    (fun x _ => ((vlConv_contDiff hl hloc₂).differentiable (by simp)).differentiableAt)
  simp_rw [vlConv_fderiv_apply hk hloc₁, vlConv_fderiv_apply hl hloc₂] at hibp
  exact hibp

/-- Convolution is linear in the kernel. -/
theorem vlConv_sub_kernel {k l h : Vec3 → ℝ} (hk : IsVlKernel k) (hl : IsVlKernel l)
    (hh : LocallyIntegrable h volume) :
    vlConv (k - l) h = vlConv k h - vlConv l h := by
  funext x
  have hkx := hk.2.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hk.continuous hh x
  have hlx := hl.2.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hl.continuous hh x
  simp only [vlConv, convolution_def, Pi.sub_apply, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]
  simp only [sub_mul]
  rw [integral_sub]
  · simpa [ConvolutionExistsAt] using hkx
  · simpa [ConvolutionExistsAt] using hlx

end CKN

end
