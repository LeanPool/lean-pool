/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Convolution with continuous compactly supported kernels on `L²(ℝ³)`

Scalar facts behind the Leray projection of `prop:lps-smoothing`: convolution with a
continuous compactly supported kernel is bounded on `L²`, its `L²` adjoint is
convolution with the reflected kernel, it maps test functions to test
functions commuting with partial derivatives, and a weak derivative of the
convolved function can be moved onto a smooth kernel.
-/

public section

open MeasureTheory Set Filter
open scoped Convolution ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Pointwise formula for real convolution (`prop:lps-smoothing`). -/
theorem lpsLeray_conv_apply (θ f : Vec3 → ℝ) (x : Vec3) :
    (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x = ∫ t, θ t * f (x - t) := by
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- Convolution with a continuous compactly supported kernel is bounded on
`L²(ℝ³)`: `‖θ ⋆ f‖₂ ≤ ‖θ‖₁ ‖f‖₂` (`prop:lps-smoothing`). -/
theorem lpsLeray_eLpNorm_conv_le {θ f : Vec3 → ℝ} (hθ : Continuous θ)
    (hθc : HasCompactSupport θ) (hf : MemLp f 2 volume) :
    eLpNorm (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) 2 volume ≤
      ENNReal.ofReal (∫ x, ‖θ x‖) * eLpNorm f 2 volume := by
  have hθint : Integrable θ volume := hθ.integrable_of_hasCompactSupport hθc
  set c : ℝ := ∫ x, ‖θ x‖ with hc
  have hc0 : 0 ≤ c := integral_nonneg fun x => norm_nonneg _
  have hpt : ∀ x, ‖(θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖ ≤
      ∫ t, ‖θ t‖ * ‖f (x - t)‖ := by
    intro x
    rw [lpsLeray_conv_apply]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext t
    rw [norm_mul]
  rcases hc0.eq_or_lt with h0 | hpos
  · have hθae : (fun x => ‖θ x‖) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg _) hθint.norm).1 h0.symm
    have hconv0 : (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) = 0 := by
      funext x
      have hx := hpt x
      have hzero : ∫ t, ‖θ t‖ * ‖f (x - t)‖ = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hθae] with t ht
        simp only [Pi.zero_apply] at ht
        simp only [ht, zero_mul, Pi.zero_apply]
      rw [hzero] at hx
      exact norm_le_zero_iff.1 hx
    rw [hconv0, eLpNorm_zero]
    exact bot_le
  · let ρ : Vec3 → ℝ := fun x => c⁻¹ * ‖θ x‖
    have hρnn : ∀ x, 0 ≤ ρ x := fun x => mul_nonneg (inv_nonneg.2 hc0) (norm_nonneg _)
    have hρint : Integrable ρ volume := hθint.norm.const_mul _
    have hρone : ∫ x, ρ x = 1 := by
      simp only [ρ]
      rw [integral_const_mul, ← hc]
      exact inv_mul_cancel₀ hpos.ne'
    have hρmeas : Measurable ρ := (continuous_const.mul hθ.norm).measurable
    have hY := CKN.young_convolution_nonneg_integral_one_of_aemeasurable (d := 3)
      (p := 2) (by norm_num) (by norm_num) hρnn hρint hρone hρmeas
      (hf.aestronglyMeasurable.norm.aemeasurable)
    rw [eLpNorm_norm f hf.aestronglyMeasurable] at hY
    have hbound : ∀ x, ‖(θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖ ≤
        ‖(c • (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y => ‖f y‖))) x‖ := by
      intro x
      refine (hpt x).trans ?_
      have heq : (c • (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y => ‖f y‖))) x =
          ∫ t, ‖θ t‖ * ‖f (x - t)‖ := by
        rw [Pi.smul_apply, lpsLeray_conv_apply, smul_eq_mul, ← integral_const_mul]
        congr 1
        funext t
        simp only [ρ]
        field_simp
      rw [heq]
      exact le_abs_self _
    calc eLpNorm (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) 2 volume
        ≤ eLpNorm (c • (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y => ‖f y‖))) 2 volume :=
          eLpNorm_mono (hθc.continuous_convolution_left _ hθ
            (hf.locallyIntegrable (by norm_num))).aestronglyMeasurable hbound
      _ = ‖c‖ₑ * eLpNorm (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y => ‖f y‖)) 2 volume :=
          eLpNorm_const_smul _ _ _ _
      _ ≤ ‖c‖ₑ * eLpNorm f 2 volume := by gcongr
      _ = ENNReal.ofReal c * eLpNorm f 2 volume := by rw [Real.enorm_eq_ofReal hc0]

/-- Convolution with a continuous compactly supported kernel preserves
`L²(ℝ³)` (`prop:lps-smoothing`). -/
theorem lpsLeray_memLp_conv {θ f : Vec3 → ℝ} (hθ : Continuous θ)
    (hθc : HasCompactSupport θ) (hf : MemLp f 2 volume) :
    MemLp (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) 2 volume := by
  exact memLp_iff.2 ((lpsLeray_eLpNorm_conv_le hθ hθc hf).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top))

/-- Fubini normal form of the pairing of a convolution with an `L²` function. -/
private theorem lpsLeray_integral_conv_mul {θ f h : Vec3 → ℝ} (hθ : Continuous θ)
    (hθc : HasCompactSupport θ) (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) :
    ∫ x, (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x * h x =
      ∫ t, θ t * ∫ y, f y * h (y + t) := by
  have hθint : Integrable θ volume := hθ.integrable_of_hasCompactSupport hθc
  let F : Vec3 → Vec3 → ℝ := fun x t => θ t * f (x - t) * h x
  have hF : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hB1 : Integrable (fun p : Vec3 × Vec3 => ‖θ p.2‖ * f (p.1 - p.2) ^ 2)
        (volume.prod volume) := by
      simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
        hθint.norm.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hf.integrable_sq
    have hB2 : Integrable (fun p : Vec3 × Vec3 => h p.1 ^ 2 * ‖θ p.2‖)
        (volume.prod volume) :=
      hh.integrable_sq.mul_prod hθint.norm
    have hmeas1 : AEStronglyMeasurable (fun p : Vec3 × Vec3 => θ p.2 * f (p.1 - p.2))
        (volume.prod volume) := by
      simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
        hθ.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ)
          hf.aestronglyMeasurable
    have hmeas2 : AEStronglyMeasurable (fun p : Vec3 × Vec3 => h p.1) (volume.prod volume) :=
      hh.aestronglyMeasurable.comp_fst
    refine (hB1.add hB2).mono' (hmeas1.mul hmeas2) ?_
    filter_upwards with p
    have key : |f (p.1 - p.2)| * |h p.1| ≤ f (p.1 - p.2) ^ 2 + h p.1 ^ 2 := by
      nlinarith only [sq_nonneg (|f (p.1 - p.2)| - |h p.1|), sq_abs (f (p.1 - p.2)),
        sq_abs (h p.1), abs_nonneg (f (p.1 - p.2)), abs_nonneg (h p.1)]
    calc ‖Function.uncurry F p‖ = ‖θ p.2‖ * (|f (p.1 - p.2)| * |h p.1|) := by
          simp only [Function.uncurry, F, norm_mul, Real.norm_eq_abs]
          ring
      _ ≤ ‖θ p.2‖ * (f (p.1 - p.2) ^ 2 + h p.1 ^ 2) :=
          mul_le_mul_of_nonneg_left key (norm_nonneg _)
      _ = ‖θ p.2‖ * f (p.1 - p.2) ^ 2 + h p.1 ^ 2 * ‖θ p.2‖ := by ring
  calc ∫ x, (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x * h x = ∫ x, ∫ t, F x t := by
        congr 1
        funext x
        rw [lpsLeray_conv_apply, ← integral_mul_const]
    _ = ∫ t, ∫ x, F x t := integral_integral_swap hF
    _ = ∫ t, θ t * ∫ y, f y * h (y + t) := by
        congr 1
        funext t
        rw [← integral_const_mul, ← integral_add_right_eq_self (fun x => F x t) t]
        congr 1
        funext y
        simp only [F, add_sub_cancel_right]
        ring

/-- The `L²` adjoint of convolution with `θ` is convolution with the reflected
kernel `x ↦ θ (-x)` (`prop:lps-smoothing`). -/
theorem lpsLeray_integral_conv_mul_eq {θ f h : Vec3 → ℝ} (hθ : Continuous θ)
    (hθc : HasCompactSupport θ) (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) :
    ∫ x, (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x * h x =
      ∫ x, f x * ((fun y => θ (-y)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] h) x := by
  have hθ' : Continuous (fun y : Vec3 => θ (-y)) := hθ.comp continuous_neg
  have hθc' : HasCompactSupport (fun y : Vec3 => θ (-y)) := by
    simpa [Function.comp_def] using hθc.comp_homeomorph (Homeomorph.neg Vec3)
  rw [lpsLeray_integral_conv_mul hθ hθc hf hh]
  rw [show (∫ x, f x * ((fun y => θ (-y)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] h) x) =
      ∫ x, ((fun y => θ (-y)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] h) x * f x by
    congr 1
    funext x
    ring]
  rw [lpsLeray_integral_conv_mul hθ' hθc' hh hf]
  rw [← integral_neg_eq_self (fun t => θ (-t) * ∫ y, h y * f (y + t))]
  congr 1
  funext t
  simp only [neg_neg]
  congr 1
  rw [← integral_add_right_eq_self (fun y => h y * f (y + -t)) t]
  congr 1
  funext y
  simp only [add_neg_cancel_right]
  ring

/-- Moving a weak derivative onto a smooth compactly supported kernel:
`(∂_k η) ⋆ g = η ⋆ G` when `G` is the weak `k`-th derivative of `g`
(`prop:lps-smoothing`). -/
theorem lpsLeray_conv_spatialDeriv_kernel {η g G : Vec3 → ℝ} {k : Fin 3}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hg : HasWeakPartialDerivOn univ k g G) (x : Vec3) :
    (spatialDeriv η k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) x =
      (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) x := by
  let φ : Vec3 → ℝ := fun y => η (x - y)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hη.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ := by
    simpa [φ, Function.comp_def] using hηc.comp_homeomorph (Homeomorph.subLeft x)
  have hφDeriv (y : Vec3) : (fderiv ℝ φ y) (basisVec k) = -spatialDeriv η k (x - y) := by
    have hinner : HasFDerivAt (fun z : Vec3 => x - z) (-(1 : Vec3 →L[ℝ] Vec3)) y :=
      (hasFDerivAt_id y).const_sub x
    have houter : HasFDerivAt η (fderiv ℝ η (x - y)) (x - y) :=
      (hη.differentiable (by simp) (x - y)).hasFDerivAt
    have hcomp := houter.comp y hinner
    simpa [φ, Function.comp_def, ContinuousLinearMap.comp_apply, spatialDeriv] using
      congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec k)) hcomp.fderiv
  have hweak := hg φ hφ hφc (subset_univ _)
  simp only [Measure.restrict_univ] at hweak
  rw [lpsLeray_conv_apply, lpsLeray_conv_apply]
  calc ∫ t, spatialDeriv η k t * g (x - t)
      = ∫ y, spatialDeriv η k (x - y) * g (x - (x - y)) :=
        (integral_sub_left_eq_self (fun t => spatialDeriv η k t * g (x - t)) volume x).symm
    _ = -∫ y, g y * (fderiv ℝ φ y) (basisVec k) := by
        rw [← integral_neg]
        congr 1
        funext y
        rw [hφDeriv, sub_sub_cancel]
        ring
    _ = ∫ y, G y * φ y := by rw [hweak, neg_neg]
    _ = ∫ t, G (x - t) * η (x - (x - t)) :=
        (integral_sub_left_eq_self (fun y => G y * φ y) volume x).symm
    _ = ∫ t, η t * G (x - t) := by
        congr 1
        funext t
        rw [sub_sub_cancel]
        ring

/-- The partial derivative of a reflected kernel (`prop:lps-smoothing`). -/
theorem lpsLeray_spatialDeriv_reflect {θ : Vec3 → ℝ} (hθ : Differentiable ℝ θ)
    (k : Fin 3) (x : Vec3) :
    spatialDeriv (fun y => θ (-y)) k x = -spatialDeriv θ k (-x) := by
  have hcomp := (hθ (-x)).hasFDerivAt.comp x (hasFDerivAt_id x).neg
  have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec k)) hcomp.fderiv
  simpa [spatialDeriv, Function.comp_def] using h

/-- Convolving a test function with a continuous kernel commutes with partial
derivatives (`prop:lps-smoothing`). -/
theorem lpsLeray_spatialDeriv_conv_test {θ φ : Vec3 → ℝ} (hθ : Continuous θ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (i : Fin 3) (x : Vec3) :
    spatialDeriv (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φ) i x =
      (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] spatialDeriv φ i) x := by
  have hfd := hφc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (hθ.locallyIntegrable (μ := volume)) (hφ.of_le (by norm_cast)) x
  have hconv : ConvolutionExists θ (fderiv ℝ φ)
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompR Vec3) volume :=
    (hφc.fderiv (𝕜 := ℝ)).convolutionExists_right _ (hθ.locallyIntegrable (μ := volume))
      (hφ.continuous_fderiv (by simp))
  unfold spatialDeriv
  rw [hfd.fderiv, convolution_def, ContinuousLinearMap.integral_apply (hconv x),
    lpsLeray_conv_apply]
  simp only [ContinuousLinearMap.precompR_apply]
  rfl

/-- Convolving a test function with a continuous compactly supported kernel
gives a test function (`prop:lps-smoothing`). -/
theorem lpsLeray_contDiff_conv_test {θ φ : Vec3 → ℝ} (hθ : Continuous θ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ContDiff ℝ (⊤ : ℕ∞) (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φ) :=
  hφc.contDiff_convolution_right _ (hθ.locallyIntegrable (μ := volume)) hφ

/-- Convolution of two compactly supported functions is compactly supported
(`prop:lps-smoothing`). -/
theorem lpsLeray_hasCompactSupport_conv {θ φ : Vec3 → ℝ} (hθc : HasCompactSupport θ)
    (hφc : HasCompactSupport φ) :
    HasCompactSupport (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φ) :=
  hθc.convolution _ hφc

end ESS
