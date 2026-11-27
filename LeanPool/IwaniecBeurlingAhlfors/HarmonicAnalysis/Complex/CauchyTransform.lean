/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Convolution
import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Complex.RadialIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Cauchy transform

The Cauchy kernel `1 / (π z)` (`HarmonicAnalysis.cauchyKernel`) and the Cauchy transform
`C g = g ∗ (1 / (π z))`, that is `C g (z) = (1/π) ∫ g (w) / (z − w) dw`
(`HarmonicAnalysis.cauchyTransform`), as a convolution in Mathlib's sense, and its basic
properties for `g` continuous, resp. smooth, with compact support. The smoothness and the
derivatives are Mathlib's differentiation of convolutions with a compactly supported factor
(`HasCompactSupport.contDiff_convolution_left`, `HasCompactSupport.hasFDerivAt_convolution_left`),
once the kernel is known to be locally integrable. The decay estimates at infinity are elementary
bounds on `1 / (z − w)` for `w` in the support of `g`.

## Main results

* `HarmonicAnalysis.locallyIntegrable_cauchyKernel`: `1 / (π z)` is locally integrable, since
  `∫_{|z| < 1} |z|^{−1} dz = 2π`.
* `HarmonicAnalysis.continuous_cauchyTransform`, `HarmonicAnalysis.contDiff_cauchyTransform`: for
  `g` continuous, resp. smooth, with compact support, `C g` is continuous, resp. smooth.
* `HarmonicAnalysis.fderiv_cauchyTransform_apply`, `HarmonicAnalysis.dz_cauchyTransform`,
  `HarmonicAnalysis.dzbar_cauchyTransform`: `∂_v (C g) = C (∂_v g)`, so `∂ (C g) = C (∂g)` and
  `∂_zbar (C g) = C (∂_zbar g)` (for `g` of class `C¹` with compact support:
  `HarmonicAnalysis.dz_cauchyTransform_of_contDiff_one`,
  `HarmonicAnalysis.dzbar_cauchyTransform_of_contDiff_one`).
* `HarmonicAnalysis.integral_dz_eq_zero`, `HarmonicAnalysis.integral_dzbar_eq_zero`:
  `∫ ∂g = ∫ ∂_zbar g = 0` for `g` of class `C¹` with compact support (integration by parts against
  the constant `1`).
* `HarmonicAnalysis.exists_norm_cauchyTransform_le`: if `g` is continuous and vanishes outside
  `|w| ≤ R₀`, then `|C g (z)| ≤ (2/π) ‖g‖₁ / |z|` for `|z| ≥ 2 R₀`, since then
  `|z − w| ≥ |z| / 2` on the support of `g`.
* `HarmonicAnalysis.exists_norm_cauchyTransform_le_of_integral_eq_zero`: if moreover `∫ g = 0`,
  then `C g (z) = (1/π) ∫ g (w) (1/(z − w) − 1/z) dw = (1/π) ∫ g (w) w / (z (z − w)) dw`, so
  `|C g (z)| ≤ (2 R₀/π) ‖g‖₁ / |z|²` for `|z| ≥ 2 R₀`.
* `HarmonicAnalysis.tendsto_cauchyTransform_cocompact`: `C g (z) → 0` as `z → ∞`.
* `HarmonicAnalysis.memLp_of_norm_le_div_sq`: a continuous function that is `O (1/|z|²)` at
  infinity is in `L^p` for every `1 < p`, by comparison with `(1 + |z|)^{−2p}`, integrable on
  `ℂ` since `2p > 2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric
open scoped Real Convolution Topology ContDiff

namespace HarmonicAnalysis

/-- The Cauchy kernel `1 / (π z)` (`0` at `z = 0`, by Lean's `0⁻¹ = 0`; the value at one point
does not matter). -/
def cauchyKernel (z : ℂ) : ℂ := ((π : ℂ) * z)⁻¹

/-- The Cauchy transform `C g = g ∗ (1 / (π z))`: `C g (z) = (1/π) ∫ g (w) / (z − w) dw`
(`HarmonicAnalysis.cauchyTransform_apply`). -/
def cauchyTransform (g : ℂ → ℂ) : ℂ → ℂ :=
  g ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] cauchyKernel

/-- `C g (z) = ∫ g (w) / (π (z − w)) dw`. -/
theorem cauchyTransform_apply (g : ℂ → ℂ) (z : ℂ) :
    cauchyTransform g z = ∫ w, g w * cauchyKernel (z - w) := by
  simp [cauchyTransform, convolution_def]

/-! ### The kernel -/

/-- `|1 / (π z)| = 1 / (π |z|)`. -/
theorem norm_cauchyKernel (z : ℂ) : ‖cauchyKernel z‖ = (π * ‖z‖)⁻¹ := by
  simp [cauchyKernel, abs_of_pos Real.pi_pos]

/-- The Cauchy kernel is measurable. -/
theorem measurable_cauchyKernel : Measurable cauchyKernel := by
  unfold cauchyKernel
  fun_prop

/-- The Cauchy kernel is integrable on the unit disc: `∫_{|z| < 1} |z|^{−1} dz = 2π`. -/
theorem integrableOn_cauchyKernel_ball : IntegrableOn cauchyKernel (ball 0 1) := by
  refine ⟨measurable_cauchyKernel.aestronglyMeasurable, ?_⟩
  have h := lintegral_ball_norm_rpow (s := 1) (by norm_num)
  have hmeas : Measurable fun z : ℂ => ENNReal.ofReal (‖z‖ ^ (-1 : ℝ)) := by fun_prop
  calc ∫⁻ z in ball 0 1, ‖cauchyKernel z‖ₑ
      = ∫⁻ z : ℂ in ball 0 1, ENNReal.ofReal π⁻¹ * ENNReal.ofReal (‖z‖ ^ (-1 : ℝ)) := by
        refine lintegral_congr fun z => ?_
        rw [← ofReal_norm, norm_cauchyKernel, ← ENNReal.ofReal_mul (by positivity),
          Real.rpow_neg_one, mul_inv]
    _ = ENNReal.ofReal π⁻¹ * ENNReal.ofReal (2 * π / (2 - 1)) := by
        rw [lintegral_const_mul _ hmeas, h]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The Cauchy kernel `1 / (π z)` is locally integrable: integrable on the unit disc, and
continuous away from `0`. -/
theorem locallyIntegrable_cauchyKernel : LocallyIntegrable cauchyKernel volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  have hk' : IsCompact (k \ ball 0 1) := hk.diff isOpen_ball
  have hcont : ContinuousOn cauchyKernel (k \ ball 0 1) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hz.2 (mem_ball_self one_pos)
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact ((continuousAt_const.mul continuousAt_id).inv₀ (mul_ne_zero hπ hz0)).continuousWithinAt
  refine (integrableOn_cauchyKernel_ball.union (hcont.integrableOn_compact hk')).mono_set ?_
  intro z hz
  by_cases h : z ∈ ball (0 : ℂ) 1
  · exact Or.inl h
  · exact Or.inr ⟨hz, h⟩

/-- For a continuous compactly supported `g`, `w ↦ g (w) / (π (z − w))` is integrable. -/
theorem integrable_mul_cauchyKernel {g : ℂ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (z : ℂ) : Integrable fun w => g w * cauchyKernel (z - w) :=
  hgc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ) hg locallyIntegrable_cauchyKernel z

/-! ### Continuity and derivatives -/

/-- The Cauchy transform of a continuous compactly supported function is continuous. -/
theorem continuous_cauchyTransform {g : ℂ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (cauchyTransform g) :=
  hgc.continuous_convolution_left _ hg locallyIntegrable_cauchyKernel

/-- The Cauchy transform of a smooth compactly supported function is smooth. -/
theorem contDiff_cauchyTransform {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ContDiff ℝ ∞ (cauchyTransform g) :=
  hgc.contDiff_convolution_left _ hg locallyIntegrable_cauchyKernel

/-- `∂_v (C g) = C (∂_v g)` for `g` of class `C¹` with compact support. -/
theorem fderiv_cauchyTransform_apply {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (z v : ℂ) :
    fderiv ℝ (cauchyTransform g) z v = cauchyTransform (fun w => fderiv ℝ g w v) z := by
  have hd := hgc.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hg
    locallyIntegrable_cauchyKernel z
  have hint := (hgc.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.mul ℝ ℂ).precompL ℂ) (hg.continuous_fderiv one_ne_zero)
    locallyIntegrable_cauchyKernel z
  rw [cauchyTransform_apply]
  unfold cauchyTransform
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint]
  rfl

/-- `w ↦ ∂_v g (w) / (π (z − w))` is integrable, for `g` of class `C¹` with compact support. -/
private lemma integrable_fderiv_mul_cauchyKernel {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (z v : ℂ) :
    Integrable fun w => fderiv ℝ g w v * cauchyKernel (z - w) :=
  integrable_mul_cauchyKernel ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (hgc.fderiv_apply ℝ v) z

/-- `∂ (C g) = C (∂g)` for `g` of class `C¹` with compact support. -/
theorem dz_cauchyTransform_of_contDiff_one {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) : dz (cauchyTransform g) = cauchyTransform (dz g) := by
  funext z
  simp only [dz, fderiv_cauchyTransform_apply hg hgc, cauchyTransform_apply, smul_eq_mul]
  rw [← integral_const_mul,
    ← integral_sub (integrable_fderiv_mul_cauchyKernel hg hgc z 1)
      ((integrable_fderiv_mul_cauchyKernel hg hgc z Complex.I).const_mul _),
    ← integral_const_mul]
  congr 1
  funext w
  ring

/-- `∂_zbar (C g) = C (∂_zbar g)` for `g` of class `C¹` with compact support. -/
theorem dzbar_cauchyTransform_of_contDiff_one {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) : dzbar (cauchyTransform g) = cauchyTransform (dzbar g) := by
  funext z
  simp only [dzbar, fderiv_cauchyTransform_apply hg hgc, cauchyTransform_apply, smul_eq_mul]
  rw [← integral_const_mul,
    ← integral_add (integrable_fderiv_mul_cauchyKernel hg hgc z 1)
      ((integrable_fderiv_mul_cauchyKernel hg hgc z Complex.I).const_mul _),
    ← integral_const_mul]
  congr 1
  funext w
  ring

/-- `∂ (C g) = C (∂g)` for `g` smooth with compact support. -/
theorem dz_cauchyTransform {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    dz (cauchyTransform g) = cauchyTransform (dz g) :=
  dz_cauchyTransform_of_contDiff_one (hg.of_le (by exact_mod_cast le_top)) hgc

/-- `∂_zbar (C g) = C (∂_zbar g)` for `g` smooth with compact support. -/
theorem dzbar_cauchyTransform {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    dzbar (cauchyTransform g) = cauchyTransform (dzbar g) :=
  dzbar_cauchyTransform_of_contDiff_one (hg.of_le (by exact_mod_cast le_top)) hgc

/-! ### Integrals of derivatives -/

/-- `∫ ∂_v g = 0` for `g` of class `C¹` with compact support: integration by parts against the
constant `1`. -/
theorem integral_fderiv_apply_eq_zero {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (v : ℂ) : ∫ z, fderiv ℝ g z v = 0 := by
  have hcont : Continuous fun z => fderiv ℝ g z v :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : ℂ => (1 : ℂ)) (g := g) (v := v) (by simp)
    (by simpa using hcont.integrable_of_hasCompactSupport (hgc.fderiv_apply ℝ v))
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hgc)
    (fun x _ => differentiableAt_const _) (fun x _ => hg.differentiable one_ne_zero x)
  simpa using h

/-- `∫ ∂g = 0` for `g` of class `C¹` with compact support. -/
theorem integral_dz_eq_zero {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∫ z, dz g z = 0 := by
  have h1 := (hg.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := (1 : ℂ)))
  have hI := (hg.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := Complex.I))
  have hi1 : Integrable fun z => fderiv ℝ g z 1 :=
    h1.integrable_of_hasCompactSupport (hgc.fderiv_apply ℝ 1)
  have hiI : Integrable fun z => Complex.I • fderiv ℝ g z Complex.I :=
    (hI.integrable_of_hasCompactSupport (hgc.fderiv_apply ℝ Complex.I)).smul Complex.I
  simp only [dz]
  rw [integral_smul, integral_sub hi1 hiI, integral_smul, integral_fderiv_apply_eq_zero hg hgc,
    integral_fderiv_apply_eq_zero hg hgc]
  simp

/-- `∫ ∂_zbar g = 0` for `g` of class `C¹` with compact support. -/
theorem integral_dzbar_eq_zero {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∫ z, dzbar g z = 0 := by
  have h1 := (hg.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := (1 : ℂ)))
  have hI := (hg.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := Complex.I))
  have hi1 : Integrable fun z => fderiv ℝ g z 1 :=
    h1.integrable_of_hasCompactSupport (hgc.fderiv_apply ℝ 1)
  have hiI : Integrable fun z => Complex.I • fderiv ℝ g z Complex.I :=
    (hI.integrable_of_hasCompactSupport (hgc.fderiv_apply ℝ Complex.I)).smul Complex.I
  simp only [dzbar]
  rw [integral_smul, integral_add hi1 hiI, integral_smul, integral_fderiv_apply_eq_zero hg hgc,
    integral_fderiv_apply_eq_zero hg hgc]
  simp

/-! ### Decay at infinity -/

/-- A compactly supported function vanishes outside a disc `|w| ≤ R₀`, `R₀ > 0`. -/
private lemma exists_norm_le_of_ne_zero {g : ℂ → ℂ} (hgc : HasCompactSupport g) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ w, g w ≠ 0 → ‖w‖ ≤ R₀ := by
  obtain ⟨r, hr⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max r 1, lt_max_of_lt_right one_pos, fun w hw => ?_⟩
  have h := hr (subset_tsupport g hw)
  rw [mem_closedBall_zero_iff] at h
  exact h.trans (le_max_left _ _)

/-- `C g = O (1/|z|)` at infinity: if `g` is continuous and vanishes outside `|w| ≤ R₀`, then
`|C g (z)| ≤ (2/π) ‖g‖₁ / |z|` for `|z| ≥ 2 R₀`. -/
theorem exists_norm_cauchyTransform_le {g : ℂ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    ∃ A R : ℝ, 0 < R ∧ ∀ z, R ≤ ‖z‖ → ‖cauchyTransform g z‖ ≤ A / ‖z‖ := by
  obtain ⟨R₀, hR₀, hsupp⟩ := exists_norm_le_of_ne_zero hgc
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  refine ⟨2 / π * ∫ w, ‖g w‖, 2 * R₀, by positivity, fun z hz => ?_⟩
  have hz0 : 0 < ‖z‖ := by linarith
  rw [cauchyTransform_apply]
  calc ‖∫ w, g w * cauchyKernel (z - w)‖ ≤ ∫ w, ‖g w‖ * (2 / (π * ‖z‖)) := by
        refine norm_integral_le_of_norm_le (hgi.norm.mul_const _)
          (Eventually.of_forall fun w => ?_)
        rw [norm_mul]
        by_cases hw : g w = 0
        · simp [hw]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hw' := hsupp w hw
        have hzw : ‖z‖ / 2 ≤ ‖z - w‖ := by
          have := norm_sub_norm_le z w
          linarith
        have hzw0 : 0 < ‖z - w‖ := by linarith
        rw [norm_cauchyKernel, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [Real.pi_pos]
    _ = 2 / π * (∫ w, ‖g w‖) / ‖z‖ := by
        rw [integral_mul_const]
        field_simp

/-- `C g = O (1/|z|²)` at infinity if `∫ g = 0`: if `g` is continuous, vanishes outside
`|w| ≤ R₀` and has integral `0`, then `C g (z) = (1/π) ∫ g (w) w / (z (z − w)) dw`, so
`|C g (z)| ≤ (2 R₀/π) ‖g‖₁ / |z|²` for `|z| ≥ 2 R₀`. -/
theorem exists_norm_cauchyTransform_le_of_integral_eq_zero {g : ℂ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (h0 : ∫ w, g w = 0) :
    ∃ A R : ℝ, 0 < R ∧ ∀ z, R ≤ ‖z‖ → ‖cauchyTransform g z‖ ≤ A / ‖z‖ ^ 2 := by
  obtain ⟨R₀, hR₀, hsupp⟩ := exists_norm_le_of_ne_zero hgc
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  refine ⟨2 * R₀ / π * ∫ w, ‖g w‖, 2 * R₀, by positivity, fun z hz => ?_⟩
  have hz0 : 0 < ‖z‖ := by linarith
  have hC : cauchyTransform g z = ∫ w, g w * (cauchyKernel (z - w) - cauchyKernel z) := by
    rw [cauchyTransform_apply]
    simp_rw [mul_sub]
    rw [integral_sub (integrable_mul_cauchyKernel hg hgc z) (hgi.mul_const _),
      integral_mul_const, h0, zero_mul, sub_zero]
  rw [hC]
  calc ‖∫ w, g w * (cauchyKernel (z - w) - cauchyKernel z)‖
      ≤ ∫ w, ‖g w‖ * (2 * R₀ / (π * ‖z‖ ^ 2)) := by
        refine norm_integral_le_of_norm_le (hgi.norm.mul_const _)
          (Eventually.of_forall fun w => ?_)
        rw [norm_mul]
        by_cases hw : g w = 0
        · simp [hw]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hw' := hsupp w hw
        have hzw : ‖z‖ / 2 ≤ ‖z - w‖ := by
          have := norm_sub_norm_le z w
          linarith
        have hzw0 : 0 < ‖z - w‖ := by linarith
        have hz' : z ≠ 0 := norm_pos_iff.1 hz0
        have hzw' : z - w ≠ 0 := norm_pos_iff.1 hzw0
        have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        have key : cauchyKernel (z - w) - cauchyKernel z = w / (π * z * (z - w)) := by
          simp only [cauchyKernel]
          field_simp
          ring
        rw [key, norm_div, norm_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le,
          div_le_div_iff₀ (by positivity) (by positivity)]
        have e1 : ‖w‖ * (π * ‖z‖ ^ 2) ≤ R₀ * (π * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hw' (by positivity)
        have e2 : R₀ * π * ‖z‖ * ‖z‖ ≤ R₀ * π * ‖z‖ * (2 * ‖z - w‖) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        nlinarith
    _ = 2 * R₀ / π * (∫ w, ‖g w‖) / ‖z‖ ^ 2 := by
        rw [integral_mul_const]
        field_simp

/-- `C g (z) → 0` as `z → ∞`, for `g` continuous with compact support. -/
theorem tendsto_cauchyTransform_cocompact {g : ℂ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Tendsto (cauchyTransform g) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨A, R, -, hA⟩ := exists_norm_cauchyTransform_le hg hgc
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have hlim : Tendsto (fun z : ℂ => A / ‖z‖) (cocompact ℂ) (𝓝 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℂ => A) (cocompact ℂ) (𝓝 A)).div_atTop hnorm
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hnorm.eventually (eventually_ge_atTop R)] with z hz using hA z hz

/-- A continuous function that is `O (1/|z|²)` at infinity is in `L^p (ℂ)` for every `1 < p`:
it is bounded by a multiple of `(1 + |z|)^{−2}`, whose `p`-th power is integrable on `ℂ` since
`2p > 2`. -/
theorem memLp_of_norm_le_div_sq {f : ℂ → ℂ} (hf : Continuous f) {A R : ℝ} (hR : 0 < R)
    (h : ∀ z, R ≤ ‖z‖ → ‖f z‖ ≤ A / ‖z‖ ^ 2) {p : ℝ} (hp : 1 < p) :
    MemLp f (ENNReal.ofReal p) volume := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hf.continuousOn
  set C := max M 0 * (1 + R) ^ 2 + |A| * (1 + R⁻¹) ^ 2 with hC
  have hbound : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ (-2 : ℝ) := by
    intro z
    have h1 : 0 < 1 + ‖z‖ := by positivity
    rw [Real.rpow_neg h1.le, Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    rcases le_or_gt ‖z‖ R with hz | hz
    · have hfz : ‖f z‖ ≤ max M 0 :=
        (hM z (mem_closedBall_zero_iff.2 hz)).trans (le_max_left _ _)
      have h2 : (1 + ‖z‖) ^ 2 ≤ (1 + R) ^ 2 := by gcongr
      calc ‖f z‖ * (1 + ‖z‖) ^ 2 ≤ max M 0 * (1 + R) ^ 2 :=
            mul_le_mul hfz h2 (by positivity) (le_max_right _ _)
        _ ≤ C := le_add_of_nonneg_right (by positivity)
    · have hz0 : 0 < ‖z‖ := hR.trans hz
      have hfz : ‖f z‖ ≤ |A| / ‖z‖ ^ 2 :=
        (h z hz.le).trans (div_le_div_of_nonneg_right (le_abs_self A) (by positivity))
      have h2 : 1 + ‖z‖ ≤ (1 + R⁻¹) * ‖z‖ := by
        have : 1 ≤ R⁻¹ * ‖z‖ := by
          rw [inv_mul_eq_div, one_le_div hR]
          exact hz.le
        nlinarith
      calc ‖f z‖ * (1 + ‖z‖) ^ 2 ≤ |A| / ‖z‖ ^ 2 * ((1 + R⁻¹) * ‖z‖) ^ 2 :=
            mul_le_mul hfz (by gcongr) (by positivity) (by positivity)
        _ = |A| * (1 + R⁻¹) ^ 2 := by
            field_simp
        _ ≤ C := le_add_of_nonneg_left (by positivity)
  have hp0 : 0 < p := by linarith
  have hdom : MemLp (fun z : ℂ => C * (1 + ‖z‖) ^ (-2 : ℝ)) (ENNReal.ofReal p) volume := by
    have hmeas : AEStronglyMeasurable (fun z : ℂ => C * (1 + ‖z‖) ^ (-2 : ℝ)) volume :=
      (by fun_prop : Measurable fun z : ℂ => C * (1 + ‖z‖) ^ (-2 : ℝ)).aestronglyMeasurable
    rw [← integrable_norm_rpow_iff hmeas (by simpa using hp0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le]
    have hint : Integrable (fun z : ℂ => (1 + ‖z‖) ^ (-(2 * p))) volume :=
      integrable_one_add_norm (by simp [Complex.finrank_real_complex]; linarith)
    refine (hint.const_mul (|C| ^ p)).congr (Eventually.of_forall fun z => ?_)
    have h1 : 0 < 1 + ‖z‖ := by positivity
    simp only
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg h1.le _),
      Real.mul_rpow (abs_nonneg _) (Real.rpow_nonneg h1.le _), ← Real.rpow_mul h1.le, neg_mul]
  exact hdom.of_le hf.aestronglyMeasurable
    (Eventually.of_forall fun z => (hbound z).trans (Real.le_norm_self _))

end HarmonicAnalysis
