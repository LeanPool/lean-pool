/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Measurable

/-!
# LipschitzApproximation: Kernel

The normalized smooth kernel, its compact support and derivative bounds for Euclidean Lipschitz
approximation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff Convolution ENNReal

namespace FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Kernel

variable [MeasurableSpace E] (m : Measure E)

/-- The normalized mollifier of radius `2 * R`. -/
def kernel (R : ℝ) (x : E) : ℝ := (∫ y, scaled R y ∂m)⁻¹ • scaled R x

theorem kernel_nonneg (R : ℝ) (x : E) : 0 ≤ kernel m R x :=
  smul_nonneg (inv_nonneg.mpr (integral_nonneg fun y => scaled_nonneg R y)) (scaled_nonneg R x)

theorem kernel_eq_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : 2 * R ≤ ‖x‖) : kernel m R x = 0 := by
  simp [kernel, scaled_eq_zero hR hx]

theorem norm_le_of_kernel_ne_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : kernel m R x ≠ 0) :
    ‖x‖ < 2 * R := by
  by_contra h
  push Not at h
  exact hx (kernel_eq_zero m hR h)

theorem hasCompactSupport_kernel [FiniteDimensional ℝ E] {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (kernel m R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R)) fun x hx =>
    kernel_eq_zero m hR
      (by
        rw [Metric.mem_closedBall, dist_zero_right] at hx
        exact le_of_lt (not_le.mp hx))

theorem tsupport_kernel_subset {R : ℝ} (hR : 0 < R) :
    tsupport (kernel m R) ⊆ Metric.closedBall (0 : E) (2 * R) :=
  closure_minimal (fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (norm_le_of_kernel_ne_zero m hR hx)) Metric.isClosed_closedBall

theorem contDiff_kernel (R : ℝ) : ContDiff ℝ ∞ (kernel m R) :=
  (contDiff_scaled R).const_smul _

theorem continuous_kernel (R : ℝ) : Continuous (kernel m R) := (contDiff_kernel m R).continuous

theorem hasFDerivAt_kernel (R : ℝ) (x : E) :
    HasFDerivAt (kernel m R)
      ((∫ y, scaled R y ∂m)⁻¹ • (R⁻¹ • fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x))) x := by
  exact HasFDerivAt.const_smul (hasFDerivAt_scaled (E := E) R x) (∫ y, scaled R y ∂m)⁻¹

theorem norm_fderiv_kernel {R : ℝ} (hR : 0 < R) (x : E) :
    ‖fderiv ℝ (kernel m R) x‖ =
      (∫ y, scaled R y ∂m)⁻¹ * (R⁻¹ * ‖fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x)‖) := by
  rw [(hasFDerivAt_kernel m R x).fderiv, norm_smul, norm_smul, norm_inv, norm_inv,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => scaled_nonneg R y),
    abs_of_pos hR]

/-- The scale-free constant controlling the mass of the kernel derivative. -/
def kernelDerivativeMass : ℝ := (∫ x, ‖fderiv ℝ (⇑(bump (E := E))) x‖ ∂m) / ∫ x, bump (E := E) x ∂m

theorem kernelDerivativeMass_nonneg : 0 ≤ kernelDerivativeMass (E := E) m :=
  div_nonneg (integral_nonneg fun _ => norm_nonneg _)
    (integral_nonneg fun _ => (bump (E := E)).nonneg)

theorem continuous_fderiv_kernel (R : ℝ) : Continuous (fderiv ℝ (kernel m R)) :=
  (contDiff_kernel m R).continuous_fderiv (by simp)

theorem hasCompactSupport_fderiv_kernel [FiniteDimensional ℝ E] {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (fderiv ℝ (kernel m R)) :=
  (hasCompactSupport_kernel m hR).fderiv (𝕜 := ℝ)

theorem norm_le_of_fderiv_kernel_ne_zero {R : ℝ} (hR : 0 < R) {x : E}
    (hx : fderiv ℝ (kernel m R) x ≠ 0) : ‖x‖ ≤ 2 * R := by
  have := tsupport_kernel_subset m hR (support_fderiv_subset ℝ hx)
  simpa [Metric.mem_closedBall, dist_zero_right] using this

/-- Mollification of `g` by the normalized kernel of radius `2 * R`. -/
def mollify (R : ℝ) (g : E → ℝ) : E → ℝ :=
  g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] kernel m R

theorem hasCompactSupport_mollify [FiniteDimensional ℝ E] {R : ℝ} (hR : 0 < R) {g : E → ℝ}
    (hg : HasCompactSupport g) : HasCompactSupport (mollify m R g) :=
  hg.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hasCompactSupport_kernel m hR)

section HaarNormalization

variable [BorelSpace E] [FiniteDimensional ℝ E] [m.IsAddHaarMeasure]

theorem integral_bump_pos : 0 < ∫ x, bump (E := E) x ∂m := (bump (E := E)).integral_pos

theorem integral_scaled {R : ℝ} (hR : 0 < R) :
    ∫ x, scaled R x ∂m = R ^ Module.finrank ℝ E * ∫ x, bump (E := E) x ∂m := by
  have := Measure.integral_comp_inv_smul m (fun y : E => bump (E := E) y) R
  simpa [scaled, abs_of_pos (pow_pos hR _)] using this

theorem integral_scaled_pos {R : ℝ} (hR : 0 < R) : 0 < ∫ x, scaled R x ∂m := by
  rw [integral_scaled m hR]
  have := integral_bump_pos (E := E) m
  positivity

theorem integrable_scaled {R : ℝ} (hR : 0 < R) : Integrable (scaled (E := E) R) m :=
  (continuous_scaled R).integrable_of_hasCompactSupport (hasCompactSupport_scaled hR)

theorem integrable_kernel {R : ℝ} (hR : 0 < R) : Integrable (kernel m R) m :=
  (continuous_kernel m R).integrable_of_hasCompactSupport (hasCompactSupport_kernel m hR)

theorem integral_kernel {R : ℝ} (hR : 0 < R) : ∫ x, kernel m R x ∂m = 1 := by
  simp only [kernel]
  rw [integral_smul, smul_eq_mul, inv_mul_cancel₀ (integral_scaled_pos m hR).ne']

theorem integrable_norm_fderiv_kernel {R : ℝ} (hR : 0 < R) :
    Integrable (fun x => ‖fderiv ℝ (kernel m R) x‖) m :=
  ((continuous_fderiv_kernel m R).integrable_of_hasCompactSupport
    (hasCompactSupport_fderiv_kernel m hR)).norm

theorem integral_norm_fderiv_kernel {R : ℝ} (hR : 0 < R) :
    ∫ x, ‖fderiv ℝ (kernel m R) x‖ ∂m = R⁻¹ * kernelDerivativeMass m := by
  simp_rw [norm_fderiv_kernel m hR]
  rw [integral_const_mul, integral_const_mul,
    Measure.integral_comp_inv_smul m (fun y : E => ‖fderiv ℝ (⇑(bump (E := E))) y‖) R,
    integral_scaled m hR, abs_of_pos (pow_pos hR _), kernelDerivativeMass, smul_eq_mul]
  have h1 := integral_bump_pos (E := E) m
  have h2 : (0 : ℝ) < R ^ Module.finrank ℝ E := pow_pos hR _
  field_simp

theorem mollify_apply (R : ℝ) (g : E → ℝ) (x : E) :
    mollify m R g x = ∫ t, g (x - t) * kernel m R t ∂m := by
  rw [mollify, convolution_eq_swap]
  simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

theorem integrable_shift_mul_kernel {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) (x : E) :
    Integrable (fun t => g (x - t) * kernel m R t) m := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hg.comp (continuous_const.sub continuous_id)).mul (continuous_kernel m R)
  · exact (hasCompactSupport_kernel m hR).mul_left

theorem contDiff_mollify {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) :
    ContDiff ℝ ∞ (mollify m R g) :=
  (hasCompactSupport_kernel m hR).contDiff_convolution_right _ hg.locallyIntegrable
    (contDiff_kernel m R)

theorem continuous_mollify {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) :
    Continuous (mollify m R g) :=
  (contDiff_mollify m hR hg).continuous

theorem lipschitzWith_mollify {R : ℝ} (hR : 0 < R) {K : NNReal} {g : E → ℝ}
    (hg : LipschitzWith K g) : LipschitzWith K (mollify m R g) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [mollify_apply, mollify_apply, Real.dist_eq,
    ← integral_sub (integrable_shift_mul_kernel m hR hg.continuous x)
      (integrable_shift_mul_kernel m hR hg.continuous y)]
  have hK : Integrable (fun t => K * dist x y * kernel m R t) m :=
    (integrable_kernel m hR).const_mul _
  calc |∫ t, (g (x - t) * kernel m R t - g (y - t) * kernel m R t) ∂m|
      ≤ ∫ t, K * dist x y * kernel m R t ∂m := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le hK (ae_of_all _ fun t => ?_)
        rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg m R t)]
        refine mul_le_mul_of_nonneg_right ?_ (kernel_nonneg m R t)
        rw [← Real.dist_eq]
        calc dist (g (x - t)) (g (y - t)) ≤ K * dist (x - t) (y - t) := hg.dist_le_mul _ _
          _ = K * dist x y := by rw [dist_sub_right]
    _ = K * dist x y := by rw [integral_const_mul, integral_kernel m hR, mul_one]

theorem mollify_le {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) {b : ℝ}
    (hb : ∀ x, g x ≤ b) (x : E) : mollify m R g x ≤ b := by
  rw [mollify_apply]
  calc ∫ t, g (x - t) * kernel m R t ∂m ≤ ∫ t, b * kernel m R t ∂m := by
        refine integral_mono (integrable_shift_mul_kernel m hR hg x)
          ((integrable_kernel m hR).const_mul _) fun t => ?_
        exact mul_le_mul_of_nonneg_right (hb _) (kernel_nonneg m R t)
    _ = b := by rw [integral_const_mul, integral_kernel m hR, mul_one]

theorem le_mollify {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) {a : ℝ}
    (ha : ∀ x, a ≤ g x) (x : E) : a ≤ mollify m R g x := by
  rw [mollify_apply]
  calc a = ∫ t, a * kernel m R t ∂m := by rw [integral_const_mul, integral_kernel m hR, mul_one]
    _ ≤ ∫ t, g (x - t) * kernel m R t ∂m := by
        refine integral_mono ((integrable_kernel m hR).const_mul _)
          (integrable_shift_mul_kernel m hR hg x) fun t => ?_
        exact mul_le_mul_of_nonneg_right (ha _) (kernel_nonneg m R t)

theorem abs_mollify_le {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) (x : E) : |mollify m R g x| ≤ C :=
  abs_le.mpr ⟨le_mollify m hR hg (fun x => (abs_le.mp (hC x)).1) x,
    mollify_le m hR hg (fun x => (abs_le.mp (hC x)).2) x⟩

theorem norm_mollify_sub_le {R : ℝ} (hR : 0 < R) {K : NNReal} {g : E → ℝ}
    (hg : LipschitzWith K g) (x : E) : ‖mollify m R g x - g x‖ ≤ K * (2 * R) := by
  have h : mollify m R g x - g x = ∫ t, (g (x - t) - g x) * kernel m R t ∂m := by
    rw [mollify_apply]
    simp_rw [sub_mul]
    rw [integral_sub (integrable_shift_mul_kernel m hR hg.continuous x)
      ((integrable_kernel m hR).const_mul _), integral_const_mul, integral_kernel m hR, mul_one]
  rw [h]
  refine (norm_integral_le_of_norm_le ((integrable_kernel m hR).const_mul (K * (2 * R)))
    (ae_of_all _ fun t => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg m R t)]
    by_cases ht : kernel m R t = 0
    · simp [ht]
    · have htR := norm_le_of_kernel_ne_zero m hR ht
      refine mul_le_mul_of_nonneg_right ?_ (kernel_nonneg m R t)
      calc |g (x - t) - g x| = dist (g (x - t)) (g x) := (Real.dist_eq _ _).symm
        _ ≤ K * dist (x - t) x := hg.dist_le_mul _ _
        _ = K * ‖t‖ := by rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
        _ ≤ K * (2 * R) := by gcongr
  · rw [integral_const_mul, integral_kernel m hR, mul_one]

theorem hasFDerivAt_mollify {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) (x : E) :
    HasFDerivAt (mollify m R g)
      ((g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR E, m] fderiv ℝ (kernel m R)) x) x :=
  (hasCompactSupport_kernel m hR).hasFDerivAt_convolution_right _ hg.locallyIntegrable
    ((contDiff_kernel m R).of_le (mod_cast le_top)) x

theorem fderiv_mollify_apply {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) (x : E) :
    fderiv ℝ (mollify m R g) x = ∫ t, g (x - t) • fderiv ℝ (kernel m R) t ∂m := by
  have h := (hasFDerivAt_mollify m hR hg x).fderiv
  rw [convolution_eq_swap] at h
  refine h.trans ?_
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  ext v
  simp [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply, smul_eq_mul]

theorem mollify_affine {R : ℝ} (hR : 0 < R) (c : ℝ) (L : E →L[ℝ] ℝ) (x : E) :
    mollify m R (fun z => c + L z) x = c + L x - ∫ t, L t * kernel m R t ∂m := by
  rw [mollify_apply]
  have h1 : Integrable (fun t => c * kernel m R t) m := (integrable_kernel m hR).const_mul _
  have h2 : Integrable (fun t => L x * kernel m R t) m := (integrable_kernel m hR).const_mul _
  have h3 : Integrable (fun t => L t * kernel m R t) m :=
    (L.continuous.mul (continuous_kernel m R)).integrable_of_hasCompactSupport
      (hasCompactSupport_kernel m hR).mul_left
  have h : (fun t => (c + L (x - t)) * kernel m R t) =
      fun t => c * kernel m R t + L x * kernel m R t - L t * kernel m R t := by
    funext t
    rw [map_sub, add_sub, sub_mul, add_mul]
  have h12 : Integrable (fun t => c * kernel m R t + L x * kernel m R t) m := h1.add h2
  rw [h, integral_sub h12 h3, integral_add h1 h2, integral_const_mul, integral_const_mul,
    integral_kernel m hR, mul_one, mul_one]

theorem hasFDerivAt_mollify_affine {R : ℝ} (hR : 0 < R) (c : ℝ) (L : E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (mollify m R (fun z => c + L z)) L x := by
  have h : mollify m R (fun z => c + L z) = fun x => c + L x - ∫ t, L t * kernel m R t ∂m :=
    funext (mollify_affine m hR c L)
  rw [h]
  exact (((hasFDerivAt_const c x).add L.hasFDerivAt).sub_const _).congr_fderiv (zero_add L)

theorem integral_affine_smul_fderiv_kernel {R : ℝ} (hR : 0 < R) (c : ℝ) (L : E →L[ℝ] ℝ)
    (x : E) : ∫ t, (c + L (x - t)) • fderiv ℝ (kernel m R) t ∂m = L := by
  have h1 := fderiv_mollify_apply m hR (g := fun z => c + L z)
    (continuous_const.add L.continuous) x
  rw [(hasFDerivAt_mollify_affine m hR c L x).fderiv] at h1
  exact h1.symm

theorem integrable_mul_smul_fderiv_kernel {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g)
    (x : E) : Integrable (fun t => g (x - t) • fderiv ℝ (kernel m R) t) m := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hg.comp (continuous_const.sub continuous_id)).smul (continuous_fderiv_kernel m R)
  · refine (hasCompactSupport_fderiv_kernel m hR).mono fun t ht => ?_
    rw [Function.mem_support] at ht ⊢
    intro h
    exact ht (by simp [h])

theorem norm_fderiv_mollify_sub_le {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) {x : E}
    {L : E →L[ℝ] ℝ} {δ r : ℝ} (hδ : 0 ≤ δ)
    (hr : ∀ y, dist y x < r → ‖g y - g x - L (y - x)‖ ≤ δ * ‖y - x‖) (hRr : 2 * R < r) :
    ‖fderiv ℝ (mollify m R g) x - L‖ ≤ δ * (2 * kernelDerivativeMass m) := by
  have hL : L = ∫ t, (g x - L x + L (x - t)) • fderiv ℝ (kernel m R) t ∂m :=
    (integral_affine_smul_fderiv_kernel m hR (g x - L x) L x).symm
  have hint := integrable_mul_smul_fderiv_kernel m hR (g := fun z => g x - L x + L z)
    (continuous_const.add L.continuous) x
  rw [fderiv_mollify_apply m hR hg x, hL,
    ← integral_sub (integrable_mul_smul_fderiv_kernel m hR hg x) hint]
  calc ‖∫ t, (g (x - t) • fderiv ℝ (kernel m R) t -
        (g x - L x + L (x - t)) • fderiv ℝ (kernel m R) t) ∂m‖
      ≤ ∫ t, δ * (2 * R) * ‖fderiv ℝ (kernel m R) t‖ ∂m := by
        refine norm_integral_le_of_norm_le ((integrable_norm_fderiv_kernel m hR).const_mul _)
          (ae_of_all _ fun t => ?_)
        rw [← sub_smul, norm_smul]
        by_cases ht : fderiv ℝ (kernel m R) t = 0
        · simp [ht]
        · have htR : ‖t‖ ≤ 2 * R := norm_le_of_fderiv_kernel_ne_zero m hR ht
          have h1 : ‖g (x - t) - (g x - L x + L (x - t))‖ ≤ δ * ‖t‖ := by
            have h2 := hr (x - t) (by
              rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
              exact lt_of_le_of_lt htR hRr)
            have e : g (x - t) - (g x - L x + L (x - t)) = g (x - t) - g x - L ((x - t) - x) := by
              simp only [map_sub]
              abel
            rw [e]
            simpa [sub_sub_cancel_left, norm_neg] using h2
          calc ‖g (x - t) - (g x - L x + L (x - t))‖ * ‖fderiv ℝ (kernel m R) t‖
              ≤ δ * ‖t‖ * ‖fderiv ℝ (kernel m R) t‖ := by gcongr
            _ ≤ δ * (2 * R) * ‖fderiv ℝ (kernel m R) t‖ := by gcongr
    _ = δ * (2 * R) * (R⁻¹ * kernelDerivativeMass m) := by
        rw [integral_const_mul, integral_norm_fderiv_kernel m hR]
    _ = δ * (2 * kernelDerivativeMass m) := by field_simp

theorem tendsto_fderiv_mollify {g : E → ℝ} (hg : Continuous g) {x : E}
    (hx : DifferentiableAt ℝ g x) {Rs : ℕ → ℝ} (hRs : ∀ j, 0 < Rs j)
    (hlim : Tendsto Rs atTop (𝓝 0)) :
    Tendsto (fun j => fderiv ℝ (mollify m (Rs j) g) x) atTop (𝓝 (fderiv ℝ g x)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have hC := kernelDerivativeMass_nonneg (E := E) m
  set δ := η / (2 * kernelDerivativeMass m + 1) with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨r, hr, hrδ⟩ := Metric.eventually_nhds_iff.mp (hx.hasFDerivAt.isLittleO.def hδ)
  have hev : ∀ᶠ j in atTop, 2 * Rs j < r := by
    have h2 : Tendsto (fun j => 2 * Rs j) atTop (𝓝 0) := by simpa using hlim.const_mul 2
    exact (tendsto_order.1 h2).2 r hr
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun j hj => ?_⟩
  rw [dist_eq_norm]
  calc ‖fderiv ℝ (mollify m (Rs j) g) x - fderiv ℝ g x‖ ≤ δ * (2 * kernelDerivativeMass m) :=
        norm_fderiv_mollify_sub_le m (hRs j) hg hδ.le (fun y hy => hrδ hy) (hN j hj)
    _ < η := by
        rw [hδ_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        have := mul_lt_mul_of_pos_left (lt_add_one (2 * kernelDerivativeMass m)) hη
        linarith

theorem tendsto_gradient_mollify {g : E → ℝ} (hg : Continuous g) {x : E}
    (hx : DifferentiableAt ℝ g x) {Rs : ℕ → ℝ} (hRs : ∀ j, 0 < Rs j)
    (hlim : Tendsto Rs atTop (𝓝 0)) :
    Tendsto (fun j => gradient (mollify m (Rs j) g) x) atTop (𝓝 (gradient g x)) :=
  ((InnerProductSpace.toDual ℝ E).symm.continuous.tendsto _).comp
    (tendsto_fderiv_mollify m hg hx hRs hlim)

end HaarNormalization

end Kernel


end FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
