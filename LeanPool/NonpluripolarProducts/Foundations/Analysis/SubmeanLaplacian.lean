/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.LeviForm
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Polar flux and the classical submean inequality

The radial and angular quantities below are defined from the actual Fréchet
derivative. Their differential identity is the polar-coordinate form of the
divergence theorem needed to derive the submean inequality from `Δu ≥ 0`.
-/

@[expose] public section

noncomputable section

open Complex Filter Laplacian MeasureTheory Metric Real Set
open scoped Topology

namespace SGPT.Foundations.Analysis

/-- Polar coordinates, with a real radius and angle. -/
def polarPoint (c : ℂ) (r θ : ℝ) : ℂ := c + r • circleMap 0 1 θ

/-- Derivative in the unit radial direction. -/
def polarRadialDerivative (u : ℂ → ℝ) (c : ℂ) (r θ : ℝ) : ℝ :=
  fderiv ℝ u (polarPoint c r θ) (circleMap 0 1 θ)

/-- The angular component of the gradient in the unit tangent direction. -/
def polarAngularDerivative (u : ℂ → ℝ) (c : ℂ) (r θ : ℝ) : ℝ :=
  fderiv ℝ u (polarPoint c r θ) (circleMap 0 1 θ * I)

/-- The radial flux integrand, including the polar Jacobian. -/
def polarRadialFlux (u : ℂ → ℝ) (c : ℂ) (r θ : ℝ) : ℝ :=
  r * polarRadialDerivative u c r θ

theorem hasDerivAt_polarPoint_radius (c : ℂ) (r θ : ℝ) :
    HasDerivAt (fun s : ℝ ↦ polarPoint c s θ) (circleMap 0 1 θ) r := by
  simpa [polarPoint] using
    ((hasDerivAt_id r).smul_const (circleMap (0 : ℂ) 1 θ)).const_add c

theorem hasDerivAt_polarPoint_angle (c : ℂ) (r θ : ℝ) :
    HasDerivAt (polarPoint c r) (r • (circleMap 0 1 θ * I)) θ := by
  change HasDerivAt (fun t ↦ c + r • circleMap 0 1 t) _ θ
  exact ((hasDerivAt_circleMap 0 1 θ).const_smul r).const_add c

theorem hasDerivAt_polar_unitTangent (θ : ℝ) :
    HasDerivAt (fun t ↦ circleMap 0 1 t * I) (-circleMap 0 1 θ) θ := by
  simpa [mul_assoc] using (hasDerivAt_circleMap 0 1 θ).mul_const I

/-- A real bilinear form has the same trace in any rotated orthogonal basis. -/
theorem complex_bilinear_rotated_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (z : ℂ) :
    B z z + B (z * I) (z * I) = ‖z‖ ^ 2 * (B 1 1 + B I I) := by
  have hsplit (w : ℂ) : w = w.re • (1 : ℂ) + w.im • I := by
    apply Complex.ext <;> simp
  have hexpand (w t : ℂ) :
      B w t = w.re * (t.re * B 1 1 + t.im * B 1 I) +
        w.im * (t.re * B I 1 + t.im * B I I) := by
    calc
      B w t = B (w.re • (1 : ℂ) + w.im • I) (t.re • (1 : ℂ) + t.im • I) := by
        rw [← hsplit w, ← hsplit t]
      _ = _ := by
        simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
        ring
  rw [hexpand z z, hexpand (z * I) (z * I), ← Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.mul_im, I_re, I_im, mul_zero, mul_one,
    zero_sub, Complex.normSq_apply]
  ring

theorem polar_hessian_trace (u : ℂ → ℝ) (c : ℂ) (r θ : ℝ) :
    realHessian u (polarPoint c r θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
      realHessian u (polarPoint c r θ) (circleMap 0 1 θ * I) (circleMap 0 1 θ * I) =
        Δ u (polarPoint c r θ) := by
  have h := complex_bilinear_rotated_trace
    (fderiv ℝ (fderiv ℝ u) (polarPoint c r θ)) (circleMap 0 1 θ)
  simpa [realHessian_eq_fderiv, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply] using h

theorem hasDerivAt_polarRadialDerivative {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℂ) (r θ : ℝ) :
    HasDerivAt (fun s ↦ polarRadialDerivative u c s θ)
      (realHessian u (polarPoint c r θ) (circleMap 0 1 θ) (circleMap 0 1 θ)) r := by
  have hd : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hc : HasDerivAt (fun s : ℝ ↦ fderiv ℝ u (polarPoint c s θ))
      (fderiv ℝ (fderiv ℝ u) (polarPoint c r θ) (circleMap 0 1 θ)) r :=
    (hd (polarPoint c r θ)).hasFDerivAt.comp_hasDerivAt r
      (hasDerivAt_polarPoint_radius c r θ)
  rw [realHessian_eq_fderiv]
  change HasDerivAt (fun s ↦ fderiv ℝ u (polarPoint c s θ) (circleMap 0 1 θ)) _ r
  simpa only [map_zero, add_zero] using!
    hc.clm_apply (hasDerivAt_const r (circleMap (0 : ℂ) 1 θ))

theorem hasDerivAt_polarRadialFlux {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℂ) (r θ : ℝ) :
    HasDerivAt (fun s ↦ polarRadialFlux u c s θ)
      (polarRadialDerivative u c r θ + r *
        realHessian u (polarPoint c r θ) (circleMap 0 1 θ) (circleMap 0 1 θ)) r := by
  simpa only [polarRadialFlux, Pi.mul_apply, id_eq, one_mul] using!
    (hasDerivAt_id r).mul (hasDerivAt_polarRadialDerivative hu c r θ)

theorem hasDerivAt_polarAngularDerivative {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℂ) (r θ : ℝ) :
    HasDerivAt (polarAngularDerivative u c r)
      (r * realHessian u (polarPoint c r θ) (circleMap 0 1 θ * I) (circleMap 0 1 θ * I) -
        polarRadialDerivative u c r θ) θ := by
  have hd : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h := ((hd (polarPoint c r θ)).hasFDerivAt.comp_hasDerivAt θ
    (hasDerivAt_polarPoint_angle c r θ)).clm_apply (hasDerivAt_polar_unitTangent θ)
  rw [realHessian_eq_fderiv]
  change HasDerivAt (fun t ↦ fderiv ℝ u (polarPoint c r t) (circleMap 0 1 t * I))
    (r * fderiv ℝ (fderiv ℝ u) (polarPoint c r θ) (circleMap 0 1 θ * I)
      (circleMap 0 1 θ * I) - fderiv ℝ u (polarPoint c r θ) (circleMap 0 1 θ)) θ
  simpa only [Function.comp_def, map_smul, smul_apply, smul_eq_mul, map_neg,
    sub_eq_add_neg] using! h

/-- The pointwise polar divergence identity, with no division by the radius. -/
theorem polar_divergence_identity {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℂ) (r θ : ℝ) :
    deriv (fun s ↦ polarRadialFlux u c s θ) r +
      deriv (polarAngularDerivative u c r) θ = r * Δ u (polarPoint c r θ) := by
  rw [(hasDerivAt_polarRadialFlux hu c r θ).deriv,
    (hasDerivAt_polarAngularDerivative hu c r θ).deriv,
    ← polar_hessian_trace u c r θ]
  ring

@[simp] theorem polarPoint_eq_circleMap (c : ℂ) (r θ : ℝ) :
    polarPoint c r θ = circleMap c r θ := by
  simp [polarPoint, circleMap, Complex.real_smul]

theorem continuous_polarPoint (c : ℂ) :
    Continuous (Function.uncurry (polarPoint c)) := by
  change Continuous (fun p : ℝ × ℝ ↦ c + p.1 • circleMap 0 1 p.2)
  exact continuous_const.add (continuous_fst.smul ((continuous_circleMap 0 1).comp continuous_snd))

theorem continuous_polarRadialDerivative {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℂ) : Continuous (Function.uncurry (polarRadialDerivative u c)) := by
  exact ((hu.continuous_fderiv (by norm_num)).comp (continuous_polarPoint c)).clm_apply
    ((continuous_circleMap 0 1).comp continuous_snd)

theorem continuous_polarRadialFlux {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℂ) : Continuous (Function.uncurry (polarRadialFlux u c)) := by
  exact continuous_fst.mul (continuous_polarRadialDerivative hu c)

theorem continuous_polarHessian {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℂ) (a b : ℝ × ℝ → ℂ) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun p : ℝ × ℝ ↦ realHessian u (polarPoint c p.1 p.2) (a p) (b p)) := by
  simp only [realHessian_eq_fderiv]
  exact ((((hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).comp
    (continuous_polarPoint c)).clm_apply ha).clm_apply hb

/-- Differentiation under a finite interval integral for a continuously
parameter-dependent derivative. Compactness supplies the domination bound. -/
theorem hasDerivAt_intervalIntegral_of_jointly_continuous
    {F F' : ℝ → ℝ → ℝ} (hF : Continuous F.uncurry)
    (hF' : Continuous F'.uncurry) (hderiv : ∀ r θ, HasDerivAt (fun s ↦ F s θ) (F' r θ) r)
    (a b r : ℝ) :
    HasDerivAt (fun s ↦ ∫ θ in a..b, F s θ) (∫ θ in a..b, F' r θ) r := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall r 1).prod (isCompact_uIcc : IsCompact (uIcc a
      b))).exists_bound_of_continuousOn
      hF'.continuousOn
  have hFc (s : ℝ) : Continuous (F s) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hF'c (s : ℝ) : Continuous (F' s) :=
    hF'.comp (continuous_const.prodMk continuous_id)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := F') (bound := fun _ ↦ C) (s := ball r 1) (ball_mem_nhds r (by norm_num))
    ?_ ((hFc r).intervalIntegrable _ _) (hF'c r).aestronglyMeasurable
    ?_ (intervalIntegrable_const) ?_).2
  · exact Filter.Eventually.of_forall fun s ↦ (hFc s).aestronglyMeasurable
  · filter_upwards with θ hθ s hs
    exact hC (s, θ) ⟨ball_subset_closedBall hs, uIoc_subset_uIcc hθ⟩
  · filter_upwards with θ _ s _
    exact hderiv s θ

theorem integral_polarAngularDerivative_deriv_eq_zero {u : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u) (c : ℂ) (r : ℝ) :
    (∫ θ in 0..2 * π,
      r * realHessian u (polarPoint c r θ) (circleMap 0 1 θ * I) (circleMap 0 1 θ * I) -
        polarRadialDerivative u c r θ) = 0 := by
  have he : Continuous (fun p : ℝ × ℝ ↦ circleMap 0 1 p.2 * I) :=
    ((continuous_circleMap 0 1).comp continuous_snd).mul_const I
  have hp : Continuous (fun θ : ℝ ↦ (r, θ)) := continuous_const.prodMk continuous_id
  have hH := (continuous_polarHessian hu c _ _ he he).comp hp
  have hD := (continuous_polarRadialDerivative hu c).comp hp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ ↦ hasDerivAt_polarAngularDerivative hu c r θ)
    (((hH.const_mul r).sub hD).intervalIntegrable _ _)]
  have heq : circleMap 0 1 (2 * π) = circleMap 0 1 0 := by
    simpa using periodic_circleMap 0 1 0
  simp only [polarAngularDerivative, polarPoint, heq, sub_self]

/-- Total outward radial flux, without the normalizing factor `2π`. -/
def circleFluxIntegral (u : ℂ → ℝ) (c : ℂ) (r : ℝ) : ℝ :=
  ∫ θ in 0..2 * π, polarRadialFlux u c r θ

/-- Angular integration turns the polar divergence identity into a derivative
of the outward flux. This also holds at radius zero. -/
theorem hasDerivAt_circleFluxIntegral {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℂ) (r : ℝ) :
    HasDerivAt (circleFluxIntegral u c)
      (∫ θ in 0..2 * π, r * Δ u (polarPoint c r θ)) r := by
  let F' : ℝ → ℝ → ℝ := fun s θ ↦ polarRadialDerivative u c s θ +
    s * realHessian u (polarPoint c s θ) (circleMap 0 1 θ) (circleMap 0 1 θ)
  let G' : ℝ → ℝ := fun θ ↦ r *
    realHessian u (polarPoint c r θ) (circleMap 0 1 θ * I) (circleMap 0 1 θ * I) -
      polarRadialDerivative u c r θ
  have he : Continuous (fun p : ℝ × ℝ ↦ circleMap 0 1 p.2) :=
    (continuous_circleMap 0 1).comp continuous_snd
  have heI := he.mul_const I
  have hp : Continuous (fun θ : ℝ ↦ (r, θ)) := continuous_const.prodMk continuous_id
  have hF' : Continuous F'.uncurry := (continuous_polarRadialDerivative hu c).add
    (continuous_fst.mul (continuous_polarHessian hu c _ _ he he))
  have hG' : Continuous G' :=
    (((continuous_polarHessian hu c _ _ heI heI).comp hp).const_mul r).sub
      ((continuous_polarRadialDerivative hu c).comp hp)
  have hd := hasDerivAt_intervalIntegral_of_jointly_continuous
    (continuous_polarRadialFlux hu c) hF'
      (fun s θ ↦ hasDerivAt_polarRadialFlux hu c s θ) 0 (2 * π) r
  have hzero : (∫ θ in 0..2 * π, G' θ) = 0 :=
    integral_polarAngularDerivative_deriv_eq_zero hu c r
  have hsum : (∫ θ in 0..2 * π, F' r θ) =
      ∫ θ in 0..2 * π, r * Δ u (polarPoint c r θ) := by
    calc
      (∫ θ in 0..2 * π, F' r θ) =
          (∫ θ in 0..2 * π, F' r θ) + ∫ θ in 0..2 * π, G' θ := by rw [hzero, add_zero]
      _ = ∫ θ in 0..2 * π, F' r θ + G' θ :=
        (intervalIntegral.integral_add ((hF'.comp hp).intervalIntegrable _ _)
          (hG'.intervalIntegrable _ _)).symm
      _ = ∫ θ in 0..2 * π, r * Δ u (polarPoint c r θ) := by
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp [F', G']
        rw [← polar_hessian_trace u c r θ]
        ring
  change HasDerivAt (fun s ↦ ∫ θ in 0..2 * π, polarRadialFlux u c s θ) _ r
  rw [← hsum]
  exact hd

theorem hasDerivAt_circleAverage_radius {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℂ) (r : ℝ) :
    HasDerivAt (Real.circleAverage u c)
      ((2 * π)⁻¹ * ∫ θ in 0..2 * π, polarRadialDerivative u c r θ) r := by
  have hderiv (s θ : ℝ) : HasDerivAt (fun t ↦ u (polarPoint c t θ))
      (polarRadialDerivative u c s θ) s := by
    simpa only [Function.comp_def, polarRadialDerivative] using
      ((hu.differentiable (by norm_num)) (polarPoint c s θ)).hasFDerivAt.comp_hasDerivAt s
        (hasDerivAt_polarPoint_radius c s θ)
  have h := hasDerivAt_intervalIntegral_of_jointly_continuous
    (F := fun s θ ↦ u (polarPoint c s θ))
    (hu.continuous.comp (continuous_polarPoint c)) (continuous_polarRadialDerivative hu c)
    hderiv 0 (2 * π) r
  change HasDerivAt (fun s ↦ Real.circleAverage u c s) _ r
  simpa only [Real.circleAverage_def, polarPoint_eq_circleMap, smul_eq_mul] using!
    h.const_mul ((2 * π)⁻¹)

theorem polarPoint_mem_closedBall (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (θ : ℝ) : polarPoint c r θ ∈ closedBall c R := by
  rw [polarPoint_eq_circleMap]
  exact closedBall_subset_closedBall hrR (circleMap_mem_closedBall c hr θ)

@[simp] theorem circleFluxIntegral_zero (u : ℂ → ℝ) (c : ℂ) :
    circleFluxIntegral u c 0 = 0 := by
  simp [circleFluxIntegral, polarRadialFlux]

theorem circleFluxIntegral_monotoneOn {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℂ) {R : ℝ} (hΔ : ∀ z ∈ closedBall c R, 0 ≤ Δ u z) :
    MonotoneOn (circleFluxIntegral u c) (Icc 0 R) := by
  have hd : Differentiable ℝ (circleFluxIntegral u c) :=
    fun r ↦ (hasDerivAt_circleFluxIntegral hu c r).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    hd.continuous.continuousOn hd.differentiableOn
  intro r hr
  have hr' : r ∈ Icc 0 R := interior_subset hr
  rw [(hasDerivAt_circleFluxIntegral hu c r).deriv]
  apply intervalIntegral.integral_nonneg_of_forall (by positivity)
  intro θ
  exact mul_nonneg hr'.1 (hΔ _ (polarPoint_mem_closedBall c hr'.1 hr'.2 θ))

theorem circleFluxIntegral_nonneg {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℂ) {R r : ℝ} (hR : 0 ≤ R) (hΔ : ∀ z ∈ closedBall c R, 0 ≤ Δ u z)
    (hr : r ∈ Icc 0 R) : 0 ≤ circleFluxIntegral u c r := by
  simpa only [circleFluxIntegral_zero] using
    (circleFluxIntegral_monotoneOn hu c hΔ) ⟨le_rfl, hR⟩ hr hr.1

/-- A nonnegative Laplacian makes concentric circle averages monotone. -/
theorem circleAverage_monotoneOn_of_laplacian_nonneg {u : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hΔ : ∀ z ∈ closedBall c R, 0 ≤ Δ u z) :
    MonotoneOn (Real.circleAverage u c) (Icc 0 R) := by
  have hd : Differentiable ℝ (Real.circleAverage u c) :=
    fun r ↦ (hasDerivAt_circleAverage_radius hu c r).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    hd.continuous.continuousOn hd.differentiableOn
  intro r hr
  have hr' : 0 < r ∧ r < R := by simpa only [interior_Icc, mem_Ioo] using hr
  have hflux := circleFluxIntegral_nonneg hu c hR hΔ ⟨hr'.1.le, hr'.2.le⟩
  have hrad : 0 ≤ ∫ θ in 0..2 * π, polarRadialDerivative u c r θ := by
    apply (mul_nonneg_iff_of_pos_left hr'.1).mp
    simpa only [circleFluxIntegral, polarRadialFlux, intervalIntegral.integral_const_mul]
      using hflux
  rw [(hasDerivAt_circleAverage_radius hu c r).deriv]
  exact mul_nonneg (by positivity) hrad

/-- The classical submean inequality for a globally C² real function whose
Laplacian is nonnegative on the specified closed disc. -/
theorem submean_of_laplacian_nonneg {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (hΔ : ∀ z ∈ closedBall c R, 0 ≤ Δ u z) :
    u c ≤ Real.circleAverage u c R := by
  have h := (circleAverage_monotoneOn_of_laplacian_nonneg hu c hR hΔ)
    ⟨le_rfl, hR⟩ ⟨hR, le_rfl⟩ hR
  simpa only [Real.circleAverage_zero] using h

end SGPT.Foundations.Analysis
