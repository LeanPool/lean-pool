/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianSmoothClass
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Joint regularity of Gaussian linear averages

Allowing the parameter to contain both the center and the scale gives joint
space-time regularity after composition with the OU coefficient curves.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (standardGaussianMeasure)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiation passes through a Gaussian linear average under polynomial growth bounds. -/
theorem hasFDerivAt_gaussianLinearAverage {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiff ℝ 1 F) {J : (Fin n → ℝ) → E →L[ℝ] (Fin n → ℝ)}
    (hJ : Continuous J) {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) {N : ℕ}
    (hJbound : ∀ z, ‖J z‖ ≤ L * (1 + ‖z‖))
    (hFbound : ∀ y, |F y| + ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖) ^ N)
    (p₀ : E) :
    HasFDerivAt (fun p => ∫ z, F (J z p) ∂standardGaussianMeasure n)
      (∫ z, (fderiv ℝ F (J z p₀)).comp (J z) ∂standardGaussianMeasure n) p₀ ∧
    ContinuousAt (fun p => ∫ z, (fderiv ℝ F (J z p)).comp (J z)
      ∂standardGaussianMeasure n) p₀ := by
  let B := 1 + L * (‖p₀‖ + 1)
  let K := C * B ^ N * L
  let D : E → (Fin n → ℝ) → E →L[ℝ] ℝ :=
    fun p z => (fderiv ℝ F (J z p)).comp (J z)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have harg (p : E) : Continuous (fun z => J z p) := hJ.clm_apply continuous_const
  have hmeas (p : E) : AEStronglyMeasurable (fun z => F (J z p))
      (standardGaussianMeasure n) := (hF.continuous.comp (harg p)).measurable.aestronglyMeasurable
  have hDmeas (p : E) : AEStronglyMeasurable (D p) (standardGaussianMeasure n) :=
    (((hF.continuous_fderiv (by norm_num)).comp (harg p)).clm_comp hJ).aestronglyMeasurable
  have hnorm (p : E) (hp : p ∈ Metric.ball p₀ 1) (z : Fin n → ℝ) :
      1 + ‖J z p‖ ≤ B * (1 + ‖z‖) := by
    have hpbound : ‖p‖ ≤ ‖p₀‖ + 1 :=
      norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hp).le
    have hjp : ‖J z p‖ ≤ L * (1 + ‖z‖) * (‖p₀‖ + 1) :=
      ((J z).le_opNorm p).trans
        (mul_le_mul (hJbound z) hpbound (norm_nonneg _) (by positivity))
    dsimp only [B]
    nlinarith only [hjp, norm_nonneg z]
  have hvalue : Integrable (fun z => F (J z p₀)) (standardGaussianMeasure n) := by
    apply integrable_of_pi_polynomial_bound
      (hF.continuous.comp (harg p₀)).measurable
      (C := C * B ^ N) (mul_nonneg hC (pow_nonneg hB _)) (d := N)
    intro z
    calc
      |F (J z p₀)| ≤ C * (1 + ‖J z p₀‖) ^ N :=
        (le_add_of_nonneg_right (norm_nonneg _)).trans (hFbound _)
      _ ≤ C * (B * (1 + ‖z‖)) ^ N := by
        gcongr
        exact hnorm p₀ (Metric.mem_ball_self zero_lt_one) z
      _ = C * B ^ N * (1 + ‖z‖) ^ N := by rw [mul_pow]; ring
  have hmajor : Integrable (fun z : Fin n → ℝ => K * (1 + ‖z‖) ^ (N + 1))
      (standardGaussianMeasure n) := by
    apply integrable_of_pi_polynomial_bound (by fun_prop) hK (d := N + 1)
    intro z
    exact (abs_of_nonneg (mul_nonneg hK (pow_nonneg (by positivity) _))).le
  have hdom : ∀ᵐ z ∂standardGaussianMeasure n, ∀ p ∈ Metric.ball p₀ 1,
      ‖D p z‖ ≤ K * (1 + ‖z‖) ^ (N + 1) := by
    apply ae_of_all
    intro z p hp
    have hdf : ‖fderiv ℝ F (J z p)‖ ≤ C * B ^ N * (1 + ‖z‖) ^ N := by
      calc
        ‖fderiv ℝ F (J z p)‖ ≤ C * (1 + ‖J z p‖) ^ N :=
          (le_add_of_nonneg_left (abs_nonneg _)).trans (hFbound _)
        _ ≤ C * (B * (1 + ‖z‖)) ^ N := by gcongr; exact hnorm p hp z
        _ = C * B ^ N * (1 + ‖z‖) ^ N := by rw [mul_pow]; ring
    calc
      ‖D p z‖ ≤ ‖fderiv ℝ F (J z p)‖ * ‖J z‖ :=
        (fderiv ℝ F (J z p)).opNorm_comp_le (J z)
      _ ≤ (C * B ^ N * (1 + ‖z‖) ^ N) * (L * (1 + ‖z‖)) :=
        mul_le_mul hdf (hJbound z) (norm_nonneg _) (by positivity)
      _ = K * (1 + ‖z‖) ^ (N + 1) := by dsimp only [K]; rw [pow_succ]; ring
  have hdiff : ∀ᵐ z ∂standardGaussianMeasure n, ∀ p ∈ Metric.ball p₀ 1,
      HasFDerivAt (fun q => F (J z q)) (D p z) p := by
    exact ae_of_all _ fun z p _ => (hF.differentiable_one _).hasFDerivAt.comp p (J z).hasFDerivAt
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds p₀ zero_lt_one) (Filter.Eventually.of_forall hmeas)
    hvalue (hDmeas p₀) hdom hmajor hdiff
  have hDcont (z : Fin n → ℝ) : ContinuousAt (fun p => D p z) p₀ :=
    (((hF.continuous_fderiv (by norm_num)).comp (J z).continuous).clm_comp
      continuous_const).continuousAt
  have hDdom : ∀ᶠ p in 𝓝 p₀, ∀ᵐ z ∂standardGaussianMeasure n,
      ‖D p z‖ ≤ K * (1 + ‖z‖) ^ (N + 1) := by
    filter_upwards [Metric.ball_mem_nhds p₀ zero_lt_one] with p hp
    exact hdom.mono fun z hz => hz p hp
  exact ⟨hderiv, continuousAt_of_dominated (Filter.Eventually.of_forall hDmeas)
    hDdom hmajor (ae_of_all _ hDcont)⟩

/-- A Gaussian linear average is continuously differentiable under polynomial growth bounds. -/
theorem contDiff_one_gaussianLinearAverage {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiff ℝ 1 F) {J : (Fin n → ℝ) → E →L[ℝ] (Fin n → ℝ)}
    (hJ : Continuous J) {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) {N : ℕ}
    (hJbound : ∀ z, ‖J z‖ ≤ L * (1 + ‖z‖))
    (hFbound : ∀ y, |F y| + ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖) ^ N) :
    ContDiff ℝ 1 (fun p => ∫ z, F (J z p) ∂standardGaussianMeasure n) := by
  rw [contDiff_one_iff_hasFDerivAt]
  exact ⟨_, continuous_iff_continuousAt.mpr (fun p =>
    (hasFDerivAt_gaussianLinearAverage hF hJ hL hC hJbound hFbound p).2),
    fun p => (hasFDerivAt_gaussianLinearAverage hF hJ hL hC hJbound hFbound p).1⟩

end EhrhardGaussian.Ehrhard

end
