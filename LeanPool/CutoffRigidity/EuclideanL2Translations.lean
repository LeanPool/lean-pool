/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EuclideanDerivatives
public import LeanPool.CutoffRigidity.RealL2Identities
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual Euclidean L² translation estimates

The proof uses line FTC, actual Jensen on the uniform unit interval,
Tonelli and Haar translation invariance. No compact embedding is assumed.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual unit-interval Lebesgue probability measure. -/
@[expose] noncomputable def unitIntervalLebesgue : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance unitIntervalLebesgue_isProbabilityMeasure : IsProbabilityMeasure unitIntervalLebesgue where
  measure_univ := by simp [unitIntervalLebesgue]

/-- Actual line FTC, expressed using the genuine gradient and the actual
uniform unit-interval measure. -/
theorem c1_translation_line_integral {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x h : E) :
    (∫ t, inner ℝ (gradient f (x + t • h)) h ∂unitIntervalLebesgue) = f (x + h) - f x := by
  have hG : Continuous (gradient f) := continuous_gradient_of_c1 hf
  have hc : Continuous (fun t : ℝ => inner ℝ (gradient f (x + t • h)) h) := by fun_prop
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => f (x + s • h))
      (inner ℝ (gradient f (x + t • h)) h) t := by
    have hl : HasDerivAt (fun s : ℝ => x + s • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have hh := ((hf.differentiable (by norm_num)) (x + t • h)).hasFDerivAt.comp_hasDerivAt t hl
    simpa only [Function.comp_def, inner_gradient_left] using hh
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc (0 : ℝ) 1) => hd t) (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at hi
  simpa only [unitIntervalLebesgue, one_smul, zero_smul, add_zero] using hi

/-- Pointwise squared translation control by the genuine averaged gradient
energy along the line segment. -/
theorem c1_translation_sq_le_line_energy {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x h : E) :
    (f (x + h) - f x) ^ 2 ≤ ‖h‖ ^ 2 *
      ∫ t, ‖gradient f (x + t • h)‖ ^ 2 ∂unitIntervalLebesgue := by
  have hG : Continuous (gradient f) := continuous_gradient_of_c1 hf
  let g (t : ℝ) := inner ℝ (gradient f (x + t • h)) h
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hg2 : Integrable (fun t => g t ^ 2) unitIntervalLebesgue := (hg.pow 2).integrableOn_Icc
  have hgLp : MemLp g 2 unitIntervalLebesgue :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hg2
  have hj := variance_nonneg g unitIntervalLebesgue
  rw [variance_eq_sub hgLp] at hj
  have hFTC := c1_translation_line_integral hf x h
  change (∫ t, g t ∂unitIntervalLebesgue) = f (x + h) - f x at hFTC
  have hnorm : Integrable (fun t : ℝ => ‖gradient f (x + t • h)‖ ^ 2) unitIntervalLebesgue :=
    (show Continuous (fun t : ℝ => ‖gradient f (x + t • h)‖ ^ 2) by fun_prop).integrableOn_Icc
  have hpoint (t : ℝ) : g t ^ 2 ≤ ‖h‖ ^ 2 * ‖gradient f (x + t • h)‖ ^ 2 := by
    have hh := abs_real_inner_le_norm (gradient f (x + t • h)) h
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hh
    simpa only [sq_abs, mul_pow, mul_comm] using hs
  have hi := integral_mono hg2 (hnorm.const_mul (‖h‖ ^ 2)) hpoint
  rw [integral_const_mul] at hi
  simp only [Pi.pow_apply] at hj
  rw [hFTC] at hj
  linarith

/-- Compact C¹ functions have genuine Lebesgue L² gradients. -/
theorem c1_compact_gradient_memLp {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    MemLp (gradient f) 2 volume := by
  have hc : HasCompactSupport (gradient f) :=
    (hfc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
  exact (continuous_gradient_of_c1 hf).memLp_of_hasCompactSupport hc

/-- Compact C¹ functions have genuine Lebesgue L² translation differences. -/
theorem c1_compact_translation_memLp {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
  (h : E) :
    MemLp (fun x => f (x + h) - f x) 2 volume := by
  have hfLp : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hfc
  simpa only [Function.comp_def, Pi.sub_def] using
    (hfLp.comp_measurePreserving (measurePreserving_add_right volume h)).sub hfLp

/-- The actual Lebesgue squared translation estimate, obtained by line FTC,
Jensen, Tonelli and Haar invariance. -/
theorem c1_compact_translation_integral_sq_le {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (h : E) :
    (∫ x, (f (x + h) - f x) ^ 2) ≤ ‖h‖ ^ 2 * ∫ x, ‖gradient f x‖ ^ 2 := by
  have hG : Continuous (gradient f) := continuous_gradient_of_c1 hf
  have hE : Integrable (fun x => ‖gradient f x‖ ^ 2) volume :=
    (c1_compact_gradient_memLp hf hfc).norm.integrable_sq
  have hD : Integrable (fun x => (f (x + h) - f x) ^ 2) volume :=
    (c1_compact_translation_memLp hf hfc h).integrable_sq
  let F (x : E) (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (‖gradient f (x + t • h)‖ ^ 2)
  have hFm : Measurable (Function.uncurry F) := by
    have hc : Continuous (fun p : E × ℝ => ‖gradient f (p.1 + p.2 • h)‖ ^ 2) := by fun_prop
    exact hc.measurable.ennreal_ofReal
  have hpoint (x : E) : ENNReal.ofReal ((f (x + h) - f x) ^ 2) ≤
      ENNReal.ofReal (‖h‖ ^ 2) * ∫⁻ t, F x t ∂unitIntervalLebesgue := by
    have ht : Integrable (fun t : ℝ => ‖gradient f (x + t • h)‖ ^ 2) unitIntervalLebesgue :=
      (show Continuous (fun t : ℝ => ‖gradient f (x + t • h)‖ ^ 2) by fun_prop).integrableOn_Icc
    have hh := ENNReal.ofReal_le_ofReal (c1_translation_sq_le_line_energy hf x h)
    rw [ENNReal.ofReal_mul (sq_nonneg _), ofReal_integral_eq_lintegral_ofReal ht
      (Filter.Eventually.of_forall fun t => sq_nonneg _)] at hh
    exact hh
  have hi := lintegral_mono (μ := (volume : Measure E)) hpoint
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_lintegral_swap hFm.aemeasurable] at hi
  have hHaar (t : ℝ) : (∫⁻ x, F x t) = ∫⁻ x, ENNReal.ofReal (‖gradient f x‖ ^ 2) :=
    lintegral_add_right_eq_self (fun x => ENNReal.ofReal (‖gradient f x‖ ^ 2)) (t • h)
  simp_rw [hHaar] at hi
  simp only [lintegral_const, measure_univ, mul_one] at hi
  rw [← ofReal_integral_eq_lintegral_ofReal hD (Filter.Eventually.of_forall fun x => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hE (Filter.Eventually.of_forall fun x => sq_nonneg _),
    ← ENNReal.ofReal_mul (sq_nonneg _)] at hi
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (integral_nonneg fun x => sq_nonneg
    _))).mp hi

/-- The requested actual L² translation norm estimate for compact C¹ functions. -/
theorem c1_compact_translation_L2_norm_le {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (h : E) :
    ‖(c1_compact_translation_memLp hf hfc h).toLp (fun x => f (x + h) - f x)‖ ≤
      ‖h‖ * ‖(c1_compact_gradient_memLp hf hfc).toLp (gradient f)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [norm_toLp_sq (c1_compact_translation_memLp hf hfc h), mul_pow, norm_toLp_norm_sq]
  exact c1_compact_translation_integral_sq_le hf hfc h

end CutoffRigidity
