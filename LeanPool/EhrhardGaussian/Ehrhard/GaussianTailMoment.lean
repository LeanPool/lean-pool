/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import LeanPool.EhrhardGaussian.Ehrhard.HalfLineExtremizer
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Ring

/-! Integrating the identity x φ(x) = −φ′(x) expresses the extremal Gaussian tail first moment in
terms of its density. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

namespace EhrhardGaussian.Ehrhard

/-- The standard Gaussian density is the normalized exponential of minus half the squared argument.
-/
theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]

/-- The derivative needed for integration of the Gaussian first moment. -/
theorem hasDerivAt_neg_gaussianPDFReal (x : ℝ) :
    HasDerivAt (fun x => -gaussianPDFReal 0 1 x) (x * gaussianPDFReal 0 1 x) x := by
  simp_rw [gaussianPDFReal_zero_one]
  convert (((((hasDerivAt_id' x).pow 2).neg.div_const 2).exp).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹).neg using 1
  simp only [Pi.neg_apply, Pi.pow_apply]
  ring

/-- The first absolute moment of the standard Gaussian density is finite. -/
theorem integrable_mul_gaussianPDFReal :
    Integrable (fun x => x * gaussianPDFReal 0 1 x) := by
  have h := (integrable_mul_exp_neg_mul_sq (by norm_num : 0 < (1 / 2 : ℝ))).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert h using 1
  ext x
  rw [gaussianPDFReal_zero_one]
  have hexp : -x ^ 2 / 2 = -(1 / 2) * x ^ 2 := by ring
  rw [hexp]
  ring

/-- The standard Gaussian density tends to zero at positive infinity. -/
theorem tendsto_gaussianPDFReal_atTop :
    Tendsto (gaussianPDFReal 0 1) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_atBot.comp
    ((tendsto_pow_atTop (by decide : 2 ≠ 0)).const_mul_atTop_of_neg
      (by norm_num : (-1 / 2 : ℝ) < 0))
  have h' := h.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  convert h' using 1
  · ext x
    rw [gaussianPDFReal_zero_one]
    congr 2
    ring
  · rw [mul_zero]

/-- The (unnormalized) first moment on an upper Gaussian half-line equals its density. -/
theorem integral_Ioi_id_gaussianReal (c : ℝ) :
    ∫ x in Ioi c, x ∂gaussianReal 0 1 = gaussianPDFReal 0 1 c := by
  have htail : ∫ x in Ioi c, x * gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 c := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x (_ : x ∈ Ici c) => hasDerivAt_neg_gaussianPDFReal x)
      integrable_mul_gaussianPDFReal.integrableOn tendsto_gaussianPDFReal_atTop.neg
    simpa only [neg_zero, sub_neg_eq_add, zero_add] using h
  rw [← integral_indicator measurableSet_Ioi,
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  calc
    (∫ x, gaussianPDFReal 0 1 x • (Ioi c).indicator (fun x : ℝ => x) x) =
        ∫ x, (Ioi c).indicator (fun x => x * gaussianPDFReal 0 1 x) x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        by_cases hx : x ∈ Ioi c
        · rw [indicator_of_mem hx, indicator_of_mem hx, smul_eq_mul, mul_comm]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]
    _ = gaussianPDFReal 0 1 c := by
      rw [integral_indicator measurableSet_Ioi, htail]

/-- The direct upper scalar Gaussian bound, with the threshold specified by its tail mass.
This formulation needs no inverse-CDF convention at zero or one. -/
theorem integral_mul_le_gaussianPDFReal {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Icc (0 : ℝ) 1) (c : ℝ)
    (hmean : ∫ x, f x ∂gaussianReal 0 1 = ((gaussianReal 0 1) (Ioi c)).toReal) :
    ∫ x, x * f x ∂gaussianReal 0 1 ≤ gaussianPDFReal 0 1 c := by
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  have hmean' : ∫ x, f x ∂gaussianReal 0 1 =
      ∫ x, (Ioi c).indicator (fun _ : ℝ => (1 : ℝ)) x ∂gaussianReal 0 1 := by
    rw [integral_indicator_const (1 : ℝ) measurableSet_Ioi, smul_eq_mul, mul_one]
    exact hmean
  exact (integral_mul_le_integral_Ioi hid hf hbound c hmean').trans_eq
    (integral_Ioi_id_gaussianReal c)

/-- Reflection invariance, with an explicit measurability premise for the integrand. -/
theorem integral_comp_neg_gaussianReal (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ x, g (-x) ∂gaussianReal 0 1 = ∫ x, g x ∂gaussianReal 0 1 := by
  calc
    (∫ x, g (-x) ∂gaussianReal 0 1) =
        ∫ x, g x ∂((gaussianReal 0 1).map (fun x : ℝ => -x)) :=
      (integral_map (by fun_prop) hg.aestronglyMeasurable).symm
    _ = ∫ x, g x ∂gaussianReal 0 1 := by rw [gaussianReal_map_neg, neg_zero]

/-- The sharp two-sided first-moment estimate for a bounded scalar Gaussian function.
The mean is parametrized by an upper half-line, including every mean in `(0,1)`.
This is the extremizer step of the direct smoothing-gradient proof. -/
theorem abs_integral_mul_le_gaussianPDFReal {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Icc (0 : ℝ) 1) (c : ℝ)
    (hmean : ∫ x, f x ∂gaussianReal 0 1 = ((gaussianReal 0 1) (Ioi c)).toReal) :
    |∫ x, x * f x ∂gaussianReal 0 1| ≤ gaussianPDFReal 0 1 c := by
  have hu := integral_mul_le_gaussianPDFReal hf hbound c hmean
  have hmean' : ∫ x, f (-x) ∂gaussianReal 0 1 =
      ((gaussianReal 0 1) (Ioi c)).toReal := by
    rw [integral_comp_neg_gaussianReal f hf, hmean]
  have hl := integral_mul_le_gaussianPDFReal (hf.comp measurable_neg)
    (fun x => hbound (-x)) c hmean'
  change (∫ x, x * f (-x) ∂gaussianReal 0 1) ≤ gaussianPDFReal 0 1 c at hl
  have hreflect := integral_comp_neg_gaussianReal (fun x => x * f x)
    (measurable_id.mul hf)
  simp only [neg_mul, integral_neg] at hreflect
  exact abs_le.mpr ⟨by linarith only [hl, hreflect], hu⟩

end EhrhardGaussian.Ehrhard
