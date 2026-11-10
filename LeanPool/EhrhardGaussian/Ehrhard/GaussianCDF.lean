/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianTailMoment
public import Mathlib.Probability.CDF
public import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# The standard Gaussian CDF as a smooth coordinate chart

The derivative follows from its density and the fundamental theorem of
calculus. Strict monotonicity and the endpoint limits identify the range
with `(0,1)`. The inverse is used only on this open probability interval.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

namespace EhrhardGaussian.Ehrhard

/-- Standard Gaussian cumulative distribution function. -/
def gaussianCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The Gaussian distribution function is the integral of the Gaussian density over the left
half-line. -/
theorem gaussianCDF_eq_integral (x : ℝ) :
    gaussianCDF x = ∫ z in Iic x, gaussianPDFReal 0 1 z := by
  rw [gaussianCDF, cdf_eq_real, Measure.real,
    gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    ENNReal.toReal_ofReal]
  exact integral_nonneg (fun z => gaussianPDFReal_nonneg 0 1 z)

/-- The Gaussian distribution function differs from its value at zero by the intervening density
integral. -/
theorem gaussianCDF_eq_integral_add (x : ℝ) :
    gaussianCDF x = gaussianCDF 0 + ∫ z in (0 : ℝ)..x, gaussianPDFReal 0 1 z := by
  rw [gaussianCDF_eq_integral, gaussianCDF_eq_integral]
  have h := intervalIntegral.integral_Iic_sub_Iic
    (a := (0 : ℝ)) (b := x) (integrable_gaussianPDFReal 0 1).integrableOn
    (integrable_gaussianPDFReal 0 1).integrableOn
  exact (eq_add_of_sub_eq h).trans (add_comm _ _)

/-- The standard Gaussian density is continuous. -/
theorem continuous_gaussianPDFReal : Continuous (gaussianPDFReal 0 1) := by
  change Continuous (fun x : ℝ => gaussianPDFReal 0 1 x)
  simp_rw [gaussianPDFReal_zero_one]
  fun_prop

/-- The derivative of the Gaussian distribution function is the Gaussian density. -/
theorem hasDerivAt_gaussianCDF (x : ℝ) :
    HasDerivAt gaussianCDF (gaussianPDFReal 0 1 x) x := by
  have h := (continuous_gaussianPDFReal.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add
    (gaussianCDF 0)
  simpa only [← gaussianCDF_eq_integral_add] using h

/-- The Gaussian distribution function is continuous. -/
theorem continuous_gaussianCDF : Continuous gaussianCDF :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_gaussianCDF x).continuousAt

/-- The Gaussian distribution function is strictly increasing. -/
theorem strictMono_gaussianCDF : StrictMono gaussianCDF := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_gaussianCDF x).deriv]
  exact gaussianPDFReal_pos 0 1 x (by norm_num)

/-- The Gaussian distribution function is strictly positive at every real argument. -/
theorem gaussianCDF_pos (x : ℝ) : 0 < gaussianCDF x :=
  (cdf_nonneg (gaussianReal 0 1) (x - 1)).trans_lt
    (strictMono_gaussianCDF (sub_one_lt x))

/-- The Gaussian distribution function is strictly less than one at every real argument. -/
theorem gaussianCDF_lt_one (x : ℝ) : gaussianCDF x < 1 :=
  (strictMono_gaussianCDF (lt_add_one x)).trans_le (cdf_le_one (gaussianReal 0 1) (x + 1))

/-- The range of the Gaussian distribution function is the open interval from zero to one. -/
theorem range_gaussianCDF : range gaussianCDF = Ioo (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨gaussianCDF_pos x, gaussianCDF_lt_one x⟩
  · have h := isPreconnected_univ.intermediate_value_Ioo
      (f := gaussianCDF) (l₁ := atBot) (l₂ := atTop) (by rw [principal_univ]; exact le_top)
      (by rw [principal_univ]; exact le_top)
      continuous_gaussianCDF.continuousOn
      (tendsto_cdf_atBot (gaussianReal 0 1)) (tendsto_cdf_atTop (gaussianReal 0 1))
    simpa only [image_univ] using h

/-- The Gaussian CDF is an order isomorphism onto the open probability interval. -/
def gaussianCDFOrderIso : ℝ ≃o Ioo (0 : ℝ) 1 :=
  (StrictMono.orderIsoOfSurjective
    (fun x => (⟨gaussianCDF x, gaussianCDF_pos x, gaussianCDF_lt_one x⟩ : Ioo (0 : ℝ) 1))
    (fun _ _ h => strictMono_gaussianCDF h)
    (fun p => by
      have hp : (p : ℝ) ∈ range gaussianCDF := by
        rw [range_gaussianCDF]
        exact p.property
      obtain ⟨x, hx⟩ := hp
      exact ⟨x, Subtype.ext hx⟩))





/-- The Gaussian distribution function is an open embedding of the real line. -/
theorem isOpenEmbedding_gaussianCDF : Topology.IsOpenEmbedding gaussianCDF :=
  isOpen_Ioo.isOpenEmbedding_subtypeVal.comp gaussianCDFOrderIso.toHomeomorph.isOpenEmbedding

/-- The CDF chart has source all of `ℝ` and target the open probability interval.
Its partial inverse is an ambient representative for differentiation on that interval. -/
def gaussianCDFChart : OpenPartialHomeomorph ℝ ℝ :=
  isOpenEmbedding_gaussianCDF.toOpenPartialHomeomorph gaussianCDF


/-- The target of the Gaussian probability chart is the open interval from zero to one. -/
theorem gaussianCDFChart_target : gaussianCDFChart.target = Ioo (0 : ℝ) 1 := by
  rw [gaussianCDFChart, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
    range_gaussianCDF]


/-- The inverse-CDF derivative, only at interior probabilities. -/
theorem hasDerivAt_gaussianCDFChart_symm {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt gaussianCDFChart.symm
      (gaussianPDFReal 0 1 (gaussianCDFChart.symm p))⁻¹ p := by
  apply gaussianCDFChart.hasDerivAt_symm
    (gaussianCDFChart_target.symm ▸ hp)
    (gaussianPDFReal_pos 0 1 _ (by norm_num)).ne'
  exact hasDerivAt_gaussianCDF _

/-- Differentiating the reciprocal profile produces the diagonal second
derivative of the inverse CDF. -/
theorem hasDerivAt_inv_gaussianDensity_quantile {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => (gaussianPDFReal 0 1 (gaussianCDFChart.symm y))⁻¹)
      (gaussianCDFChart.symm p / (gaussianPDFReal 0 1 (gaussianCDFChart.symm p)) ^ 2) p := by
  have hq := hasDerivAt_gaussianCDFChart_symm hp
  have hφ : HasDerivAt (gaussianPDFReal 0 1)
      (-(gaussianCDFChart.symm p * gaussianPDFReal 0 1 (gaussianCDFChart.symm p)))
      (gaussianCDFChart.symm p) := by
    simpa only [Pi.neg_def, neg_neg] using
      (hasDerivAt_neg_gaussianPDFReal (gaussianCDFChart.symm p)).neg
  have hne := (gaussianPDFReal_pos 0 1 (gaussianCDFChart.symm p) (by norm_num)).ne'
  have h := (hφ.comp (h := gaussianCDFChart.symm) p hq).inv hne
  simp only [Pi.inv_def, Function.comp_def] at h
  convert h using 1
  field_simp

end EhrhardGaussian.Ehrhard

end
