/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.IntermediateValue

/-!
# The normal CDF and strict distribution functions

One-dimensional ingredients for the strict-CDF convention in KPZ Definition 3.5 and
LX26 Lemmas 2.5–2.6. In particular, strict and closed distribution functions agree for a
nondegenerate normal law, but this identification is not asserted for arbitrary laws.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Topology

namespace EhrhardGaussian.EhrhardType

/-- An atomless probability law has the same strict and closed CDF. -/
theorem strictCDF_eq_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (a : ℝ) :
    (μ (Iio a)).toReal = cdf μ a := by
  rw [measure_congr Iio_ae_eq_Iic, cdf_eq_real]
  rfl

/-- A probability CDF is continuous wherever its law has no atoms. -/
theorem continuous_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ) := by
  refine continuous_iff_continuousAt.mpr fun a => ?_
  have hatom := (cdf μ).measure_singleton a
  rw [measure_cdf, measure_singleton] at hatom
  have hle : cdf μ a ≤ Function.leftLim (cdf μ) a := by
    exact sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hatom.symm)
  have heq : Function.leftLim (cdf μ) a = cdf μ a :=
    le_antisymm ((monotone_cdf μ).leftLim_le le_rfl) hle
  apply ((monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim).mpr
  rw [heq, (cdf μ).rightLim_eq]

/-- A probability law charging every open interval has strictly increasing CDF. -/
theorem strictMono_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [IsOpenPosMeasure μ] : StrictMono (cdf μ) := by
  intro a b hab
  have hpos : 0 < μ (Ioc a b) :=
    (isOpen_Ioo.measure_pos μ (nonempty_Ioo.mpr hab)).trans_le
      (measure_mono Ioo_subset_Ioc_self)
  have hposreal : 0 < (μ (Ioc a b)).toReal :=
    ENNReal.toReal_pos hpos.ne' (measure_ne_top μ _)
  have hinterval := (cdf μ).measure_Ioc a b
  rw [measure_cdf] at hinterval
  have hdiff : (μ (Ioc a b)).toReal = cdf μ b - cdf μ a := by
    rw [hinterval, ENNReal.toReal_ofReal (sub_nonneg.mpr ((monotone_cdf μ) hab.le))]
  rw [hdiff] at hposreal
  exact sub_pos.mp hposreal

/-- A full-support probability CDF takes values strictly between zero and one. -/
theorem cdf_mem_Ioo (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [IsOpenPosMeasure μ] (a : ℝ) : cdf μ a ∈ Ioo 0 1 := by
  constructor
  · exact (cdf_nonneg μ (a - 1)).trans_lt (strictMono_cdf μ (by linarith))
  · exact (strictMono_cdf μ (show a < a + 1 by linarith)).trans_le (cdf_le_one μ _)

/-- Nondegenerate normal laws charge every nonempty open set. -/
theorem isOpenPosMeasure_gaussianReal (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    IsOpenPosMeasure (gaussianReal m v) :=
  (gaussianReal_absolutelyContinuous' m hv).isOpenPosMeasure

/-- The standard Gaussian's strict CDF equals Mathlib's closed CDF. -/
theorem strictCDF_standardGaussian (a : ℝ) :
    ((gaussianReal 0 1) (Iio a)).toReal = cdf (gaussianReal 0 1) a := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  exact strictCDF_eq_cdf _ a

/-- Strict increase of the standard Gaussian CDF. -/
theorem strictMono_standardGaussian_cdf : StrictMono (cdf (gaussianReal 0 1)) := by
  have := isOpenPosMeasure_gaussianReal 0 (v := 1) one_ne_zero
  exact strictMono_cdf _

/-- Continuity of the standard Gaussian CDF. -/
theorem continuous_standardGaussian_cdf : Continuous (cdf (gaussianReal 0 1)) := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  exact continuous_cdf _

/-- No finite standard Gaussian threshold has probability zero or one. -/
theorem standardGaussian_cdf_mem_Ioo (a : ℝ) : cdf (gaussianReal 0 1) a ∈ Ioo 0 1 := by
  have := isOpenPosMeasure_gaussianReal 0 (v := 1) one_ne_zero
  exact cdf_mem_Ioo _ a

/-- The range of the standard Gaussian CDF is exactly the open unit interval. -/
theorem range_standardGaussian_cdf :
    Set.range (cdf (gaussianReal 0 1)) = Ioo 0 1 := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact standardGaussian_cdf_mem_Ioo x
  · intro y hy
    have h := isPreconnected_univ.intermediate_value_Ioo
      (l₁ := atBot) (l₂ := atTop) (by simp only [principal_univ, le_top])
      (by simp only [principal_univ, le_top]) continuous_standardGaussian_cdf.continuousOn
      (tendsto_cdf_atBot (gaussianReal 0 1)) (tendsto_cdf_atTop (gaussianReal 0 1)) hy
    rcases h with ⟨x, _, hx⟩
    exact ⟨x, hx⟩

/-- Every probability strictly between zero and one has a unique finite normal quantile. -/
theorem existsUnique_standardGaussian_quantile {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃! x : ℝ, cdf (gaussianReal 0 1) x = p := by
  obtain ⟨x, hx⟩ := range_standardGaussian_cdf.symm ▸ hp
  exact ⟨x, hx, fun y hy => strictMono_standardGaussian_cdf.injective (hy.trans hx.symm)⟩

end EhrhardGaussian.EhrhardType
