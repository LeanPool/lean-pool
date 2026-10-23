/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! # The probability integral transform for continuous CDFs

Continuity, rather than strict monotonicity, suffices. In particular, this
result allows gaps in the support of a distribution.
-/

public section

open MeasureTheory Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory

/-- A real CDF bundled with its values in the unit interval. -/
@[expose]
noncomputable def cdfUnit (μ : Measure ℝ) (x : ℝ) : I :=
  ⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩

@[simp]
theorem coe_cdfUnit (μ : Measure ℝ) (x : ℝ) : (cdfUnit μ x : ℝ) = cdf μ x := rfl

@[fun_prop]
theorem measurable_cdfUnit (μ : Measure ℝ) : Measurable (cdfUnit μ) :=
  (monotone_cdf μ).measurable.subtype_mk

theorem exists_cdf_eq_of_continuous (μ : Measure ℝ) (hc : Continuous (cdf μ))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : ∃ x, cdf μ x = t := by
  exact mem_range_of_exists_le_of_exists_ge hc
    ((tendsto_cdf_atBot μ).eventually_le_const ht0).exists
    ((tendsto_cdf_atTop μ).eventually_const_le ht1).exists

/-- An atomless real probability measure has a continuous CDF. -/
theorem continuous_cdf_of_atomless (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [(cdf μ).rightLim_eq]
  apply le_antisymm ((monotone_cdf μ).leftLim_le le_rfl)
  have h := (cdf μ).measure_singleton x
  rw [measure_cdf, measure_singleton] at h
  exact sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp h.symm)

/-- Applying a continuous CDF to a variable with that law gives a uniform variable. -/
theorem map_cdfUnit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) : μ.map (cdfUnit μ) = volume := by
  apply Measure.ext_of_Iic
  intro u
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (μ.map (cdfUnit μ)).real (Iic u) = volume.real (Iic u)
  rw [map_measureReal_apply (measurable_cdfUnit μ) measurableSet_Iic]
  have hvol : volume.real (Iic u) = (u : ℝ) := by
    simp [Measure.real, u.property.1]
  rw [hvol]
  change μ.real {x | cdf μ x ≤ (u : ℝ)} = (u : ℝ)
  apply le_antisymm
  · by_contra! h
    obtain ⟨r, hur, hr⟩ := exists_between h
    have hr0 : 0 < r := lt_of_le_of_lt u.property.1 hur
    have hr1 : r < 1 := hr.trans_le measureReal_le_one
    obtain ⟨y, hy⟩ := exists_cdf_eq_of_continuous μ hc hr0 hr1
    have hsub : {x | cdf μ x ≤ (u : ℝ)} ⊆ Iic y := by
      intro x hx
      change x ≤ y
      by_contra! hxy
      have hm := monotone_cdf μ hxy.le
      change cdf μ x ≤ (u : ℝ) at hx
      linarith
    have hm := measureReal_mono (μ := μ) hsub
    rw [← cdf_eq_real, hy] at hm
    linarith
  · by_cases hu0 : (u : ℝ) = 0
    · rw [hu0]
      exact measureReal_nonneg
    by_cases hu1 : (u : ℝ) = 1
    · have he : {x | cdf μ x ≤ (u : ℝ)} = univ := by
        ext x
        simp [hu1, cdf_le_one]
      rw [he, probReal_univ, hu1]
    · obtain ⟨y, hy⟩ := exists_cdf_eq_of_continuous μ hc
        (lt_of_le_of_ne u.property.1 (Ne.symm hu0))
        (lt_of_le_of_ne u.property.2 hu1)
      have hsub : Iic y ⊆ {x | cdf μ x ≤ (u : ℝ)} := by
        intro x hx
        exact (monotone_cdf μ hx).trans hy.le
      have hm := measureReal_mono (μ := μ) hsub
      rwa [← cdf_eq_real, hy] at hm

/-- The CDF transform is measure preserving when its CDF is continuous. -/
theorem measurePreserving_cdfUnit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) : MeasurePreserving (cdfUnit μ) μ volume :=
  ⟨measurable_cdfUnit μ, map_cdfUnit μ hc⟩

end ProbabilityTheory
