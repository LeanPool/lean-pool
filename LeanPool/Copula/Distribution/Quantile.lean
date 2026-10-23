/-
Copyright (c) 2025 Gaëtan Serré, 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne, Marcus Rockel
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.CDF

/-! # Quantiles of laws on the unit interval

The compact unit interval allows a total quantile, including at zero and one.
The proof of the quantile adjunction follows the construction in mathlib's
`Probability.Kernel.Representation`, specialized to a single probability law.
-/

public section

open MeasureTheory Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory

/-- The generalized inverse of the distribution function of a law on `[0,1]`. -/
@[expose]
noncomputable def unitQuantile (μ : Measure I) (t : I) : I :=
  sSup {x | μ.real (Iic x) < (t : ℝ)}

theorem monotone_unitQuantile (μ : Measure I) : Monotone (unitQuantile μ) := by
  intro t u htu
  exact sSup_le_sSup (fun _ hx => lt_of_lt_of_le hx (show (t : ℝ) ≤ (u : ℝ) from htu))

theorem measurable_unitQuantile (μ : Measure I) : Measurable (unitQuantile μ) :=
  (monotone_unitQuantile μ).measurable

/-- The quantile adjunction holds at atoms and at both endpoints. -/
theorem unitQuantile_le_iff (μ : Measure I) [IsProbabilityMeasure μ] (t x : I) :
    unitQuantile μ t ≤ x ↔ (t : ℝ) ≤ μ.real (Iic x) := by
  constructor
  · intro ht
    by_cases hx : x = 1
    · have he : Iic x = univ := by
        ext y
        simp [hx, unitInterval.le_one']
      rw [he, probReal_univ]
      exact t.property.2
    let : NeBot (𝓝[>] x) := nhdsGT_neBot_of_exists_gt
      ⟨1, lt_of_le_of_ne unitInterval.le_one' hx⟩
    have hc : ContinuousWithinAt (fun y : I => μ.real (Iic y)) (Ioi x) x := by
      have h := continuousWithinAt_Ioi_iff_Ici.mpr
        ((cdf (μ.map ((↑) : I → ℝ))).right_continuous (x : ℝ))
      have he (y : I) : μ.real (Iic y) = cdf (μ.map ((↑) : I → ℝ)) (y : ℝ) := by
        rw [ProbabilityTheory.unitInterval.cdf_eq_real]
        congr 1
        ext z
        simp
      simp_rw [he]
      exact h.comp (continuous_subtype_val.continuousWithinAt) (fun y hy => hy)
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) continuousWithinAt_const hc ?_
    apply eventually_nhdsWithin_of_forall
    intro y hy
    by_contra! h
    have hyt : y ≤ unitQuantile μ t := le_sSup h
    exact (not_le.mpr hy) (hyt.trans ht)
  · intro ht
    apply sSup_le
    intro y hy
    by_contra! hxy
    have hm : μ.real (Iic x) ≤ μ.real (Iic y) := measureReal_mono (Iic_subset_Iic.mpr hxy.le)
    exact (not_lt.mpr (ht.trans hm)) hy

/-- Inverse-transform sampling is valid for arbitrary laws, including atomic laws. -/
theorem map_unitQuantile (μ : Measure I) [IsProbabilityMeasure μ] :
    volume.map (unitQuantile μ) = μ := by
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (measurable_unitQuantile μ) measurableSet_Iic]
  let u : I := ⟨μ.real (Iic x), measureReal_nonneg, measureReal_le_one⟩
  have he : unitQuantile μ ⁻¹' Iic x = Iic u := by
    ext t
    exact unitQuantile_le_iff μ t x
  rw [he, unitInterval.volume_Iic]
  exact ofReal_measureReal (measure_ne_top μ _)

end ProbabilityTheory
