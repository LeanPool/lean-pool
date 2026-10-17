/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# SubgaussianTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Gaussian tails give square integrability

The paper's J2 tail bound is a literal strict upper-tail estimate.  This module
turns that estimate, with no added moment hypothesis, into the `L²` input
needed to construct the stationary J4 observable.
-/

namespace Algsuperdiff.Probability

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A nonnegative measurable real random variable with the paper's strict
Gaussian upper tail (above level one) belongs to `L²`. -/
theorem memLp_two_of_gaussian_tail
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXmeas : Measurable X)
    (hXnonneg : ∀ ω, 0 ≤ X ω)
    (htail : ∀ t : ℝ, 1 ≤ t →
      μ {ω | t < X ω} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2))) ) :
    MemLp X 2 μ := by
  have hXsq_meas : Measurable (fun ω ↦ X ω ^ 2) := by
    simpa only [pow_two] using! hXmeas.mul hXmeas
  have htail_sq : ∀ t : ℝ, 1 ≤ t →
      μ {ω | t < X ω ^ 2} ≤ ENNReal.ofReal (Real.exp (-t)) := by
    intro t ht
    calc
      μ {ω | t < X ω ^ 2} ≤ μ {ω | Real.sqrt t < X ω} := by
        apply measure_mono
        intro ω hω
        change t < X ω ^ 2 at hω
        change Real.sqrt t < X ω
        rw [Real.sqrt_lt (by linarith) (hXnonneg ω)]
        exact hω
      _ ≤ ENNReal.ofReal (Real.exp (-(Real.sqrt t) ^ 2)) := by
        apply htail
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt ht
      _ = ENNReal.ofReal (Real.exp (-t)) := by
        rw [Real.sq_sqrt (by linarith)]
  have hsmall :
      (∫⁻ t in Ioc (0 : ℝ) 1, μ {ω | t < X ω ^ 2}) < ∞ := by
    calc
      (∫⁻ t in Ioc (0 : ℝ) 1, μ {ω | t < X ω ^ 2}) ≤
          ∫⁻ _t in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) := by
        apply setLIntegral_mono measurable_const
        intro t _
        exact (measure_mono (by intro ω _; trivial)).trans_eq
          (IsProbabilityMeasure.measure_univ (μ := μ))
      _ < ∞ := by
        simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ,
          univ_inter, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top
  have hlarge :
      (∫⁻ t in Ioi (1 : ℝ), μ {ω | t < X ω ^ 2}) < ∞ := by
    calc
      (∫⁻ t in Ioi (1 : ℝ), μ {ω | t < X ω ^ 2}) ≤
          ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (-t)) := by
        apply setLIntegral_mono
        · exact (Real.continuous_exp.comp continuous_neg).measurable.ennreal_ofReal
        · intro t ht
          exact htail_sq t ht.le
      _ < ∞ := by
        simpa [Real.norm_eq_abs] using
          (integrableOn_exp_neg_Ioi (1 : ℝ)).lintegral_lt_top
  have htail_integral :
      (∫⁻ t in Ioi (0 : ℝ), μ {ω | t < X ω ^ 2}) < ∞ := by
    have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 :=
      (Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)).symm
    rw [hsplit, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
    exact ENNReal.add_lt_top.mpr ⟨hsmall, hlarge⟩
  have hlayer :
      (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂μ) =
        ∫⁻ t in Ioi (0 : ℝ), μ {ω | t < X ω ^ 2} := by
    exact lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall fun ω ↦ sq_nonneg (X ω))
      hXsq_meas.aemeasurable
  have hsq_integrable : Integrable (fun ω ↦ X ω ^ 2) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      hXsq_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ sq_nonneg (X ω))).mp
    rw [hlayer]
    exact htail_integral.ne
  exact (memLp_two_iff_integrable_sq hXmeas.aestronglyMeasurable).mpr hsq_integrable

end

end Algsuperdiff.Probability
