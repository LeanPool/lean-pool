/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Laws.StudentT
public import LeanPool.MathFin.Risk.ExpectedShortfall

/-!
# Value-at-risk and expected shortfall of a Student-t loss

Let `T` have the standard Student-t law `t_ν` (`Probability/Laws/StudentT.lean`) and consider the
location-scale loss `L = μ + σ T` with `σ ≥ 0`. Through the library's own `valueAtRisk` and
`expectedShortfall` (`Risk/ValueAtRisk.lean`), this file proves the closed forms of
McNeil, Frey and Embrechts, *Quantitative Risk Management* (2015), Example 2.15:

  `VaR_α(L) = μ + σ t_ν⁻¹(α)`,
  `ES_α(L) = μ + σ · g_ν(t_ν⁻¹(α))/(1 − α) · (ν + t_ν⁻¹(α)²)/(ν − 1)`   (`ν > 1`),

where `t_ν⁻¹(α) = quantile (studentTMeasure ν) α` is the quantile of the law
(`cdf_studentTMeasure_quantile`: it solves `F_ν(q) = α`) and `g_ν = studentTPDFReal ν` is its
density. The ES proof runs through the Acerbi–Tasche formula
(`expectedShortfall_eq_acerbiTasche`): the law has no atoms, so the tail probability above the
quantile is exactly `1 − α` and ES is the tail first moment `∫_q^∞ t g_ν(t) dt / (1 − α)`, which
`setIntegral_Ioi_mul_studentTPDFReal` evaluates.

`VaR ≤ ES` is not reproved: it is the general `valueAtRisk_le_expectedShortfall`, instantiated
at the Student-t loss (`valueAtRisk_le_expectedShortfall_of_hasLaw_studentTMeasure`).

## Main results

* `valueAtRisk_of_hasLaw_studentTMeasure`: `VaR_α(μ + σ T) = μ + σ t_ν⁻¹(α)`.
* `expectedShortfall_of_hasLaw_studentTMeasure`: the McNeil–Frey–Embrechts closed form of
  `ES_α(μ + σ T)` for `ν > 1`.
* `valueAtRisk_le_expectedShortfall_of_hasLaw_studentTMeasure`:
  `VaR_α(μ + σ T) ≤ ES_α(μ + σ T)`.
* `quantile_studentTMeasure_le_expectedShortfall_closedForm`: the same inequality between the
  two closed forms, `q ≤ g_ν(q)/(1 − α) · (ν + q²)/(ν − 1)`.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Example 2.15

## Tags

Student-t VaR, heavy-tailed loss, t distribution, expected shortfall closed form,
McNeil-Frey-Embrechts, location-scale loss, MSC 91G70, MSC 60E05, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {T : Ω → ℝ} {ν μ σ α : ℝ}

/-- The Student-t law has a continuous cdf: it has a density, hence no atoms. -/
lemma continuous_cdf_studentTMeasure (hν : 0 < ν) : Continuous (cdf (studentTMeasure ν)) :=
  have := isProbabilityMeasure_studentTMeasure hν
  continuous_cdf

/-- The Student-t quantile `t_ν⁻¹(α)` solves `F_ν(q) = α`. -/
lemma cdf_studentTMeasure_quantile (hν : 0 < ν) (hα : α ∈ Ioo 0 1) :
    cdf (studentTMeasure ν) (quantile (studentTMeasure ν) α) = α :=
  cdf_quantile (continuous_cdf_studentTMeasure hν) hα

/-- The Student-t law with `ν > 1` has a mean: `id` is integrable. -/
lemma integrable_id_studentTMeasure (hν : 1 < ν) : Integrable id (studentTMeasure ν) := by
  have hν0 : 0 < ν := by linarith
  rw [studentTMeasure, integrable_withDensity_iff (measurable_studentTPDF ν)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine (integrable_mul_studentTPDFReal hν).congr (ae_of_all _ fun x ↦ ?_)
  simp [studentTPDF, ENNReal.toReal_ofReal (studentTPDFReal_pos hν0 x).le]

/-- **Value-at-risk of a Student-t loss**: `VaR_α(μ + σ T) = μ + σ t_ν⁻¹(α)` for `T ~ t_ν` and
`σ ≥ 0`. -/
theorem valueAtRisk_of_hasLaw_studentTMeasure (hT : HasLaw T (studentTMeasure ν) P) (hσ : 0 ≤ σ)
    (hα : α ∈ Ioo 0 1) :
    valueAtRisk (fun ω ↦ μ + σ * T ω) P α = μ + σ * quantile (studentTMeasure ν) α := by
  rw [valueAtRisk_comp (h := fun x ↦ μ + σ * x) hT.aemeasurable
    ((monotone_id.const_mul hσ).const_add μ)
    (by fun_prop : Continuous fun x ↦ μ + σ * x).lowerSemicontinuous hα,
    valueAtRisk_eq_quantile hT]

/-- **Expected shortfall of a standard Student-t loss**: for `T ~ t_ν` with `ν > 1`,
`ES_α(T) = g_ν(q)/(1 − α) · (ν + q²)/(ν − 1)` at `q = t_ν⁻¹(α)`. -/
theorem expectedShortfall_of_hasLaw_studentTMeasure_standard (hν : 1 < ν)
    (hT : HasLaw T (studentTMeasure ν) P) (hα : α ∈ Ioo 0 1) :
    expectedShortfall T P α =
      studentTPDFReal ν (quantile (studentTMeasure ν) α) / (1 - α) *
        ((ν + quantile (studentTMeasure ν) α ^ 2) / (ν - 1)) := by
  have hν0 : 0 < ν := by linarith
  have := isProbabilityMeasure_studentTMeasure hν0
  set q := quantile (studentTMeasure ν) α
  have hVaR : valueAtRisk T P α = q := valueAtRisk_eq_quantile hT
  -- the tail above the quantile carries probability exactly `1 − α`
  have htail : P.real {ω | q < T ω} = 1 - α := by
    rw [hT.measureReal_eq (p := fun x ↦ q < x) measurableSet_Ioi, show {x | q < x} = Ioi q from rfl,
      ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
      cdf_studentTMeasure_quantile hν0 hα]
  -- and the tail first moment is the integral evaluated in `Probability/Laws/StudentT.lean`
  have hmoment : ∫ ω in {ω | q < T ω}, T ω ∂P = ∫ t in Ioi q, t * studentTPDFReal ν t := by
    rw [show {ω | q < T ω} = T ⁻¹' Ioi q from rfl, ← setIntegral_map (f := fun t : ℝ ↦ t)
      measurableSet_Ioi (by fun_prop) hT.aemeasurable, hT.map_eq, studentTMeasure,
      setIntegral_withDensity_eq_setIntegral_toReal_smul (measurable_studentTPDF ν)
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) _ measurableSet_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    simp [studentTPDF, ENNReal.toReal_ofReal (studentTPDFReal_pos hν0 t).le, mul_comm]
  rw [expectedShortfall_eq_acerbiTasche (hT.integrable (integrable_id_studentTMeasure hν)) hα, hVaR,
    htail, hmoment, setIntegral_Ioi_mul_studentTPDFReal hν, sub_self, mul_zero, add_zero]
  ring

/-- **Expected shortfall of a Student-t loss** (McNeil–Frey–Embrechts, Example 2.15): for
`T ~ t_ν` with `ν > 1` and `σ ≥ 0`, at `q = t_ν⁻¹(α)`,
`ES_α(μ + σ T) = μ + σ · g_ν(q)/(1 − α) · (ν + q²)/(ν − 1)`. -/
theorem expectedShortfall_of_hasLaw_studentTMeasure (hν : 1 < ν)
    (hT : HasLaw T (studentTMeasure ν) P) (hσ : 0 ≤ σ) (hα : α ∈ Ioo 0 1) :
    expectedShortfall (fun ω ↦ μ + σ * T ω) P α =
      μ + σ * (studentTPDFReal ν (quantile (studentTMeasure ν) α) / (1 - α) *
        ((ν + quantile (studentTMeasure ν) α ^ 2) / (ν - 1))) := by
  have hint := hT.integrable (integrable_id_studentTMeasure hν)
  rw [show (fun ω ↦ μ + σ * T ω) = fun ω ↦ σ * T ω + μ from funext fun _ ↦ add_comm _ _,
    expectedShortfall_add_const (hint.const_mul σ) hα, expectedShortfall_const_mul hint hα hσ,
    expectedShortfall_of_hasLaw_studentTMeasure_standard hν hT hα, add_comm]

/-- **VaR ≤ ES for a Student-t loss**: the general `valueAtRisk_le_expectedShortfall`, at the
law. -/
theorem valueAtRisk_le_expectedShortfall_of_hasLaw_studentTMeasure (hν : 1 < ν)
    (hT : HasLaw T (studentTMeasure ν) P) (hα : α ∈ Ioo 0 1) :
    valueAtRisk (fun ω ↦ μ + σ * T ω) P α ≤ expectedShortfall (fun ω ↦ μ + σ * T ω) P α :=
  valueAtRisk_le_expectedShortfall
    ((integrable_const μ).add ((hT.integrable (integrable_id_studentTMeasure hν)).const_mul σ)) hα

/-- **The closed forms inherit `VaR ≤ ES`**: at `q = t_ν⁻¹(α)` with `ν > 1`,
`q ≤ g_ν(q)/(1 − α) · (ν + q²)/(ν − 1)`. An inequality about the Student-t density and quantile,
read off the general `valueAtRisk_le_expectedShortfall` for `T = id` under the law itself. -/
theorem quantile_studentTMeasure_le_expectedShortfall_closedForm (hν : 1 < ν) (hα : α ∈ Ioo 0 1) :
    quantile (studentTMeasure ν) α ≤
      studentTPDFReal ν (quantile (studentTMeasure ν) α) / (1 - α) *
        ((ν + quantile (studentTMeasure ν) α ^ 2) / (ν - 1)) := by
  have := isProbabilityMeasure_studentTMeasure (by linarith : 0 < ν)
  have hT : HasLaw id (studentTMeasure ν) (studentTMeasure ν) := .id
  rw [← expectedShortfall_of_hasLaw_studentTMeasure_standard hν hT hα, ← valueAtRisk_eq_quantile hT]
  exact valueAtRisk_le_expectedShortfall (hT.integrable (integrable_id_studentTMeasure hν)) hα

end MathFin
