/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Independence.Basic

/-!
# Minimum of independent exponentials (Appendix B.2)

The minimum of independent exponentials has the `Exp(∑ rates)` **survival function**:
`μ {ω | t < min_i τ_i ω} = exp (-(∑ rates) * t)` for `t ≥ 0`, derived from joint
independence (`iIndepFun.meas_iInter`) and the individual exponential laws
(`expMeasure` CDF formula). The law identity itself — that the minimum *is*
`Exp(∑ rates)` as a measure — is not stated here.

## Main results

* `minimum_survival`: for jointly independent `τ i` with exponential laws of rates `rates i > 0`
  and `t ≥ 0`, `μ {ω | t < min_i τ_i ω} = exp (-(∑ rates) * t)`. The law of the minimum as a
  measure is not stated.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], B.2

## Tags

minimum of exponentials, survival function, competing risks, first default time,
independent exponentials, MSC 60E05, MSC 91G40
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} {n : ℕ} {rates : Fin n → ℝ} {τ : Fin n → Ω → ℝ}

/-- Survival function of `expMeasure r` for `t ≥ 0`. -/
lemma expMeasure_Ioi (r : ℝ) (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    expMeasure r (Set.Ioi t) = ENNReal.ofReal (Real.exp (-(r * t))) := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have h_compl : expMeasure r (Set.Ioi t) = 1 - expMeasure r (Set.Iic t) := by
    have h_eq : (Set.Ioi t : Set ℝ) = (Set.Iic t)ᶜ := Set.compl_Iic.symm
    rw [h_eq, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ]
  have h_iic : expMeasure r (Set.Iic t) = ENNReal.ofReal (cdf (expMeasure r) t) :=
    (ProbabilityTheory.ofReal_cdf (expMeasure r) t).symm
  rw [h_compl, h_iic, cdf_expMeasure_eq hr t, ite_eq_left ht]
  have hexp_le : Real.exp (-(r * t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := mul_nonneg hr.le ht
    linarith
  have h_diff_nonneg : (0 : ℝ) ≤ 1 - Real.exp (-(r * t)) := by linarith
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h_diff_nonneg]
  congr 1
  ring

/-- The set `{ω | t < min_i τ_i ω}` rewrites to `⋂_i {ω | t < τ_i ω}`. -/
lemma min_gt_iInter (hn : 0 < n) (t : ℝ) :
    {ω : Ω | t < (Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      (fun i : Fin n ↦ τ i ω))}
      = ⋂ i : Fin n, (τ i) ⁻¹' Set.Ioi t := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi]
  exact ⟨fun h i => h.trans_le (Finset.inf'_le _ (Finset.mem_univ i)),
    fun h => (Finset.lt_inf'_iff _).2 fun i _ => h i⟩

variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Appendix B.2: minimum of independent exponentials.

For a finite family of jointly independent `Exp(rates i)` random variables `τ : Fin n → Ω → ℝ`,
the survival function of the pointwise minimum is `exp(-(∑ rates) · t)` for `t ≥ 0` —
i.e. the minimum has law `Exp(∑ rates)` (at the survival-function / CDF level). -/
theorem minimum_survival
    (hrates_pos : ∀ i, 0 < rates i)
    (hexp_law : ∀ i, Measure.map (τ i) μ = expMeasure (rates i))
    (hindep : iIndepFun τ μ)
    (hmeas : ∀ i, Measurable (τ i))
    (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      (fun i : Fin n ↦ τ i ω)} =
        ENNReal.ofReal (Real.exp (-((∑ i, rates i) * t))) := by
  rw [min_gt_iInter hn t]
  rw [hindep.meas_iInter (fun _ ↦ ⟨Set.Ioi t, measurableSet_Ioi, rfl⟩)]
  have step_each : ∀ i, μ ((τ i) ⁻¹' Set.Ioi t)
      = ENNReal.ofReal (Real.exp (-(rates i * t))) := fun i ↦ by
    rw [show μ ((τ i) ⁻¹' Set.Ioi t) = (Measure.map (τ i) μ) (Set.Ioi t) from
      (Measure.map_apply (hmeas i) measurableSet_Ioi).symm,
      hexp_law i, expMeasure_Ioi (rates i) (hrates_pos i) ht]
  simp_rw [step_each]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (Real.exp_pos _).le)]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib]
  simp [Finset.sum_mul]

end MathFin
