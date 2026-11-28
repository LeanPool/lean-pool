/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# The first interarrival time of a Poisson process is exponential

Saporito, Proposition 3.3.6 asserts that the interarrival times of a Poisson
process are iid `Exp(rate)`. The full iid statement for the whole sequence
needs the strong Markov property of the process (upstream-gated). What *is*
derivable from the bare counting axioms — zero start, Poisson increments,
independent increments, monotone paths — is the proposition's analytic core,
and this file derives exactly that:

* **survival law**: `P(N_t = 0) = e^{−rate·t}` — read off the increment law;
* **memoryless factorisation**: `P(N_t = 0) = P(N_s = 0) · P(N_t − N_s = 0)`
  — survival of the first arrival factorises over disjoint windows, the
  signature property of the exponential law (derived from independent
  increments, not assumed);
* **the law itself**: the first arrival time `τ` (characterised by
  `τ > t ↔ N_t = 0`) satisfies `τ ∼ Exp(rate)` — by computing its CDF from
  the survival law and identifying it with Mathlib's `cdf_expMeasure_eq`.

## Main results

* `PoissonInterarrival.survival_eq` — `μ {N t = 0} = e^{−rate t}`.
* `PoissonInterarrival.survival_factorizes` — `μ {N t = 0} = μ {N s = 0} * μ {N t - N s = 0}`
  for `s ≤ t`, the factorisation behind the memoryless property.
* `PoissonInterarrival.map_firstArrival_eq_expMeasure` —
  `τ ∼ Exp(rate)`, fully derived.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Proposition 3.3.6

## Tags

Poisson process, first arrival time, exponential distribution, memoryless property, waiting time,
survival function, MSC 60G55, MSC 60E05
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace PoissonInterarrival

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Survival law of the first arrival.** From the increment law alone:
`P(N_t = 0) = e^{−rate·t}` for `t ≥ 0`. -/
theorem survival_eq {rate : ℝ≥0} {N : ℝ → Ω → ℕ}
    (hmeas : ∀ t, Measurable (N t)) (hzero : ∀ ω, N 0 ω = 0)
    (hincr : ∀ ⦃s t : ℝ⦄, 0 ≤ s → (hst : s ≤ t) →
      Measure.map (fun ω ↦ N t ω - N s ω) μ
        = poissonMeasure (rate * ⟨t - s, sub_nonneg.mpr hst⟩))
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | N t ω = 0} = ENNReal.ofReal (rexp (-((rate : ℝ) * t))) := by
  have h := hincr le_rfl ht
  rw [show (fun ω ↦ N t ω - N 0 ω) = N t from
    funext fun ω ↦ by rw [hzero ω, Nat.sub_zero]] at h
  have hset : μ {ω | N t ω = 0} = μ.map (N t) {0} := by
    rw [Measure.map_apply (hmeas t) (measurableSet_singleton 0)]
    rfl
  rw [hset, h, poissonMeasure_singleton]
  norm_num
  rfl

/-- **Memoryless factorisation (the exponential signature).** Survival of
the first arrival factorises over disjoint windows:
`P(N_t = 0) = P(N_s = 0) · P(N_t − N_s = 0)` — derived from independent
increments and monotone paths, not assumed. -/
theorem survival_factorizes {N : ℝ → Ω → ℕ}
    (hzero : ∀ ω, N 0 ω = 0)
    (hmono : ∀ ⦃s t : ℝ⦄, s ≤ t → ∀ ω, N s ω ≤ N t ω)
    (hindep : ∀ ⦃s t u v : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ u → u ≤ v →
      IndepFun (fun ω ↦ N t ω - N s ω) (fun ω ↦ N v ω - N u ω) μ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    μ {ω | N t ω = 0}
      = μ {ω | N s ω = 0} * μ {ω | N t ω - N s ω = 0} := by
  have hI : IndepFun (N s) (fun ω ↦ N t ω - N s ω) μ := by
    have h := hindep le_rfl hs le_rfl hst
    rwa [show (fun ω ↦ N s ω - N 0 ω) = N s from
      funext fun ω ↦ by rw [hzero ω, Nat.sub_zero]] at h
  have hsplit : {ω | N t ω = 0}
      = (N s) ⁻¹' {0} ∩ (fun ω ↦ N t ω - N s ω) ⁻¹' {0} := by
    ext ω
    have hm := hmono hst ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    omega
  rw [hsplit,
    hI.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton 0)
      (measurableSet_singleton 0)]
  rfl

/-- **Proposition 3.3.6, first interarrival (derived).** If `τ` is the first
arrival time of the counting process (`τ > t ↔ N_t = 0` for `t ≥ 0`,
`τ ≥ 0`), then `τ ∼ Exp(rate)`. The CDF is computed from the survival law
and matched against Mathlib's closed-form exponential CDF. -/
theorem map_firstArrival_eq_expMeasure [IsProbabilityMeasure μ]
    {rate : ℝ≥0} (hrate : 0 < rate) {N : ℝ → Ω → ℕ}
    (hmeas : ∀ t, Measurable (N t)) (hzero : ∀ ω, N 0 ω = 0)
    (hincr : ∀ ⦃s t : ℝ⦄, 0 ≤ s → (hst : s ≤ t) →
      Measure.map (fun ω ↦ N t ω - N s ω) μ
        = poissonMeasure (rate * ⟨t - s, sub_nonneg.mpr hst⟩))
    {τ : Ω → ℝ} (hτ_meas : Measurable τ) (hτ_nonneg : ∀ ω, 0 ≤ τ ω)
    (hτ_first : ∀ ⦃t : ℝ⦄, 0 ≤ t → {ω | t < τ ω} = {ω | N t ω = 0}) :
    μ.map τ = expMeasure rate := by
  have hr : (0 : ℝ) < rate := NNReal.coe_pos.mpr hrate
  have : IsProbabilityMeasure (expMeasure (rate : ℝ)) :=
    isProbabilityMeasure_expMeasure hr
  -- the exponential CDF in measure form
  have hexp_Iic : ∀ x : ℝ, expMeasure (rate : ℝ) (Set.Iic x)
      = ENNReal.ofReal (if 0 ≤ x then 1 - rexp (-((rate : ℝ) * x)) else 0) := by
    intro x
    rw [← ENNReal.ofReal_toReal (measure_ne_top (expMeasure (rate : ℝ)) _),
      show ((expMeasure (rate : ℝ) (Set.Iic x)).toReal)
        = cdf (expMeasure (rate : ℝ)) x from by rw [cdf_eq_real, measureReal_def],
      cdf_expMeasure_eq hr x]
  refine Measure.ext_of_Iic _ _ fun x ↦ ?_
  rw [Measure.map_apply hτ_meas measurableSet_Iic, hexp_Iic x]
  rcases lt_or_ge x 0 with hx | hx
  · -- x < 0 : τ ≥ 0 makes the event empty
    rw [ite_eq_right (not_le.mpr hx), ENNReal.ofReal_zero,
      show τ ⁻¹' Set.Iic x = ∅ from Set.eq_empty_of_forall_notMem fun ω h ↦
        absurd (le_trans (hτ_nonneg ω) (Set.mem_Iic.mp h)) (not_le.mpr hx)]
    exact measure_empty
  · -- x ≥ 0 : complement of the survival event
    have hcompl : τ ⁻¹' Set.Iic x = {ω | x < τ ω}ᶜ := by
      ext ω
      simp [not_lt]
    have hsurv_set : MeasurableSet {ω | x < τ ω} :=
      measurableSet_lt measurable_const hτ_meas
    rw [ite_eq_left hx, hcompl, measure_compl hsurv_set (measure_ne_top μ _),
      measure_univ, hτ_first hx,
      survival_eq hmeas hzero hincr hx,
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
      ← ENNReal.ofReal_sub 1 (Real.exp_nonneg _)]

end PoissonInterarrival

end MathFin
