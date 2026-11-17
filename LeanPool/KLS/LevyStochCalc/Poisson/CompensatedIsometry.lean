/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedSimple
public import LeanPool.KLS.LevyStochCalc.Poisson.Filtered
public import Mathlib.Probability.Independence.Integration
import TauCeti.Probability.Distributions.Poisson.Basic

/-!
# Second moments and L²-isometry of the simple compensated-Poisson integral

The mean-zero / second-moment (variance) identities for the compensated Poisson
measure `Ñ(B) = N(B) − ν̂(B)`, and the diagonal / off-diagonal computation for
`simpleIntegral` (orthogonality of disjoint compensated-Poisson increments) that
they feed, culminating in the simple-integrand L²-isometry `simpleIntegral_isometry`
and L²-membership `simpleIntegral_memLp_compensated`. Builds on the integrand
definitions in `Poisson/CompensatedSimple.lean`.

This module uses Tau Ceti's Poisson mean and second moment, proves the associated
factorial-series summability, and transports the moment identities along `poisson_law`
to the compensated increments `Ñ(B)`.

## Downstream modules

* `LevyStochCalc.Poisson.CompensatedIsometryOrthogonality` — the diagonal identity
  `∫⁻ ‖ξ_i · Ñ(B_i)‖² ∂P = ν̂(B_i) · ∫⁻ ‖ξ_i‖² ∂P` and the off-diagonal vanishing
  `∫ (ξ_i · Ñ(B_i)) · (ξ_j · Ñ(B_j)) ∂P = 0` for `i < j`.
* `LevyStochCalc.Poisson.CompensatedIsometryL2` — the Bochner expansion of
  `(∑_i ξ_i · Ñ(B_i))²`, the isometry `simpleIntegral_isometry` with its sum form, and
  the membership `simpleIntegral_memLp_compensated`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

private lemma poisson_term_succ_eq (r : ℝ) (n : ℕ) :
    r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ)
    = r * (r ^ n / (n.factorial : ℝ)) := by
  have hn : (n.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- The mean of a Poisson law on naturals, by transport from the real-valued law. -/
private lemma poissonMeasure_integral_id (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r) = (r : ℝ) := by
  rw [← integral_map (f := fun x : ℝ => x)
    Measurable.of_discrete.aemeasurable measurable_id.aestronglyMeasurable]
  exact TauCeti.Probability.integral_id_map_cast_poissonMeasure r

/-- **Summability of `r^n / n! · n` for r ≥ 0.** Used for integrability of `(n : ℝ)`
w.r.t. `poissonMeasure r`. -/
lemma summable_pow_div_factorial_mul_nat (r : ℝ) :
    Summable fun n : ℕ => r ^ n / (n.factorial : ℝ) * (n : ℝ) := by
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ))
            = fun n => r * (r ^ n / (n.factorial : ℝ)) from
      funext (poisson_term_succ_eq r)]
    exact (Real.summable_pow_div_factorial r).mul_left r
  exact (summable_nat_add_iff 1).mp h_summable_succ

-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Compensated-Poisson mean is zero.** For a measurable set `B` with finite
intensity, `∫ ω, Ñ(B, ω) ∂P = 0`. Follows from `E[N(B)] = ν̂(B)` (Poisson mean,
proved via `poissonMeasure_integral_id`). -/
lemma compensated_mean_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    ∫ ω, N.compensated B ω ∂P = 0 := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_c_eq_r : c = (r : ℝ) := by
    rw [hc_def, hr_def, ENNReal.coe_toNNReal_eq_toReal]
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  -- compensated B ω = (·.toReal - c) ∘ (N.N · B)
  have h_compensated_eq : (fun ω => N.compensated B ω) =
      (fun x : ℝ≥0∞ => x.toReal - c) ∘ (fun ω => N.N ω B) := by
    funext ω
    rfl
  rw [h_compensated_eq]
  -- Pushforward via integral_map
  rw [show (∫ ω, ((fun x : ℝ≥0∞ => x.toReal - c) ∘ (fun ω => N.N ω B)) ω ∂P)
      = ∫ x, (x.toReal - c) ∂(P.map (fun ω => N.N ω B)) from
    (MeasureTheory.integral_map h_NB_meas.aemeasurable
      (ENNReal.measurable_toReal.sub_const _).aestronglyMeasurable).symm]
  -- Apply poisson_law
  rw [N.poisson_law hB h_finite]
  -- Unfold poissonMeasureENN
  change ∫ x, (x.toReal - c) ∂((ProbabilityTheory.poissonMeasure r).map
    (fun n : ℕ => (n : ℝ≥0∞))) = 0
  rw [MeasureTheory.integral_map measurable_from_nat.aemeasurable
    (ENNReal.measurable_toReal.sub_const _).aestronglyMeasurable]
  -- Simplify the cast (n : ℝ≥0∞).toReal = (n : ℝ)
  have h_phi_cast : ∀ n : ℕ, ((n : ℝ≥0∞)).toReal - c = (n : ℝ) - c := by
    intro n
    rw [show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp]
  simp_rw [h_phi_cast]
  -- Now goal: ∫ n, (n : ℝ) - c ∂(poissonMeasure r) = 0
  -- Establish integrability of (n : ℝ) w.r.t. poissonMeasure r
  have h_int_id : MeasureTheory.Integrable
      (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure r) := by
    rw [ProbabilityTheory.integrable_poissonMeasure_iff]
    have h_norm : ∀ n : ℕ, ‖((n : ℝ))‖ = (n : ℝ) := fun n => by
      rw [Real.norm_eq_abs]; exact abs_of_nonneg (Nat.cast_nonneg n)
    simp_rw [h_norm]
    have h_eq : ∀ n : ℕ,
        Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)
        = Real.exp (-(↑r : ℝ))
          * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)) := by
      intro n; ring
    simp_rw [h_eq]
    exact (summable_pow_div_factorial_mul_nat (↑r)).mul_left _
  have h_int_const : MeasureTheory.Integrable
      (fun _ : ℕ => c) (ProbabilityTheory.poissonMeasure r) :=
    MeasureTheory.integrable_const _
  rw [MeasureTheory.integral_sub h_int_id h_int_const]
  rw [poissonMeasure_integral_id, MeasureTheory.integral_const]
  -- Goal: (↑r : ℝ) - (Measure.real (poissonMeasure r) Set.univ) • c = 0
  rw [show ((ProbabilityTheory.poissonMeasure r).real Set.univ : ℝ) = 1 from by
    rw [MeasureTheory.measureReal_def]
    simp [MeasureTheory.measure_univ]]
  rw [← h_c_eq_r]
  simp

/-- **The mean count is the reference intensity.** For a measurable set of finite intensity the
lower integral of the count is that intensity. -/
lemma lintegral_count_eq_referenceIntensity
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    ∫⁻ ω, N.N ω B ∂P = LevyStochCalc.Poisson.referenceIntensity ν B := by
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have h_int_id : MeasureTheory.Integrable
      (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure r) := by
    rw [ProbabilityTheory.integrable_poissonMeasure_iff]
    have h_norm : ∀ n : ℕ, ‖((n : ℝ))‖ = (n : ℝ) := fun n => by
      rw [Real.norm_eq_abs]; exact abs_of_nonneg (Nat.cast_nonneg n)
    simp_rw [h_norm]
    have h_eq : ∀ n : ℕ,
        Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)
        = Real.exp (-(↑r : ℝ))
          * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)) := by
      intro n; ring
    simp_rw [h_eq]
    exact (summable_pow_div_factorial_mul_nat (↑r)).mul_left _
  have hmap : ∫⁻ x, x ∂(P.map (fun ω => N.N ω B)) = ∫⁻ ω, N.N ω B ∂P :=
    lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id' h_NB_meas
  rw [← hmap, N.poisson_law hB h_finite]
  change ∫⁻ x, x ∂((ProbabilityTheory.poissonMeasure r).map (fun n : ℕ => (n : ℝ≥0∞))) = _
  rw [lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id' measurable_from_nat]
  have hcast : (fun n : ℕ => ((n : ℝ≥0∞))) = fun n : ℕ => ENNReal.ofReal ((n : ℝ)) := by
    funext n
    rw [ENNReal.ofReal_natCast]
  rw [hcast, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_id
    (Filter.Eventually.of_forall fun n => Nat.cast_nonneg n), poissonMeasure_integral_id,
    ENNReal.ofReal_coe_nnreal, hr_def, ENNReal.coe_toNNReal h_finite]

/-- **Per-term reduction for `n²`:** `r^(n+1) / (n+1)! · (n+1)² = r · (n+1) · (r^n / n!)`. -/
private lemma poisson_term_succ_sq_eq (r : ℝ) (n : ℕ) :
    r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2
    = r * ((n + 1 : ℕ) : ℝ) * (r ^ n / (n.factorial : ℝ)) := by
  have hn : (n.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- **Summability of `r^n / n! · n²`** for any real `r`. -/
private lemma summable_pow_div_factorial_mul_nat_sq (r : ℝ) :
    Summable fun n : ℕ => r ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 2 := by
  have h_split : ∀ n : ℕ,
      r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2
      = r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
        + r * (r ^ n / (n.factorial : ℝ)) := by
    intro n
    rw [poisson_term_succ_sq_eq r]
    push_cast
    ring
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2)
            = fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
              + r * (r ^ n / (n.factorial : ℝ)) from
      funext h_split]
    refine Summable.add ?_ ?_
    · have h_eq : (fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ)))
              = fun n : ℕ => r * (r ^ n / (n.factorial : ℝ) * (n : ℝ)) := by
        funext n; ring
      rw [h_eq]
      exact (summable_pow_div_factorial_mul_nat r).mul_left r
    · exact (Real.summable_pow_div_factorial r).mul_left r
  exact (summable_nat_add_iff 1).mp h_summable_succ

/-- The second raw moment of a Poisson law on naturals. -/
private lemma poissonMeasure_integral_id_sq (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
      = (r : ℝ) ^ 2 + (r : ℝ) := by
  rw [← integral_map (f := fun x : ℝ => x ^ 2)
    Measurable.of_discrete.aemeasurable (measurable_id.pow_const 2).aestronglyMeasurable]
  exact TauCeti.Probability.integral_sq_map_cast_poissonMeasure r

/-- Integrability of `(n : ℝ)` w.r.t. `poissonMeasure r`. -/
private lemma integrable_id_poissonMeasure (r : ℝ≥0) :
    MeasureTheory.Integrable (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have h_norm : ∀ n : ℕ, ‖((n : ℝ))‖ = (n : ℝ) := fun n => by
    rw [Real.norm_eq_abs]; exact abs_of_nonneg (Nat.cast_nonneg n)
  simp_rw [h_norm]
  have h_eq : ∀ n : ℕ,
      Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)
      = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)) := by
    intro n; ring
  simp_rw [h_eq]
  exact (summable_pow_div_factorial_mul_nat (↑r)).mul_left _

/-- Integrability of `(n : ℝ)²` w.r.t. `poissonMeasure r`. -/
private lemma integrable_id_sq_poissonMeasure (r : ℝ≥0) :
    MeasureTheory.Integrable
      (fun n : ℕ => (n : ℝ) ^ 2) (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have h_norm : ∀ n : ℕ, ‖((n : ℝ) ^ 2)‖ = (n : ℝ) ^ 2 := fun n => by
    rw [Real.norm_eq_abs]; exact abs_of_nonneg (sq_nonneg _)
  simp_rw [h_norm]
  have h_eq : ∀ n : ℕ,
      Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)^2
      = Real.exp (-(↑r : ℝ))
        * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)^2) := by
    intro n; ring
  simp_rw [h_eq]
  exact (summable_pow_div_factorial_mul_nat_sq (↑r)).mul_left _

-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Variance of `poissonMeasure r`:** `∫ n, ((n:ℝ) − r)² ∂poissonMeasure r = r`.
Mean `r`, second moment `r²+r`, variance `(r²+r) − r² = r`. -/
private lemma poissonMeasure_variance (r : ℝ≥0) :
    ∫ n : ℕ, ((n : ℝ) - (r : ℝ)) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
      = (r : ℝ) := by
  have h_int_n := integrable_id_poissonMeasure r
  have h_int_nsq := integrable_id_sq_poissonMeasure r
  have h_int_const : MeasureTheory.Integrable
      (fun _ : ℕ => (r : ℝ) ^ 2) (ProbabilityTheory.poissonMeasure r) :=
    MeasureTheory.integrable_const _
  have h_int_2rn : MeasureTheory.Integrable
      (fun n : ℕ => 2 * (r : ℝ) * (n : ℝ)) (ProbabilityTheory.poissonMeasure r) :=
    h_int_n.const_mul (2 * (r : ℝ))
  -- Expand (n - r)² = n² - 2rn + r², explicitly stated as ((n² - 2rn) + r²) for additivity.
  have h_expand : ∀ n : ℕ, ((n : ℝ) - (r : ℝ)) ^ 2
      = ((n : ℝ) ^ 2 - 2 * (r : ℝ) * (n : ℝ)) + (r : ℝ) ^ 2 := by
    intro n; ring
  simp_rw [h_expand]
  -- Use integral linearity step-by-step. To avoid Pi.sub_apply matching issues,
  -- compute each integral as a have-hypothesis and combine via calc.
  have h_e_nsq : ∫ n : ℕ, (n : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
      = (↑r : ℝ) ^ 2 + (↑r : ℝ) := poissonMeasure_integral_id_sq r
  have h_e_2rn : ∫ n : ℕ, 2 * (↑r : ℝ) * (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r)
      = 2 * (↑r : ℝ) * (↑r : ℝ) := by
    rw [MeasureTheory.integral_const_mul]
    rw [poissonMeasure_integral_id]
  have h_e_csq :
      ∫ _ : ℕ, (↑r : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r) = (↑r : ℝ) ^ 2 := by
    rw [MeasureTheory.integral_const]
    rw [show (ProbabilityTheory.poissonMeasure r).real Set.univ = 1 from by
      rw [MeasureTheory.measureReal_def]; simp [MeasureTheory.measure_univ]]
    rw [one_smul]
  -- ∫ ((n² - 2rn) + r²) = ∫ (n² - 2rn) + ∫ r²
  rw [show
      ∫ n : ℕ, ((n : ℝ) ^ 2 - 2 * (↑r : ℝ) * (n : ℝ)) + (↑r : ℝ) ^ 2
        ∂(ProbabilityTheory.poissonMeasure r)
      = ∫ n : ℕ, ((n : ℝ) ^ 2 - 2 * (↑r : ℝ) * (n : ℝ))
          ∂(ProbabilityTheory.poissonMeasure r)
        + ∫ _ : ℕ, (↑r : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r) from
    MeasureTheory.integral_add (h_int_nsq.sub h_int_2rn) h_int_const]
  -- ∫ (n² - 2rn) = ∫ n² - ∫ 2rn
  rw [show
      ∫ n : ℕ, ((n : ℝ) ^ 2 - 2 * (↑r : ℝ) * (n : ℝ))
        ∂(ProbabilityTheory.poissonMeasure r)
      = ∫ n : ℕ, (n : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
        - ∫ n : ℕ, 2 * (↑r : ℝ) * (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r) from
    MeasureTheory.integral_sub h_int_nsq h_int_2rn]
  rw [h_e_nsq, h_e_2rn, h_e_csq]
  ring

-- maxHeartbeats: typechecker budget for proof-heavy goal below.
lemma compensated_second_moment
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    ∫ ω, (N.compensated B ω)^2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν B).toReal := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_c_eq_r : c = (r : ℝ) := by
    rw [hc_def, hr_def, ENNReal.coe_toNNReal_eq_toReal]
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have h_meas_phi : Measurable (fun x : ℝ≥0∞ => (x.toReal - c)^2) :=
    (ENNReal.measurable_toReal.sub_const _).pow_const 2
  -- (Ñ(B,ω))² = ((·).toReal - c)² ∘ (N.N · B)
  have h_compensated_sq_eq : (fun ω => (N.compensated B ω)^2) =
      (fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun ω => N.N ω B) := by
    funext ω; rfl
  rw [h_compensated_sq_eq]
  rw [show (∫ ω, ((fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun ω => N.N ω B)) ω ∂P)
      = ∫ x, (x.toReal - c)^2 ∂(P.map (fun ω => N.N ω B)) from
    (MeasureTheory.integral_map h_NB_meas.aemeasurable
      h_meas_phi.aestronglyMeasurable).symm]
  rw [N.poisson_law hB h_finite]
  change ∫ x, (x.toReal - c)^2 ∂((ProbabilityTheory.poissonMeasure r).map
    (fun n : ℕ => (n : ℝ≥0∞))) = c
  rw [MeasureTheory.integral_map measurable_from_nat.aemeasurable
    h_meas_phi.aestronglyMeasurable]
  have h_phi_cast :
      ∀ n : ℕ, (((n : ℝ≥0∞)).toReal - c) ^ 2 = ((n : ℝ) - (r : ℝ)) ^ 2 := by
    intro n
    rw [show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp, h_c_eq_r]
  simp_rw [h_phi_cast]
  rw [poissonMeasure_variance r]
  exact h_c_eq_r.symm

/-- **Integrability of `(N.compensated B)²` w.r.t. P.** Follows from pushforward
through `poisson_law` + integrability of `(n − r)²` w.r.t. `poissonMeasure r`. -/
lemma compensated_sq_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    MeasureTheory.Integrable (fun ω => (N.compensated B ω)^2) P := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_c_eq_r : c = (r : ℝ) := by
    rw [hc_def, hr_def, ENNReal.coe_toNNReal_eq_toReal]
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have h_meas_phi_sq : Measurable (fun x : ℝ≥0∞ => (x.toReal - c)^2) :=
    (ENNReal.measurable_toReal.sub_const _).pow_const 2
  -- (compensated B)² = ((·).toReal - c)² ∘ (N.N · B). Lift through pushforwards.
  rw [show (fun ω => (N.compensated B ω)^2) =
      (fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun ω => N.N ω B) from rfl]
  -- Step 1: convert Integrable (g ∘ f) P → Integrable g (P.map f) via the iff.
  rw [← MeasureTheory.integrable_map_measure (μ := P) (f := fun ω => N.N ω B)
      h_meas_phi_sq.aestronglyMeasurable h_NB_meas.aemeasurable]
  -- Step 2: replace P.map with poissonMeasureENN via poisson_law.
  rw [N.poisson_law hB h_finite]
  -- Step 3: unfold poissonMeasureENN = (poissonMeasure r).map Nat.cast.
  change MeasureTheory.Integrable (fun x : ℝ≥0∞ => (x.toReal - c)^2)
    ((ProbabilityTheory.poissonMeasure r).map (fun n : ℕ => (n : ℝ≥0∞)))
  -- Step 4: convert Integrable g (μ.map f) → Integrable (g ∘ f) μ.
  rw [MeasureTheory.integrable_map_measure
      (μ := ProbabilityTheory.poissonMeasure r) (f := fun n : ℕ => (n : ℝ≥0∞))
      h_meas_phi_sq.aestronglyMeasurable measurable_from_nat.aemeasurable]
  -- Now goal: Integrable ((fun x => (x.toReal - c)^2) ∘ Nat.cast) (poissonMeasure r)
  -- Simplify (↑n : ℝ≥0∞).toReal = (n : ℝ); use c = (r : ℝ).
  have h_simp : ((fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun n : ℕ => (n : ℝ≥0∞)))
              = fun n : ℕ => ((n : ℝ) - (r : ℝ))^2 := by
    funext n
    change (((n : ℝ≥0∞)).toReal - c)^2 = ((n : ℝ) - (r : ℝ))^2
    rw [show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp, h_c_eq_r]
  rw [h_simp]
  -- Expand (n - r)² = (n² - 2rn) + r².
  have h_eq : (fun n : ℕ => ((n : ℝ) - (r : ℝ))^2)
            = fun n : ℕ => (((n : ℝ)^2) - (2 * (r : ℝ) * (n : ℝ))) + (r : ℝ)^2 := by
    funext n; ring
  rw [h_eq]
  have h_int_n := integrable_id_poissonMeasure r
  have h_int_nsq := integrable_id_sq_poissonMeasure r
  have h_int_const : MeasureTheory.Integrable
      (fun _ : ℕ => (r : ℝ)^2) (ProbabilityTheory.poissonMeasure r) :=
    MeasureTheory.integrable_const _
  have h_int_2rn : MeasureTheory.Integrable
      (fun n : ℕ => 2 * (r : ℝ) * (n : ℝ)) (ProbabilityTheory.poissonMeasure r) :=
    h_int_n.const_mul (2 * (r : ℝ))
  exact (h_int_nsq.sub h_int_2rn).add h_int_const

end LevyStochCalc.Poisson.Compensated
