/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Laws.ErlangSum
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# The Poisson marginal law from the arrival-time construction

Saporito's Theorem 3.3.5 states the Poisson marginal law and derives
it from infinitesimal transition probabilities. Here the counting process is
constructed from iid `Exp(r)` interarrival times and its marginal law follows
from the arrival-time identities.

This file derives the marginal from the construction:

* the `k`-th arrival time `T k = ξ₀ + ⋯ + ξ_{k−1}` has the `Erlang(k, r) =
  gammaMeasure k r` law (`ErlangSum.map_sum_iidExp`, our Gamma convolution
  identity);
* the counting event `{N t = k}` is the difference
  `{T k ≤ t} \ {T (k+1) ≤ t}`;
* the analytic heart: the **Gamma-CDF difference identity**

  `∫₀ᵗ γ_k − ∫₀ᵗ γ_{k+1} = e^{−rt} (rt)ᵏ / k!`

  where `γ_k` is the `Gamma(k, r)` density — proved by the fundamental
  theorem of calculus applied to `Φ_k(u) = (ru)ᵏ e^{−ru}/k!`, whose
  derivative telescopes to exactly `γ_k − γ_{k+1}`.

## Main results

* `PoissonCounting.map_count_eq_poissonMeasure` — for iid `Exp(r)`
  interarrivals and the counting process they generate,
  `N t ∼ Poisson(r·t)` by the arrival-time derivation.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 3.3.5 (the marginal law)

## Tags

Poisson process, counting process, Erlang distribution, Gamma distribution, interarrival times,
Poisson marginal law, MSC 60G55, MSC 60E05
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat

namespace PoissonCounting

variable {r t : ℝ}

/-! ### Integrability of the Gamma density on `[0, t]` -/

/-- The Gamma density of shape `a ≥ 1` is continuous on `[0, ∞)`. -/
lemma continuousOn_gammaPDFReal {a : ℝ} (ha : 1 ≤ a) (r : ℝ) :
    ContinuousOn (gammaPDFReal a r) (Set.Ici 0) := by
  have hform : ContinuousOn
      (fun x : ℝ ↦ r ^ a / Real.Gamma a * x ^ (a - 1) * rexp (-(r * x)))
      (Set.Ici 0) := by
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) ?_
    · exact continuousOn_id.rpow_const fun x _ ↦ Or.inr (by linarith)
    · exact ((continuous_const.mul continuous_id).neg.rexp).continuousOn
  exact hform.congr fun x hx ↦ by
    rw [gammaPDFReal, ite_eq_left (Set.mem_Ici.mp hx)]

/-- The Gamma density of shape `a ≥ 1` is interval integrable on `[0, t]`. -/
lemma intervalIntegrable_gammaPDFReal {a : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) :
    IntervalIntegrable (gammaPDFReal a r) volume 0 t := by
  refine ContinuousOn.intervalIntegrable ?_
  refine (continuousOn_gammaPDFReal ha r).mono ?_
  rw [Set.uIcc_of_le ht]
  exact fun x hx ↦ hx.1

/-! ### The Gamma CDF as an interval integral -/

/-- For shape `a ≥ 1`, the `Gamma(a, r)` measure of `Iic t` is the interval
integral of its density over `[0, t]` (the density vanishes on negatives). -/
lemma gammaMeasure_Iic {a : ℝ} (ha : 1 ≤ a) (hr : 0 < r) (ht : 0 ≤ t) :
    gammaMeasure a r (Set.Iic t)
      = ENNReal.ofReal (∫ s in (0:ℝ)..t, gammaPDFReal a r s) := by
  have hInt : IntegrableOn (gammaPDFReal a r) (Set.Icc 0 t) volume :=
    ((continuousOn_gammaPDFReal ha r).mono Set.Icc_subset_Ici_self).integrableOn_compact
      isCompact_Icc
  rw [show gammaMeasure a r = volume.withDensity (gammaPDF a r) from rfl,
    withDensity_apply _ measurableSet_Iic,
    lintegral_Iic_eq_lintegral_Iio_add_Icc _ ht,
    lintegral_gammaPDF_of_nonpos le_rfl, zero_add,
    show gammaPDF a r = fun s ↦ ENNReal.ofReal (gammaPDFReal a r s) from rfl,
    ← ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun s ↦
        gammaPDFReal_nonneg (by linarith) hr s),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]

/-! ### The Gamma-CDF difference identity (the analytic heart) -/

/-- The telescoping antiderivative: on `s ≥ 0`, `Φ_k(u) = (ru)ᵏ e^{−ru}/k!`
has derivative `γ_k(s) − γ_{k+1}(s)` (Gamma densities of natural shapes). -/
lemma hasDerivAt_gamma_antideriv {k : ℕ} (hk : k ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun u : ℝ ↦ (r * u) ^ k * rexp (-(r * u)) / k !)
      (gammaPDFReal k r s - gammaPDFReal (k + 1 : ℕ) r s) s := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 :=
    ⟨k - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hk)).symm⟩
  have h1 : HasDerivAt (fun u : ℝ ↦ (r * u) ^ (m + 1))
      (((m + 1 : ℕ) : ℝ) * (r * s) ^ m * r) s := by
    have := (hasDerivAt_pow (m + 1) (r * s)).comp s ((hasDerivAt_id s).const_mul r)
    convert this using 1 <;> first | rfl | (push_cast; ring)
  have h2 : HasDerivAt (fun u : ℝ ↦ rexp (-(r * u)))
      (rexp (-(r * s)) * (-r)) s := by
    have := (((hasDerivAt_id s).const_mul r).neg).exp
    simpa using this
  have h3 := (h1.mul h2).div_const ((m + 1)! : ℝ)
  convert h3 using 1
  -- value identity: γ_{m+1}(s) − γ_{m+2}(s) equals the product-rule expression
  have hGm : Real.Gamma ((m + 1 : ℕ) : ℝ) = (m ! : ℝ) := by
    push_cast
    exact_mod_cast Real.Gamma_nat_eq_factorial m
  have hGm1 : Real.Gamma ((m + 1 + 1 : ℕ) : ℝ) = ((m + 1)! : ℝ) := by
    push_cast
    exact_mod_cast Real.Gamma_nat_eq_factorial (m + 1)
  have hs_pow : s ^ (((m + 1 : ℕ) : ℝ) - 1) = s ^ m := by
    rw [show ((m + 1 : ℕ) : ℝ) - 1 = ((m : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have hs_pow1 : s ^ (((m + 1 + 1 : ℕ) : ℝ) - 1) = s ^ (m + 1) := by
    rw [show ((m + 1 + 1 : ℕ) : ℝ) - 1 = ((m + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have hr_pow : r ^ (((m + 1 : ℕ) : ℕ) : ℝ) = r ^ (m + 1 : ℕ) :=
    Real.rpow_natCast r (m + 1)
  have hr_pow1 : r ^ (((m + 1 + 1 : ℕ) : ℕ) : ℝ) = r ^ (m + 1 + 1 : ℕ) :=
    Real.rpow_natCast r (m + 1 + 1)
  have hm0 : (m ! : ℝ) ≠ 0 := by positivity
  have hm10 : ((m + 1)! : ℝ) ≠ 0 := by positivity
  simp only [gammaPDFReal, ite_eq_left hs]
  rw [hGm, hGm1, hr_pow, hr_pow1, hs_pow, hs_pow1, Nat.factorial_succ]
  simp only [mul_pow]
  push_cast
  field_simp
  ring

/-- **Gamma-CDF difference identity.** For `k ≥ 1`, `r > 0`, `t ≥ 0`:
`∫₀ᵗ γ_k − ∫₀ᵗ γ_{k+1} = e^{−rt} (rt)ᵏ / k!` — the Poisson pmf appears as
the telescoping gap between consecutive Erlang CDFs (a formal calculus
identity; no positivity of `r` is needed). -/
lemma integral_gammaPDFReal_sub_succ (ht : 0 ≤ t)
    {k : ℕ} (hk : k ≠ 0) :
    (∫ s in (0:ℝ)..t, gammaPDFReal k r s)
        - ∫ s in (0:ℝ)..t, gammaPDFReal (k + 1 : ℕ) r s
      = rexp (-(r * t)) * (r * t) ^ k / k ! := by
  have hk1 : (1 : ℝ) ≤ ((k : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hk1' : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hint1 := intervalIntegrable_gammaPDFReal (a := ((k : ℕ) : ℝ)) (r := r) hk1 ht
  have hint2 := intervalIntegrable_gammaPDFReal (a := ((k + 1 : ℕ) : ℝ)) (r := r) hk1' ht
  rw [← intervalIntegral.integral_sub hint1 hint2,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs ↦ hasDerivAt_gamma_antideriv hk
        (by rw [Set.uIcc_of_le ht] at hs; exact hs.1))
      (hint1.sub hint2)]
  rw [mul_zero, zero_pow hk, zero_mul, zero_div, sub_zero]
  ring

/-- The base case against zero: `∫₀ᵗ γ_1 = 1 − e^{−rt}` (the exponential
CDF). -/
lemma integral_gammaPDFReal_one (ht : 0 ≤ t) :
    ∫ s in (0:ℝ)..t, gammaPDFReal 1 r s = 1 - rexp (-(r * t)) := by
  have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) t,
      HasDerivAt (fun u : ℝ ↦ -rexp (-(r * u))) (gammaPDFReal 1 r s) s := by
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    have h := hasDerivAt_neg_exp_mul_exp (r := r) (x := s)
    convert h using 1
    simp only [gammaPDFReal, ite_eq_left hs.1]
    rw [Real.Gamma_one, Real.rpow_one, sub_self, Real.rpow_zero]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_gammaPDFReal le_rfl ht)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  ring

/-! ### The marginal law of the counting process -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Poisson marginal law from interarrival times.** Let `ξ i` be iid `Exp(rate)`
interarrival times and `N` the counting process they generate. Then `N t = k`
exactly when the `k`-th arrival has happened by `t` and the `(k+1)`-st has not,
and `N t ∼ Poisson(rate · t)`.

The proof composes the Erlang law of the arrival times (the Gamma convolution
identity) with the Gamma-CDF difference identity. -/
theorem map_count_eq_poissonMeasure [IsProbabilityMeasure μ]
    {rate : ℝ≥0} (hrate : 0 < rate)
    {ξ : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (ξ i))
    (hnonneg : ∀ i ω, 0 ≤ ξ i ω)
    (hlaw : ∀ i, μ.map (ξ i) = expMeasure rate)
    (hindep : iIndepFun ξ μ)
    {N : ℝ → Ω → ℕ}
    (hcount : ∀ t k ω, N t ω = k ↔
      (∑ i ∈ Finset.range k, ξ i ω) ≤ t ∧ t < ∑ i ∈ Finset.range (k + 1), ξ i ω)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.map (N t) = poissonMeasure (rate * ⟨t, ht⟩) := by
  have hr : (0 : ℝ) < rate := NNReal.coe_pos.mpr hrate
  -- arrival times
  set T : ℕ → Ω → ℝ := fun k ω ↦ ∑ i ∈ Finset.range k, ξ i ω with hT
  have hTmeas : ∀ k, Measurable (T k) := fun k ↦
    Finset.measurable_sum _ fun i _ ↦ hmeas i
  have hTmono : ∀ k ω, T k ω ≤ T (k + 1) ω := fun k ω ↦ by
    rw [hT]
    simp only [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hnonneg k ω)
  -- the Erlang law of the k-th arrival
  have hTlaw : ∀ k : ℕ, k ≠ 0 → μ.map (T k) = gammaMeasure k rate := by
    intro k hk
    have h := ErlangSum.map_sum_iidExp hr hmeas hlaw hindep (Finset.range k)
      (Finset.nonempty_range_iff.mpr hk)
    rwa [show (∑ i ∈ Finset.range k, ξ i) = T k from
        funext fun ω ↦ Finset.sum_apply ω (Finset.range k) ξ,
      Finset.card_range] at h
  -- arrival events and their measures
  have hTset_meas : ∀ k, MeasurableSet {ω | T k ω ≤ t} := fun k ↦
    measurableSet_le (hTmeas k) measurable_const
  have hF : ∀ k : ℕ, k ≠ 0 → μ {ω | T k ω ≤ t}
      = ENNReal.ofReal (∫ s in (0:ℝ)..t, gammaPDFReal k rate s) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ ((k : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have hmap : μ {ω | T k ω ≤ t} = μ.map (T k) (Set.Iic t) := by
      rw [Measure.map_apply (hTmeas k) measurableSet_Iic]
      rfl
    rw [hmap, hTlaw k hk, gammaMeasure_Iic hk1 hr ht]
  -- the counting event as a difference of arrival events
  have hpre : ∀ k : ℕ,
      (N t) ⁻¹' {k} = {ω | T k ω ≤ t} \ {ω | T (k + 1) ω ≤ t} := by
    intro k
    ext ω
    simp [hcount t k ω, hT, not_le]
  have hNmeas : Measurable (N t) := measurable_to_countable' fun k ↦ by
    rw [hpre k]; exact (hTset_meas k).diff (hTset_meas (k + 1))
  have hsub : ∀ k : ℕ, {ω | T (k + 1) ω ≤ t} ⊆ {ω | T k ω ≤ t} :=
    fun k ω h ↦ le_trans (hTmono k ω) h
  have hdiff : ∀ k : ℕ, μ ((N t) ⁻¹' {k})
      = μ {ω | T k ω ≤ t} - μ {ω | T (k + 1) ω ≤ t} := by
    intro k
    rw [hpre k, measure_sdiff (hsub k) (hTset_meas (k + 1)).nullMeasurableSet
      (measure_ne_top μ _)]
  -- assemble per singleton
  refine Measure.ext_of_singleton fun k ↦ ?_
  rw [Measure.map_apply hNmeas (measurableSet_singleton k),
    poissonMeasure_singleton, hdiff k]
  have hco : ((rate * ⟨t, ht⟩ : ℝ≥0) : ℝ) = (rate : ℝ) * t := rfl
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · -- k = 0 : survival of the first arrival
    have hT0 : {ω | T 0 ω ≤ t} = Set.univ := by
      ext ω
      simp [hT, ht]
    have hexp_le : rexp (-((rate : ℝ) * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg rate.coe_nonneg ht))
    rw [hT0, measure_univ, hF 1 one_ne_zero,
      show ((1 : ℕ) : ℝ) = (1 : ℝ) from Nat.cast_one,
      integral_gammaPDFReal_one ht,
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
      ← ENNReal.ofReal_sub 1 (by linarith)]
    norm_num [hco]
  · -- k ≥ 1 : the Gamma-CDF difference identity
    have hk : k ≠ 0 := Nat.pos_iff_ne_zero.mp hkpos
    have hnn : 0 ≤ ∫ s in (0:ℝ)..t, gammaPDFReal (k + 1 : ℕ) rate s :=
      intervalIntegral.integral_nonneg ht fun s _ ↦
        gammaPDFReal_nonneg (by positivity) hr s
    rw [hF k hk, hF (k + 1) (Nat.succ_ne_zero k),
      ← ENNReal.ofReal_sub _ hnn,
      integral_gammaPDFReal_sub_succ ht hk, hco]

end PoissonCounting

end MathFin
