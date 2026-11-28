/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Dependence.CorrelationFallacies

/-!
# Roll (1984): the bid-ask bounce spread estimator

Roll's model of a mid-price `m_t` contaminated by bid-ask bounce: the observed trade price is

`P_t = m_t + (s/2) * q_t`,

where `s ≥ 0` is the (constant) bid-ask spread and `q_t ∈ {-1, +1}` is the trade-direction
indicator (buy/sell), modelled as a fair random sign (`rademacher`, from
`MathFin.Probability.Dependence.CorrelationFallacies`). Roll's economic assumptions — stated here as
explicit, named hypotheses, since the original note leaves them implicit — are:

* the signs `q_t` have the `rademacher` law (pairwise independent fair coin flips across time —
  joint independence is never used);
* every pair of the five variables drawn from the two consecutive price changes that *splits
  across* the two changes (one variable feeding `ΔP_t`, the other `ΔP_{t-1}`) is independent,
  *except* the sign shared by the two changes with itself; independence *within* a single price
  change is not assumed.

The mid-price increments are also assumed square-integrable, so that the covariances exist.
Under these hypotheses the first-order autocovariance of the *trade-price change*
`ΔP_t = P_t - P_{t-1}` is `-(s/2)²`, nonpositive and strictly negative whenever `s ≠ 0`:

`Cov(ΔP_t, ΔP_{t-1}) = -(s/2)²`.

This is `covariance_rollPriceChange`. Covariance is bilinear and translation-invariant, so the
mean of the mid-price increments plays no role; only independence matters. Expanding the product and
discarding every covariance between independent variables leaves exactly one surviving term: the
own-covariance (variance) of the sign `q_{t-1}` shared between the two consecutive price changes,
whose variance is `1` (`variance_one_of_hasLaw_rademacher`). The identity is usually inverted into
the **Roll estimator** `s_hat = 2 √(-γ̂₁)` of the spread from the sample first-order autocovariance
`γ̂₁` of observed price changes; `rollSpread_eq_two_mul_sqrt` records the inversion at the level of
the model's covariance (`s = 2 √(-γ)` whenever `γ = -(s/2)²` and `s ≥ 0`). No sample
autocovariance, and no property of `s_hat` as an estimator, is formalized.

We state the result for three consecutive sign variables `q0 q1 q2` (representing
`q_{t-2}, q_{t-1}, q_t`) and two increments `dm1 dm2` (`Δm_{t-1}, Δm_t`), rather than threading a
time index through a stochastic process, since only these five variables and their pairwise
independence ever enter the computation.

The inversion is only meaningful when the sample autocovariance `γ̂₁` is nonpositive, as the model
predicts. If `γ̂₁ > 0` — which real data can and does produce, since the model is an
approximation — no `s` satisfies the hypothesis `γ = -(s/2)²` of `rollSpread_eq_two_mul_sqrt`, and
`Real.sqrt` of the negative argument `-γ̂₁` returns `0` by Mathlib's junk-value convention, so
naively evaluating `2 * Real.sqrt (-γ̂₁)` at `γ̂₁ > 0` silently yields a spread estimate of `0`
rather than signalling that the estimator is undefined there.

## Main definitions

* `rollPriceChange`: the Roll trade-price change `dm + (s/2) qNow - (s/2) qPrev` from a mid-price
  increment `dm`, a spread `s` and two consecutive trade-direction signs.

## Main results

* `variance_id_rademacher`, `variance_one_of_hasLaw_rademacher`: a fair random sign has variance
  `1`.
* `covariance_rollPriceChange`: `Cov(ΔP_t, ΔP_{t-1}) = -(s/2)²` under the stated law,
  integrability and independence hypotheses.
* `rollSpread_eq_two_mul_sqrt`: the algebraic inversion `s = 2 * √(-γ)` for `s ≥ 0` and any real
  `γ = -(s/2)²`; with `covariance_rollPriceChange` it gives `s = 2 * √(-Cov(ΔP_t, ΔP_{t-1}))`.

## References

* [R. Roll, *A simple implicit measure of the effective bid-ask spread in an efficient
  market*][Roll1984].

## Tags

Roll model, bid–ask bounce, effective spread, serial covariance, spread estimator,
market microstructure, MSC 62P05, MSC 91G70, JEL G14
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **A fair random sign has variance `1`.** -/
lemma variance_id_rademacher : Var[id; rademacher] = 1 := by
  have hmean : rademacher[id] = 0 := by simpa using integral_id_rademacher
  rw [variance_of_integral_eq_zero aemeasurable_id hmean]
  have hsq : ∀ᵐ x ∂rademacher, (id x : ℝ) ^ 2 = 1 := by
    filter_upwards [ae_rademacher] with x hx; rcases hx with h | h <;> simp [h]
  rw [integral_congr_ae hsq]
  simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **A fair random sign lies in every `L^p`**: it is bounded by `1`. -/
lemma memLp_id_rademacher (p : ℝ≥0∞) : MemLp id p rademacher :=
  MemLp.of_bound aestronglyMeasurable_id 1
    (by filter_upwards [ae_rademacher] with x hx; rcases hx with h | h <;> simp [h])

omit [IsProbabilityMeasure P] in
/-- **A fair random sign has variance `1`, transported along its law.** -/
lemma variance_one_of_hasLaw_rademacher {X : Ω → ℝ} (hX : HasLaw X rademacher P) :
    Var[X; P] = 1 := by
  rw [hX.variance_eq, variance_id_rademacher]

variable {q0 q1 q2 dm1 dm2 : Ω → ℝ} {s : ℝ}

/-- The Roll trade-price change built from a mid-price increment `dm` (`Δm_t`) and two
consecutive trade signs `qPrev qNow` (`q_{t-1}, q_t`), following `P_t = m_t + (s/2) q_t`. -/
noncomputable def rollPriceChange (dm qPrev qNow : Ω → ℝ) (s : ℝ) : Ω → ℝ :=
  dm + (fun ω ↦ s / 2 * qNow ω) - fun ω ↦ s / 2 * qPrev ω

/-- **Roll's (1984) autocovariance identity.** Under the explicitly-stated hypotheses —
`q0, q1, q2` are fair random signs (`rademacher` law), `dm1, dm2` are square-integrable, and
every pair drawn from the five variables `{q0, q1, q2, dm1, dm2}` that is *split across the two
consecutive price changes* (one variable feeding `ΔP_t`, the other `ΔP_{t-1}`) is independent,
except `q1` with itself — the lag-one autocovariance of the trade-price change is `-(s/2)²`: the
own-covariance of the shared sign `q1` is the only surviving term. Independence *within* a single
price change (e.g. `dm2` with `q2`, or `dm1` with `q0`) is never used and so is not assumed: those
pairs never get multiplied together by the covariance expansion. -/
theorem covariance_rollPriceChange
    (hq0 : HasLaw q0 rademacher P) (hq1 : HasLaw q1 rademacher P) (hq2 : HasLaw q2 rademacher P)
    (hdm1 : MemLp dm1 2 P) (hdm2 : MemLp dm2 2 P)
    (h_q2q1 : q2 ⟂ᵢ[P] q1) (h_q2q0 : q2 ⟂ᵢ[P] q0) (h_q1q0 : q1 ⟂ᵢ[P] q0)
    (h_dm2dm1 : dm2 ⟂ᵢ[P] dm1)
    (h_dm2q0 : dm2 ⟂ᵢ[P] q0) (h_dm2q1 : dm2 ⟂ᵢ[P] q1)
    (h_dm1q1 : dm1 ⟂ᵢ[P] q1) (h_dm1q2 : dm1 ⟂ᵢ[P] q2) :
    cov[rollPriceChange dm2 q1 q2 s, rollPriceChange dm1 q0 q1 s; P] = -(s / 2) ^ 2 := by
  have hq0' := hq0.memLp (memLp_id_rademacher 2)
  have hq1' := hq1.memLp (memLp_id_rademacher 2)
  have hq2' := hq2.memLp (memLp_id_rademacher 2)
  have hsq0 : MemLp (fun ω ↦ s / 2 * q0 ω) 2 P := hq0'.const_mul _
  have hsq1 : MemLp (fun ω ↦ s / 2 * q1 ω) 2 P := hq1'.const_mul _
  have hsq2 : MemLp (fun ω ↦ s / 2 * q2 ω) 2 P := hq2'.const_mul _
  rw [rollPriceChange, rollPriceChange,
    covariance_sub_sub (hdm2.add hsq2) hsq1 (hdm1.add hsq1) hsq0,
    covariance_add_left hdm2 hsq2 (hdm1.add hsq1), covariance_add_left hdm2 hsq2 hsq0,
    covariance_add_right hdm2 hdm1 hsq1, covariance_add_right hsq2 hdm1 hsq1,
    covariance_add_right hsq1 hdm1 hsq1,
    covariance_const_mul_right (X := dm2) (Y := q1) (s / 2),
    covariance_const_mul_left (X := q2) (Y := dm1) (s / 2),
    covariance_const_mul_left (X := q2) (Y := fun ω ↦ s / 2 * q1 ω) (s / 2),
    covariance_const_mul_right (X := q2) (Y := q1) (s / 2),
    covariance_const_mul_right (X := dm2) (Y := q0) (s / 2),
    covariance_const_mul_left (X := q2) (Y := fun ω ↦ s / 2 * q0 ω) (s / 2),
    covariance_const_mul_right (X := q2) (Y := q0) (s / 2),
    covariance_const_mul_left (X := q1) (Y := dm1) (s / 2),
    covariance_const_mul_left (X := q1) (Y := fun ω ↦ s / 2 * q1 ω) (s / 2),
    covariance_const_mul_right (X := q1) (Y := q1) (s / 2),
    covariance_const_mul_left (X := q1) (Y := fun ω ↦ s / 2 * q0 ω) (s / 2),
    covariance_const_mul_right (X := q1) (Y := q0) (s / 2),
    h_dm2dm1.covariance_eq_zero hdm2 hdm1, h_dm2q1.covariance_eq_zero hdm2 hq1',
    h_dm1q2.symm.covariance_eq_zero hq2' hdm1, h_q2q1.covariance_eq_zero hq2' hq1',
    h_dm2q0.covariance_eq_zero hdm2 hq0', h_q2q0.covariance_eq_zero hq2' hq0',
    h_dm1q1.symm.covariance_eq_zero hq1' hdm1,
    covariance_self hq1'.aemeasurable, variance_one_of_hasLaw_rademacher hq1,
    h_q1q0.covariance_eq_zero hq1' hq0']
  ring

/-- **Roll's (1984) spread estimator**: inverting the covariance identity algebraically gives
`s = 2 √(-Cov(ΔP_t, ΔP_{t-1}))` for `s ≥ 0`. Stated directly from the covariance value (rather
than re-deriving it from the independence hypotheses) since the inversion is pure algebra on a
real number `γ` standing for `cov[ΔP_t, ΔP_{t-1}; P]`. -/
theorem rollSpread_eq_two_mul_sqrt {γ : ℝ} (hs : 0 ≤ s) (hγ : γ = -(s / 2) ^ 2) :
    s = 2 * Real.sqrt (-γ) := by
  rw [hγ, neg_neg, Real.sqrt_sq (by positivity)]
  ring

end MathFin
