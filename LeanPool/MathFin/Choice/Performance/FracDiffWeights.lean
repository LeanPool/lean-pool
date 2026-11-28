/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Laws.Estimation
public import Mathlib.Analysis.Analytic.Binomial

/-!
# Fractional-differentiation weight recursion

López de Prado (*Advances in Financial Machine Learning*, ch. 5) builds the
fractionally-differenced series `(1-B)^d X` from a weight sequence computed by
the recursion `w_0 = 1`, `w_k = -w_{k-1}·(d-k+1)/k`, the binomial-series
coefficients of `(1-B)^d` for real exponent `d`.

This file states the recursion as `fracDiffWeight` and proves it agrees with
the closed-form alternating product `(-1)^k · ∏_{i<k} (d-i)/(i+1)`, by induction
directly on the recursion, and with `(-1)^k` times Mathlib's generalized binomial
coefficient `Ring.choose d k`. Through Mathlib's binomial series
(`Real.one_add_rpow_hasFPowerSeriesOnBall_zero`) the weights are the coefficients of
`(1 - x)^d`: `∑ₖ wₖ xᵏ = (1 - x)^d` for `|x| < 1` (a scalar `x`; the backshift operator
`B` itself is not formalized). It also records the elementary per-step magnitude
ratio relating consecutive weights. The ratio `|d-k|/(k+1)` tends to `1`; that the
weights nevertheless tend to `0` for `d > -1` is not proved here, and no decay
statement is.

The expanding-window differenced series `fracDiff d X t = ∑_{k ≤ t} wₖ X_{t-k}` is defined;
for an integer `d = n` the weights are `(-1)^k C(n, k)` and vanish beyond `n`, so `d = 1`
gives the first difference `X_{t+1} - X_t`. Applied to `X_t = μt + σB_t` with `B` a
pre-Brownian motion, observed on an equally spaced grid of `[0, T]`, the drift estimator
built from these first differences telescopes to the endpoint estimator of
`Probability/Laws/Estimation.lean`, so its law is `N(μ, σ²/T)` for every number of observations
(`hasLaw_fracDiff_one_driftEstimator`). Only the case `d = 1` enters there.

## Main definitions

* `fracDiffWeight`: the fractional-differentiation weights `w₀ = 1`, `w_{k+1} = −w_k (d − k)/(k+1)`.
* `fracDiff`: the expanding-window fractionally differenced series `∑_{k ≤ t} wₖ X_{t−k}`.

## Main results

* `fracDiffWeight_eq_prod`: `fracDiffWeight d k = (-1)^k * ∏ i ∈ range k, (d-i)/(i+1)`.
* `fracDiffWeight_eq_choose`: `fracDiffWeight d k = (-1)^k * Ring.choose d k`.
* `hasSum_fracDiffWeight_mul_pow`: `∑ₖ fracDiffWeight d k * x^k = (1 - x)^d` for `|x| < 1`.
* `abs_fracDiffWeight_succ`: `|fracDiffWeight d (k+1)| = |fracDiffWeight d k| * |d-k| / (k+1)`,
  the per-step magnitude ratio between consecutive weights.
* `fracDiffWeight_natCast`, `fracDiff_one_succ`: integer orders; `d = 1` is the first
  difference.
* `hasLaw_fracDiff_one_driftEstimator`: the first-difference drift estimator of a Brownian
  motion with drift has law `N(μ, σ²/T)`, whatever the sampling frequency.

## References

* [Hosking, *Fractional differencing*][Hosking1981]
* [López de Prado, *Advances in Financial Machine Learning*][LopezDePrado2018], ch. 5; ch. 5, §5.4
* [R. C. Merton, *On estimating the expected return on the market*][Merton1980], §I

## Tags

fractional differentiation, binomial series, López de Prado, stationarity, drift estimator,
long memory, MSC 62M10, MSC 60G22, JEL C22
-/

@[expose] public section

namespace MathFin

open scoped NNReal

/-- The fractional-differentiation weight recursion: `w_0 = 1`,
`w_{k+1} = -w_k · (d-k)/(k+1)` (i.e. `w_k = -w_{k-1}·(d-k+1)/k` for `k ≥ 1`). -/
noncomputable def fracDiffWeight (d : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => -fracDiffWeight d k * (d - k) / (k + 1)

@[simp] theorem fracDiffWeight_zero (d : ℝ) : fracDiffWeight d 0 = 1 := rfl

theorem fracDiffWeight_succ (d : ℝ) (k : ℕ) :
    fracDiffWeight d (k + 1) = -fracDiffWeight d k * (d - k) / (k + 1) := rfl

/-- Closed form: `w_k` is the alternating product `(-1)^k · ∏_{i<k} (d-i)/(i+1)`,
the real-exponent binomial coefficient `(-1)^k · C(d,k)`. -/
theorem fracDiffWeight_eq_prod (d : ℝ) (k : ℕ) :
    fracDiffWeight d k = (-1) ^ k * ∏ i ∈ Finset.range k, (d - i) / (i + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [fracDiffWeight_succ, ih, Finset.prod_range_succ]
    ring

/-- Per-step magnitude ratio: `|w_{k+1}| = |w_k| · |d-k| / (k+1)`. -/
theorem abs_fracDiffWeight_succ (d : ℝ) (k : ℕ) :
    |fracDiffWeight d (k + 1)| = |fracDiffWeight d k| * |d - k| / (k + 1) := by
  rw [fracDiffWeight_succ, abs_div, abs_mul, abs_neg,
    abs_of_pos (show (0 : ℝ) < (k : ℝ) + 1 by positivity)]

/-- `(k + 1) · C(d, k + 1) = C(d, k) · (d - k)`: the ratio recursion of Mathlib's
generalized binomial coefficient, the case `n = k + 1` of `Ring.choose_smul_choose`. -/
lemma succ_mul_ringChoose_succ (d : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * Ring.choose d (k + 1) = Ring.choose d k * (d - k) := by
  have h := Ring.choose_smul_choose d (Nat.le_add_right k 1)
  rw [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right,
    nsmul_eq_mul] at h
  push_cast at h
  exact h

/-- **The weights are signed generalized binomial coefficients**:
`fracDiffWeight d k = (-1)^k * Ring.choose d k`, with Mathlib's `Ring.choose`. -/
theorem fracDiffWeight_eq_choose (d : ℝ) (k : ℕ) :
    fracDiffWeight d k = (-1) ^ k * Ring.choose d k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : Ring.choose d (k + 1) = Ring.choose d k * (d - k) / (k + 1) := by
      rw [eq_div_iff (by positivity)]
      linear_combination succ_mul_ringChoose_succ d k
    rw [fracDiffWeight_succ, ih, h]
    ring

/-- **The weights are the binomial series of `(1 - x)^d`**: for `|x| < 1`,
`∑ₖ fracDiffWeight d k * x^k = (1 - x)^d`. From Mathlib's binomial series
`Real.one_add_rpow_hasFPowerSeriesOnBall_zero` at `-x` and `fracDiffWeight_eq_choose`. -/
theorem hasSum_fracDiffWeight_mul_pow (d : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k ↦ fracDiffWeight d k * x ^ k) ((1 - x) ^ d) := by
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := d)).hasSum (y := -x)
    (by rw [mem_eball_zero_iff, Real.eNorm_eq_ofReal_abs, abs_neg, ENNReal.ofReal_lt_one]
        exact hx)
  simp only [zero_add, binomialSeries_apply, List.ofFn_const, List.prod_replicate,
    smul_eq_mul] at h
  have hfun : (fun k ↦ fracDiffWeight d k * x ^ k) = fun k ↦ Ring.choose d k * (-x) ^ k := by
    funext k
    rw [fracDiffWeight_eq_choose, neg_pow]
    ring
  rw [hfun, sub_eq_add_neg]
  exact h

/-- **Integer orders**: for `d = n ∈ ℕ` the weights are `(-1)^k C(n, k)`, so they vanish
for `k > n` and `(1 - B)^n` is a finite difference. -/
theorem fracDiffWeight_natCast (n k : ℕ) :
    fracDiffWeight n k = (-1) ^ k * (n.choose k : ℝ) := by
  rw [fracDiffWeight_eq_choose, Ring.choose_natCast]

/-- The expanding-window fractionally differenced series (López de Prado, ch. 5):
`fracDiff d X t = ∑_{k ≤ t} wₖ X_{t-k}`, the binomial series of `(1 - B)^d` applied to `X`
and truncated at the start of the sample. -/
noncomputable def fracDiff (d : ℝ) (X : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (t + 1), fracDiffWeight d k * X (t - k)

/-- **`d = 1` is the first difference**: `fracDiff 1 X (t + 1) = X (t + 1) - X t`, since
`w₀ = 1`, `w₁ = -1` and `wₖ = 0` for `k ≥ 2` (`fracDiffWeight_natCast`). -/
theorem fracDiff_one_succ (X : ℕ → ℝ) (t : ℕ) : fracDiff 1 X (t + 1) = X (t + 1) - X t := by
  have h1 : fracDiffWeight 1 1 = -1 := by
    have h := fracDiffWeight_natCast 1 1
    norm_num at h
    exact h
  have h2 (k : ℕ) : fracDiffWeight 1 (k + 1 + 1) = 0 := by
    have h := fracDiffWeight_natCast 1 (k + 1 + 1)
    rw [Nat.cast_one, Nat.choose_eq_zero_of_lt (show 1 < k + 1 + 1 by omega), Nat.cast_zero,
      mul_zero] at h
    exact h
  rw [fracDiff, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [h2, zero_mul, Finset.sum_const_zero, zero_add, h1, fracDiffWeight_zero,
    Nat.add_sub_cancel, Nat.sub_zero]
  ring

open MeasureTheory ProbabilityTheory in
/-- **The first-difference drift estimator sees only the endpoints.** Let `X_t = μt + σB_t`
with `B` a pre-Brownian motion, observed at the `n ≥ 1` equally spaced times
`tₖ = kT/n` of `[0, T]`. The drift estimator `(1/T) ∑_{i<n} (fracDiff 1 X)_{i+1}`, the sum of
the first-differenced observations, telescopes to the endpoint estimator `(X_T - X_0)/T`, so it
has law `N(μ, σ²/T)` for every `n` (`drift_se_endpoint_hasLaw`, with the Brownian increment
`B_T - B_0 ∼ N(0, T)`): sampling more often does not shrink the standard error `σ/√T`. -/
theorem hasLaw_fracDiff_one_driftEstimator {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (mu sigma : ℝ)
    {T : ℝ≥0} (hT : 0 < T) {n : ℕ} (hn : 0 < n) :
    HasLaw (fun ω ↦ (∑ i ∈ Finset.range n,
        fracDiff 1 (fun k ↦ mu * (k * T / n : ℝ≥0) + sigma * B (k * T / n) ω) (i + 1)) / T)
      (gaussianReal mu (sigma ^ 2 / T).toNNReal) P := by
  have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum (ω : Ω) : ∑ i ∈ Finset.range n,
      fracDiff 1 (fun k ↦ mu * (k * T / n : ℝ≥0) + sigma * B (k * T / n) ω) (i + 1) =
        mu * T + sigma * (B T ω - B 0 ω) := by
    set X : ℕ → ℝ := fun k ↦ mu * (k * T / n : ℝ≥0) + sigma * B (k * T / n) ω with hX
    calc ∑ i ∈ Finset.range n, fracDiff 1 X (i + 1)
        = ∑ i ∈ Finset.range n, (X (i + 1) - X i) :=
          Finset.sum_congr rfl fun i _ ↦ fracDiff_one_succ X i
      _ = X n - X 0 := Finset.sum_range_sub X n
      _ = mu * T + sigma * (B T ω - B 0 ω) := by
          simp only [hX, Nat.cast_zero, zero_mul, zero_div, mul_div_cancel_left₀ T hn',
            NNReal.coe_zero]
          ring
  have hB0 : HasLaw (fun ω ↦ B T ω - B 0 ω) (gaussianReal 0 (T : ℝ).toNNReal) P := by
    convert hB.hasLaw_sub T 0 using 2
    ext
    simp
  convert drift_se_endpoint_hasLaw (NNReal.coe_pos.2 hT) mu sigma hB0 using 1
  funext ω
  rw [hsum ω]

end MathFin
