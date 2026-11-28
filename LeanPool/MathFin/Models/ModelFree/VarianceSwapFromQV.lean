/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.BrownianQuadraticVariation

/-!
# Variance-swap log-price increment from Brownian quadratic variation (phase 32)

The pre-existing `Models/ModelFree/VarianceSwap.lean` proves the Demeterfi-
Derman-Kamal log-payoff identity `(2/T) · E[log(F/S_T)] = σ²` — the
*replicating-portfolio* characterisation of the variance-swap fair strike.

This file provides the *quadratic-variation* characterisation: the
expected squared increment of the BS log-price `X_t := log S_0 + (r −
σ²/2)·t + σ · B_t` over a single sub-interval `[s, t]` is

  `E[(X_t − X_s)²] = σ² · (t − s) + (r − σ²/2)² · (t − s)²`,

a direct algebraic consequence of `(X_t − X_s)² = σ²(B_t − B_s)² +
2σ(r−σ²/2)(t−s)(B_t − B_s) + (r−σ²/2)²(t−s)²`, integrating term by term
using

* `BrownianQuadraticVariation.integral_increment`: `E[B_t − B_s] = 0`,
* `BrownianQuadraticVariation.integral_sq_increment`: `E[(B_t − B_s)²] = t − s`.

In the limit of finer partitions of `[0, T]` (deferred to follow-up), the
drift contribution `(r−σ²/2)²·T²/(n+1)` vanishes and the realised
variance converges to `σ²·T`, matching the `varianceSwap_log_contribution`
result via a different functional of the same price process.

## Why this is a "bridge"

`Probability/Brownian/BrownianQuadraticVariation.lean` (L¹ QV identity for pure BM)
was previously **not consumed by any pricing module**. This file gives it
its first downstream use: deriving the per-increment expectation of the
*log-price* (with drift), the building block for the realised-variance /
QV-style derivation of the variance-swap fair strike.

## Main definitions

* `bsLogPrice`: the Black–Scholes log-price process `X_t = log S₀ + (r − σ²/2)·t + σ·B_t`.

## Main results

* `expected_bsLogPrice_sq_increment`: the per-increment QV identity for
  BS log-price.

## Tags

variance swap, quadratic variation, log-price, Black–Scholes, fair strike, Demeterfi–Derman–Kamal,
MSC 91G20, MSC 60J65, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ → Ω → ℝ}

/-- BS log-price process: `X_t(ω) = log S_0 + (r − σ²/2)·t + σ · B_t(ω)`. -/
noncomputable def bsLogPrice (S_0 r σ : ℝ) (B : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Real.log S_0 + (r - σ ^ 2 / 2) * t + σ * B t ω

/-- **Variance-swap per-increment QV identity** (phase 32, main theorem).
Under the `BrownianQuadraticVariation` hypothesis on `B` and a probability
measure `μ`, the expected squared increment of the BS log-price equals

  `E[(X_t − X_s)²] = σ² · (t − s) + (r − σ²/2)² · (t − s)²`,

for `s ≤ t`. Algebraically:
`(X_t − X_s)² = σ²(B_t − B_s)² + 2σ(r−σ²/2)(t−s)(B_t − B_s) + (r−σ²/2)²(t−s)²`,
and integrating term by term uses `integral_sq_increment` (E[X²] = t−s),
`integral_increment` (E[X] = 0), and the constancy of the drift² term.

In the equipartition of `[0, T]` with `n + 1` subintervals, the drift
contribution sums to `(r − σ²/2)² · T² / (n + 1) → 0`, so

  `lim_n E[Σ (X_{t_{k+1}} − X_{t_k})²] = σ² · T`,

the QV / realised-variance characterisation of the variance-swap fair
strike (deferred to a follow-up phase). -/
theorem expected_bsLogPrice_sq_increment
    [IsProbabilityMeasure μ]
    (hB : BrownianQuadraticVariation μ B)
    (S_0 r σ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (bsLogPrice S_0 r σ B t ω - bsLogPrice S_0 r σ B s ω) ^ 2 ∂μ
      = σ ^ 2 * (t - s) + (r - σ ^ 2 / 2) ^ 2 * (t - s) ^ 2 := by
  -- Increment: X_t - X_s = (r-σ²/2)(t-s) + σ(B_t - B_s)
  set a : ℝ := (r - σ ^ 2 / 2) * (t - s) with a_def
  have h_inc : ∀ ω : Ω,
      bsLogPrice S_0 r σ B t ω - bsLogPrice S_0 r σ B s ω =
      a + σ * (B t ω - B s ω) := by
    intro ω
    unfold bsLogPrice
    rw [a_def]; ring
  -- Squared: (a + σX)² = a² + 2aσX + σ²X²
  have h_sq : ∀ ω : Ω,
      (bsLogPrice S_0 r σ B t ω - bsLogPrice S_0 r σ B s ω) ^ 2 =
      a ^ 2 + 2 * a * σ * (B t ω - B s ω) + σ ^ 2 * (B t ω - B s ω) ^ 2 := by
    intro ω
    rw [h_inc]; ring
  -- Integrate term by term using public BQV helpers
  rw [show (fun ω ↦ (bsLogPrice S_0 r σ B t ω - bsLogPrice S_0 r σ B s ω) ^ 2) =
      (fun ω ↦ a ^ 2 + 2 * a * σ * (B t ω - B s ω) +
                σ ^ 2 * (B t ω - B s ω) ^ 2) from funext h_sq]
  have h_int_const : Integrable (fun _ : Ω ↦ a ^ 2) μ := integrable_const _
  have h_int_lin : Integrable
      (fun ω ↦ 2 * a * σ * (B t ω - B s ω)) μ :=
    (hB.integrable_increment hs hst).const_mul (2 * a * σ)
  have h_int_sq : Integrable
      (fun ω ↦ σ ^ 2 * (B t ω - B s ω) ^ 2) μ :=
    (hB.integrable_sq_increment hs hst).const_mul (σ ^ 2)
  -- Split the three-term integral via two `integral_add` extractions (avoids
  -- the syntactic-vs-definitional mismatch between `Integrable.add` Pi-form
  -- and the literal lambda in the goal).
  have h_split_outer :
      ∫ ω, a ^ 2 + 2 * a * σ * (B t ω - B s ω) +
            σ ^ 2 * (B t ω - B s ω) ^ 2 ∂μ
      = (∫ ω, a ^ 2 + 2 * a * σ * (B t ω - B s ω) ∂μ) +
        ∫ ω, σ ^ 2 * (B t ω - B s ω) ^ 2 ∂μ :=
    integral_add (h_int_const.add h_int_lin) h_int_sq
  have h_split_inner :
      ∫ ω, a ^ 2 + 2 * a * σ * (B t ω - B s ω) ∂μ
      = (∫ ω, (a : ℝ) ^ 2 ∂μ) +
        ∫ ω, 2 * a * σ * (B t ω - B s ω) ∂μ :=
    integral_add h_int_const h_int_lin
  have h_const_int : ∫ _ω : Ω, (a : ℝ) ^ 2 ∂μ = a ^ 2 := by
    rw [integral_const]; simp
  have h_lin_int : ∫ ω, 2 * a * σ * (B t ω - B s ω) ∂μ = 0 := by
    rw [integral_const_mul, hB.integral_increment hs hst, mul_zero]
  have h_sq_int : ∫ ω, σ ^ 2 * (B t ω - B s ω) ^ 2 ∂μ = σ ^ 2 * (t - s) := by
    rw [integral_const_mul, hB.integral_sq_increment hs hst]
  rw [h_split_outer, h_split_inner, h_const_int, h_lin_int, h_sq_int]
  rw [a_def]
  ring

end MathFin
