/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Gaussian.StandardNormal

/-!
# Standard normal moment-generating function: the one computation in BS

Every closed-form risk-neutral expectation under the BS lognormal hypothesis
reduces to a single identity:

  `∫ exp(c · Z) ∂N(0,1) = exp(c² / 2)`.

This is the *moment-generating function (MGF) of the standard normal*. It is
proved in `Probability.Gaussian.StandardNormal` as `integral_exp_mul_gaussianPDFReal_univ`
by completing-the-square (`exp(c · z) · pdf(0, 1, z) = exp(c²/2) · pdf(c, 1, z)`)
followed by integration of the shifted PDF against Lebesgue.

## How the MGF generates BS pricing

The standard-normal MGF is enough to derive *every* lognormal moment and
*every* European pricing formula in the BS family. The variations live in two
ancillary moves:

1. **Affine rescaling**: `S_T = S_0 · exp((r − σ²/2)T + σ√T · Z)` ⟹ exponents
   are of the form `α + β · Z`. Use `MGF(β)` plus the constant prefactor `exp(α)`.

2. **Half-line restriction**: when the payoff vanishes off `{S_T > K}`,
   integrate against the right tail (equivalent to multiplying by `Φ(d_i)`).

| Pricing target            | MGF instance        | Result                                       |
|---------------------------|---------------------|----------------------------------------------|
| Forward price `E[S_T]`    | `β = σ√T`           | `S_0 · exp(rT)`                              |
| `n`-th moment `E[S_T^n]`  | `β = n · σ√T`       | `S_0^n · exp(n·rT + n(n−1)/2 · σ²T)`         |
| Power forward `e^{−rT}·…` | same                | `S_0^n · exp((n−1)·rT + n(n−1)/2 · σ²T)`     |
| Lognormal variance        | derived from `n=2`  | `S_0² · exp(2rT) · (exp(σ²T) − 1)`           |
| BS call `e^{−rT}·E[(S−K)⁺]`| `β = σ√T`, half-line| `S · Φ(d₁) − K · e^{−rT} · Φ(d₂)`            |
| Variance swap log moment  | first-moment of Z   | `σ² T / 2` (no MGF; linear E[Z]=0)           |

All of these are already proved in this library. This file packages the
*affine-shifted* MGF identity that they share, as a named theorem suitable
for re-use, and serves as a navigational guide to the structural unification.

## Main results

* `integral_exp_affine_gaussianPDFReal_univ`: the affine-shifted MGF
  `∫ exp(α + β · z) · pdf(0, 1, z) = exp(α + β²/2)`.

The single-line corollary pattern: each downstream theorem unfolds a payoff
of the form `S_0^k · exp(α + β · Z)`, factors `S_0^k · exp(α)` out, and applies
this identity at `β`.

## Tags

moment generating function, lognormal moments, Black–Scholes, Gaussian expectation,
risk-neutral expectation, standard normal, MSC 60E10, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- **Affine-shifted standard-normal MGF** (Lebesgue form):
`∫ exp(α + β · z) · pdf(0, 1, z) dz = exp(α + β²/2)`.

Direct corollary of the bare MGF `integral_exp_mul_gaussianPDFReal_univ` plus
`exp(α + β·z) = exp(α) · exp(β·z)` and linearity of integration. -/
lemma integral_exp_affine_gaussianPDFReal_univ (α β : ℝ) :
    ∫ z, Real.exp (α + β * z) * gaussianPDFReal 0 1 z =
      Real.exp (α + β^2 / 2) := by
  -- Factor the integrand: exp(α + β·z) · pdf = exp(α) · (exp(β·z) · pdf).
  rw [show (fun z ↦ Real.exp (α + β * z) * gaussianPDFReal 0 1 z) =
        (fun z ↦ Real.exp α * (Real.exp (β * z) * gaussianPDFReal 0 1 z))
      from funext (fun z ↦ by rw [Real.exp_add]; ring)]
  rw [integral_const_mul, integral_exp_mul_gaussianPDFReal_univ]
  -- exp(α) · exp(β²/2) = exp(α + β²/2)
  rw [← Real.exp_add]

end MathFin
