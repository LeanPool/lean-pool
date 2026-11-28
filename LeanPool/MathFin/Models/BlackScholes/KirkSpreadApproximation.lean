/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.ExchangeOption
public import LeanPool.MathFin.Models.BlackScholes.MargrabeGrounding

/-!
# Kirk's approximation for spread options (`K ≠ 0`)

**This is an approximation, not an exact closed form.** The spread-option
payoff `max(S¹_T − S²_T − K, 0)` for `K ≠ 0` has no known exact Black–Scholes
closed form — unlike the `K = 0` case, which is the exact Margrabe exchange
option (`Models/BlackScholes/ExchangeOption.lean`). E. Kirk ("Correlation in the energy markets",
in *Managing Energy Price Risk*, Risk Publications, 1995, 71–78) prices it, in
forward terms, by treating `F² + K` as a single "pseudo-asset" and running
the Margrabe/Garman machinery on `F¹` vs. that pseudo-asset, approximating
the pseudo-asset's lognormal volatility by linearising `F²/(F² + K)` at its
initial value. Converting to spot via `Fⁱ = Sⁱ·e^{rT}` (no dividends), the
pseudo-strike becomes `S² + K·e^{-rT}` — only the cash strike `K` is
discounted, `S²` is already a present value — and the linearisation weight
becomes `w = S²₀/(S²₀ + K·e^{-rT})`. The resulting formula is a
Black-Scholes-style **undiscounted** spot price (`DF = 1`, since `S¹, S²`
already are present values) at an **effective volatility**

  `σ_eff² = σ₁² − 2ρσ₁σ₂ · w + σ₂² · w²`,  `w = S²₀/(S²₀ + K·e^{-rT})`,

which this file states and threads through the Garman normal form
(`GarmanNormalForm.lean`). It is a documented approximation (the
"pseudo-asset" is not actually lognormal), so for `K ≠ 0` no claim is made that
`kirkSpreadPrice` equals the true discounted expected payoff — only that it
is literally the standard BS closed form at this particular `(A, K', σ_eff)`.
At `K = 0` the discounted cash strike `K·e^{-rT}` is `0` for every `r`, so
the pseudo-asset reduces to `S²` itself for every `r`: both the
**effective-variance parameter** (`kirkEffectiveVariance_zero_eq_margrabe`)
and the **price itself** (`kirkSpreadPrice_zero_eq_margrabe`) collapse to
exactly Margrabe at `K = 0`, for every `r` (and `S²₀ ≠ 0`). Since Margrabe's formula is the
discounted expected exchange payoff in the two-GBM model (`margrabe_exchange_price`), Kirk's
price is exact at `K = 0` (`kirkSpreadPrice_zero_eq_expected`).

## Main definitions

* `kirkWeight`: the linearisation point `w = S²₀/(S²₀ + K)`.
* `kirkEffectiveVariance`: `σ₁² − 2ρσ₁σ₂·w + σ₂²·w²`, with `w = kirkWeight S2 K`.
* `kirkDiscountedStrike`: the discounted cash strike `K · e^{−rT}`.
* `kirkSpreadPrice`: Kirk's approximate spread-option price, the Black–Scholes closed form at the
  exchange leg `S¹₀` with pseudo-strike `S²₀ + K·e^{−rT}` and the effective variance (an
  approximation, shown exact at `K = 0`).

## Main results

* `kirk_variance_sub_weighted`: `Var[L₁ − w·L₂] = kirkEffectiveVariance · T` for log-prices
  with variances `σᵢ²T` and covariance `ρσ₁σ₂T` — the variance identity that defines Kirk's
  effective variance.
* `kirkEffectiveVariance_zero_eq_margrabe`: at `K' = 0` and `S²₀ ≠ 0` (so `w = 1`) Kirk's
  effective variance is exactly the Margrabe effective variance
  `σ₁² + σ₂² − 2ρσ₁σ₂`.
* `kirkSpreadPrice_zero_eq_margrabe`: at `K = 0`, for every `r` and `S²₀ ≠ 0`,
  `kirkSpreadPrice` is exactly `margrabePrice` at the Margrabe volatility
  `√(σ₁² + σ₂² − 2ρσ₁σ₂)` — a price-level equality, not just a variance-level one.
* `kirkSpreadPrice_zero_eq_expected`: in the two-GBM model of `margrabe_exchange_price`
  (`MargrabeGrounding.lean`), Kirk's price at `K = 0` is the discounted expected spread
  payoff — so the approximation is exact at zero strike. For `K ≠ 0` no accuracy statement
  is made.

## References

* [E. Kirk, *Correlation in the energy markets*][Kirk1995]

## Tags

Kirk approximation, spread option, energy markets, crack spread, approximate closed form, MSC 91G20,
JEL G13, JEL Q02
-/

@[expose] public section

namespace MathFin

open Real MeasureTheory ProbabilityTheory

/-- **Kirk's weight**: the linearisation point `w = S²₀/(S²₀ + K)` at which the
pseudo-asset `S² + K`'s lognormal volatility is approximated by `σ₂ · w`. -/
noncomputable def kirkWeight (S2 K : ℝ) : ℝ := S2 / (S2 + K)

/-- **Kirk's effective variance**: `σ₁² − 2ρσ₁σ₂·w + σ₂²·w²`, with
`w = kirkWeight S2 K`. It is `Var[L₁ − w·L₂]/T` for log-prices with variances `σᵢ²T` and
correlation `ρ` (`kirk_variance_sub_weighted`, the bilinear expansion of
`margrabe_variance_sub` with `L₂` scaled by `w`), i.e. Kirk's approximation is "Margrabe
with `S²` shrunk by `w`." -/
noncomputable def kirkEffectiveVariance (S2 K σ1 σ2 ρ : ℝ) : ℝ :=
  σ1 ^ 2 - 2 * ρ * σ1 * σ2 * kirkWeight S2 K + σ2 ^ 2 * kirkWeight S2 K ^ 2

/-- **Kirk's effective variance is a variance**: for square-integrable log-prices `L₁, L₂` with
`Var L₁ = σ₁²T`, `Var L₂ = σ₂²T` and `cov(L₁, L₂) = ρσ₁σ₂T`, the variance of `L₁ − w·L₂` at
Kirk's weight `w = kirkWeight S2 K` is `kirkEffectiveVariance S2 K σ₁ σ₂ ρ · T`
(`margrabe_variance_sub` applied to `L₁` and `w·L₂`). -/
theorem kirk_variance_sub_weighted {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {L₁ L₂ : Ω → ℝ} {S2 K σ1 σ2 ρ T : ℝ}
    (h₁ : MemLp L₁ 2 P) (h₂ : MemLp L₂ 2 P)
    (hV₁ : Var[L₁; P] = σ1 ^ 2 * T) (hV₂ : Var[L₂; P] = σ2 ^ 2 * T)
    (hcov : cov[L₁, L₂; P] = ρ * σ1 * σ2 * T) :
    Var[fun ω ↦ L₁ ω - kirkWeight S2 K * L₂ ω; P] = kirkEffectiveVariance S2 K σ1 σ2 ρ * T := by
  have h := margrabe_variance_sub h₁ (h₂.const_mul (kirkWeight S2 K))
  rw [variance_const_mul, covariance_const_mul_right, hV₁, hV₂, hcov] at h
  rw [show (fun ω ↦ L₁ ω - kirkWeight S2 K * L₂ ω) = L₁ - fun ω ↦ kirkWeight S2 K * L₂ ω
    from rfl, h]
  unfold kirkEffectiveVariance
  ring

/-- **Kirk reduces to Margrabe at `K = 0`**: for `S²₀ ≠ 0`, `kirkWeight S2 0 = 1`, so Kirk's
effective variance collapses to exactly the Margrabe effective variance
`σ₁² + σ₂² − 2ρσ₁σ₂` — the one point where the spread-option payoff
`max(S¹ − S² − K, 0)` is the *exact* exchange-option payoff. The price-level collapse to
`margrabePrice` is `kirkSpreadPrice_zero_eq_margrabe`. -/
theorem kirkEffectiveVariance_zero_eq_margrabe (S2 σ1 σ2 ρ : ℝ) (hS2 : S2 ≠ 0) :
    kirkEffectiveVariance S2 0 σ1 σ2 ρ = σ1 ^ 2 + σ2 ^ 2 - 2 * ρ * σ1 * σ2 := by
  unfold kirkEffectiveVariance kirkWeight
  rw [add_zero, div_self hS2]
  ring

/-- **Kirk's discounted cash strike** `K · e^{-rT}`: the only piece of the
pseudo-strike `S²₀ + K·e^{-rT}` that needs discounting, since `S²₀` is
already a spot (present-value) quantity while `K` is a cash amount paid
at `T`. -/
noncomputable def kirkDiscountedStrike (K r T : ℝ) : ℝ := K * Real.exp (-(r * T))

/-- **Kirk's approximate spread-option price**: the Garman-normal BS closed
form at `A = S¹₀` (the exchange leg), pseudo-strike
`K' = S²₀ + K·e^{-rT}`, `DF = 1` (both `S¹₀` and the pseudo-strike are
already present-value spot quantities, so no further discounting applies),
and effective volatility `√(kirkEffectiveVariance S²₀ (K·e^{-rT}) σ₁ σ₂ ρ)`.
Documented as an **approximation**: this is Kirk's (1995) heuristic, not the
exact discounted expected payoff of `max(S¹_T − S²_T − K, 0)`. -/
noncomputable def kirkSpreadPrice (S1 S2 K r σ1 σ2 ρ T : ℝ) : ℝ :=
  bsVGarman S1 (S2 + kirkDiscountedStrike K r T) 1
    (Real.sqrt (kirkEffectiveVariance S2 (kirkDiscountedStrike K r T) σ1 σ2 ρ)) T

/-- **Kirk's price collapses to the Margrabe price at `K = 0`, for every `r`** (and `S²₀ ≠ 0`): the
discounted cash strike `kirkDiscountedStrike 0 r T` is `0` regardless of `r` (nothing to
discount), so the pseudo-asset is `S²₀` itself, the effective variance is Margrabe's
(`kirkEffectiveVariance_zero_eq_margrabe`), and `kirkSpreadPrice` is `margrabePrice` at the
Margrabe volatility `√(σ₁² + σ₂² − 2ρσ₁σ₂)` — the point where the spread payoff
`max(S¹ − S² − K, 0)` is the exchange-option payoff. -/
theorem kirkSpreadPrice_zero_eq_margrabe (S1 r σ1 σ2 ρ T : ℝ) {S2 : ℝ} (hS2 : S2 ≠ 0) :
    kirkSpreadPrice S1 S2 0 r σ1 σ2 ρ T =
      margrabePrice S1 S2 (Real.sqrt (σ1 ^ 2 + σ2 ^ 2 - 2 * ρ * σ1 * σ2)) T := by
  rw [← kirkEffectiveVariance_zero_eq_margrabe S2 σ1 σ2 ρ hS2]
  unfold kirkSpreadPrice kirkDiscountedStrike
  rw [zero_mul, add_zero]
  exact (margrabe_eq_bsVGarman S1 S2 _ T).symm

/-- **At zero strike Kirk's price is the expected spread payoff.** For two Black–Scholes
terminals driven by a jointly Gaussian pair of standard normals with covariance `ρ`, and a
non-degenerate spread variance `σ₁² + σ₂² − 2ρσ₁σ₂ > 0`, Kirk's approximate price at `K = 0`
equals `𝔼_P[e^{−rT}·max(S¹_T − S²_T − 0, 0)]` (`kirkSpreadPrice_zero_eq_margrabe` and
`margrabe_exchange_price`). -/
theorem kirkSpreadPrice_zero_eq_expected {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {W₁ W₂ : Ω → ℝ} {σ1 σ2 ρ S1 S2 r T : ℝ}
    (hjoint : HasGaussianLaw (fun ω ↦ (W₁ ω, W₂ ω)) P)
    (hW₁meas : Measurable W₁) (hW₂meas : Measurable W₂)
    (hW₁ : HasLaw W₁ (gaussianReal 0 1) P) (hW₂ : HasLaw W₂ (gaussianReal 0 1) P)
    (hcov : cov[W₁, W₂; P] = ρ) (hS1 : 0 < S1) (hS2 : 0 < S2) (hT : 0 < T)
    (hv : 0 < σ1 ^ 2 + σ2 ^ 2 - 2 * ρ * σ1 * σ2) :
    kirkSpreadPrice S1 S2 0 r σ1 σ2 ρ T
      = ∫ ω, Real.exp (-(r * T)) *
          max (bsTerminal S1 r σ1 T (W₁ ω) - bsTerminal S2 r σ2 T (W₂ ω) - 0) 0 ∂P := by
  simp_rw [sub_zero]
  rw [kirkSpreadPrice_zero_eq_margrabe S1 r σ1 σ2 ρ T hS2.ne',
    margrabe_exchange_price hjoint hW₁meas hW₂meas hW₁ hW₂ hcov hS1 hS2
      (Real.sqrt_pos.mpr hv) hT (Real.sq_sqrt hv.le)]

end MathFin
