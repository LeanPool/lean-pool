/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.FTAP.FTAPOnePeriodVector

/-!
# One-period FTAP on a general probability space (scalar)

The one-period Fundamental Theorem of Asset Pricing (Föllmer–Schied, *Stochastic Finance*,
§1.2; the one-period case of Dalang–Morton–Willinger) for a single scalar discounted excess
return `Y` on an **arbitrary** probability space `(Ω, P)`: no arbitrage ↔ there is an
equivalent martingale measure `Q ~ P` with `Y` integrable and `E_Q[Y] = 0`.

`Y ∈ L⁰` here: it need not be bounded, and integrability is not free.

## Relation to the vector and discrete-time theorems

`IsEMM` is the vector notion `OnePeriodVector.IsEMM` at `F = ℝ`, and `NoArbitrage` is the
vector no-arbitrage condition at `F = ℝ` (`noArbitrage_iff_vector`: on `ℝ` the inner
product `⟪θ, y⟫` is `θ · y`). So `ftap_one_period` is a corollary of
`OnePeriodVector.ftap_one_period_vector` at `F = ℝ`, and carries no proof of its own: the
backward direction (the L¹ tempering and the logistic tilt) and the forward direction
(`MathFin.IsEMM.noArbitrage`) are proved once, in the vector file. On a finite space
with trivial initial information, the one-step market of `Pricing/FTAP/FTAPDiscrete.lean` is
this market for `Y = S 1 − S 0` (`isEMM_one_iff_onePeriod`, `noArbitrage_one_iff_onePeriod`).

## Scope

One trading period, **one scalar asset**, arbitrary `(Ω, P)`. The `d`-asset
generalisation is `Pricing/FTAP/FTAPOnePeriodVector.lean`; the general-Ω **multi-period**
Dalang–Morton–Willinger theorem (which glues one-period conditional markets and needs a
measurable selection theorem) is not formalised.

## Main definitions

* `NoArbitrage`: any scalar position `θ` whose gain `θ · Y` is `P`-a.e. nonnegative has
  `θ · Y = 0` a.e.
* `IsEMM`: `Q ~ P`, `Y` is `Q`-integrable and `E_Q[Y] = 0`; the vector notion
  `OnePeriodVector.IsEMM` at `F = ℝ`.

## Main results

* `MathFin.OnePeriod.ftap_one_period`
* `MathFin.OnePeriod.noArbitrage_iff_vector`

## References

* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §1.2

## Tags

fundamental theorem of asset pricing, one-period model, no arbitrage, Föllmer–Schied,
equivalent martingale measure, JEL G13, MSC 91G20
-/

@[expose] public section

namespace MathFin.OnePeriod

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  (Y : Ω → ℝ)

/-- **No arbitrage**: no scalar position `θ` turns zero wealth into a sure
non-loss with a chance of gain — any `θ` whose discounted gain `θ · Y` is `≥ 0`
a.e. already has `θ · Y = 0` a.e. -/
def NoArbitrage : Prop :=
  ∀ θ : ℝ, 0 ≤ᵐ[P] (fun ω ↦ θ * Y ω) → (fun ω ↦ θ * Y ω) =ᵐ[P] 0

/-- **Equivalent martingale measure** (one period, scalar): `Q ~ P`, `Y` is `Q`-integrable,
and `E_Q[Y] = 0`. This is the library's one-period notion `OnePeriodVector.IsEMM` at
`F = ℝ`, with the same fields `toIsEquivProbMeasure` (`isProb`, `ac`, `ac'`), `int`, `fair`. -/
abbrev IsEMM (Q : Measure Ω) : Prop :=
  OnePeriodVector.IsEMM P Y Q

omit [IsProbabilityMeasure P] in
/-- **The scalar no-arbitrage condition is the vector one at `F = ℝ`.** On `ℝ` the inner
product `⟪θ, y⟫` is the product `θ · y`, so a scalar position `θ` with gain `θ · Y` is the
vector portfolio `θ ∈ ℝ`. With `IsEMM` defined as `OnePeriodVector.IsEMM` at `F = ℝ`, this
identifies `ftap_one_period` with `OnePeriodVector.ftap_one_period_vector` at `F = ℝ`. -/
theorem noArbitrage_iff_vector : NoArbitrage P Y ↔ OnePeriodVector.NoArbitrage P Y := by
  simp only [NoArbitrage, OnePeriodVector.NoArbitrage, Real.inner_apply]

/-- **One-period Fundamental Theorem of Asset Pricing** (scalar, general `Ω`).
For a single measurable discounted excess return `Y` on an arbitrary probability
space, *no arbitrage* holds if and only if there exists an *equivalent martingale
measure*: a `Q ~ P` under which `Y` is integrable and `E_Q[Y] = 0`. This is the
Föllmer–Schied / one-period Dalang–Morton–Willinger theorem for one asset, the `F = ℝ` case
of `OnePeriodVector.ftap_one_period_vector`; on a finite space with trivial initial
information its EMM and no-arbitrage notions are those of the horizon-`1` market of
`Pricing/FTAP/FTAPDiscrete.lean` (`isEMM_one_iff_onePeriod`, `noArbitrage_one_iff_onePeriod`). -/
theorem ftap_one_period (hY : Measurable Y) :
    NoArbitrage P Y ↔ ∃ Q, IsEMM P Y Q :=
  (noArbitrage_iff_vector P Y).trans (OnePeriodVector.ftap_one_period_vector P Y hY)

end MathFin.OnePeriod
