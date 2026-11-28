/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.BlackScholes

/-!
# Binary (digital) barrier options: Rubinstein & Reiner's closed form

A digital (cash-or-nothing / asset-or-nothing) option that is additionally knocked in or
knocked out by a single barrier `H` (Rubinstein & Reiner, *Risk* 4(9) (1991); Haug, *The Complete
Guide to Option Pricing Formulas*, 2nd ed. (2007), ch. 4, "Binary Barrier Options"). Unlike the
two-asset barriers in
`HeynenKatTwoAssetBarrier.lean`, this is single-underlying, single-variable Black–Scholes
machinery — no bivariate normal CDF needed.

Transcribed from QuantLib's
`ql/pricingengines/barrier/analyticbinarybarrierengine.cpp`
(`AnalyticBinaryBarrierEngine_helper::payoffAtExpiry`, upstream commit `6efc1ed`, 2026-09-23).
QuantLib computes a *drift* `mu` once (`mu = log(dividendDiscount/discount)/variance − 1/2`,
which for constant cost-of-carry `b = r − q` is `(b − σ²/2)/σ²`, i.e. the same `hkMu`-style
drift divided by `σ²`) and shares one formula shape between the **cash-or-nothing** payoff
(`K` = the fixed cash amount) and the **asset-or-nothing** payoff (`mu` shifted by `+1`, `K` =
the forward price `S·e^{bT}`, QuantLib's `spot·dividendDiscount/discount`). We keep `mu` an
explicit parameter rather than hard-wiring either case, exactly mirroring QuantLib's shared
code path — the docstrings below name which
`mu`/`K` substitution each payoff kind uses, but the lemmas hold for the shared formula shape
regardless of which substitution is made.

With `stdDev = σ√T`, `η = 1` for `Down{In,Out}` / `η = −1` for `Up{In,Out}`, `φ = 1` for a call /
`φ = −1` for a put:

  `x₁ = φ(log(S/X)/stdDev + μ·stdDev)`,  `x₂ = φ(log(S/H)/stdDev + μ·stdDev)`,
  `y₁ = η(log(H²/(SX))/stdDev + μ·stdDev)`,  `y₂ = η(log(H/S)/stdDev + μ·stdDev)`,

and, with `(H/S)^{2μ}` written as `exp(2μ·log(H/S))` (algebraically identical for `S, H > 0`;
QuantLib's own overflow guard evaluates the product `(H/S)^{2μ}·Φ(y)` as a whole in logs,
`exp(2μ·log(H/S) + log Φ(y))`, rather than this factor alone),

  `B₁ = Φ(x₁)`,  `B₂ = Φ(x₂)`,  `B₃ = (H/S)^{2μ}·Φ(y₁)`,  `B₄ = (H/S)^{2μ}·Φ(y₂)`.

QuantLib's 16-branch `switch` (barrier type × call/put × strike-vs-barrier) selects one of
`B₁, B₂, B₃, B₄` and their `±` combinations per branch; the final price is `discount·K·α`. The
16 branches are transcribed verbatim below as `bboDownInAlpha`/`bboDownOutAlpha` (both share
`η = 1`) and `bboUpInAlpha`/`bboUpOutAlpha` (both share `η = −1`).

## Main definitions

* `bboPhiOf`: the sign `φ`, equal to `1` for a call and `-1` for a put.
* `bboX1`, `bboX2`, `bboY1`, `bboY2`: the exponents of the four terms, struck at `X` (`x₁`), at the
  barrier `H` (`x₂`), at the reflected log `log (H²/(S X))` (`y₁`) and at `log (H/S)` (`y₂`).
* `bboHS2mu`: the factor `(H/S)^{2μ}`, written as `exp (2μ · log (H/S))`.
* `bboB1`, `bboB2`, `bboB3`, `bboB4`: the four building blocks `B₁` to `B₄` of the Rubinstein and
  Reiner binary-barrier formulas.
* `bboDownInAlpha`, `bboDownOutAlpha`, `bboUpInAlpha`, `bboUpOutAlpha`: the knock-in and knock-out
  `α`-factors for a down or up barrier (before the discount and payoff scale), each selected from
  `B₁` to `B₄` by `isCall` and the strike-barrier comparison `xGeH`.

## Main results

* `bboDownIn_add_DownOut`: knock-in + knock-out, same direction/type/regime, collapses to the
  vanilla digital α-factor `B₁` — the barrier-hit event and its complement partition the payoff
  (the closed-form counterpart of `BarrierParity.lean`'s
  `knockIn_add_knockOut_eq_vanilla`, checked on the literal 16-branch table; not derived from
  it here). Checked for every `(isCall, xGeH)` combination by `decide`-free case split.
* `bboUpIn_add_UpOut`: the same parity for the up-barrier family (`η = −1`).
* `bboB1_eq_Phi_bsd2`: at the risk-neutral drift `μ = (r − σ²/2)/σ²` the vanilla exponent
  `x₁` is Black–Scholes' `d₂` (`bsd2 S X r σ T`) — `B₁` is the standard-normal factor of the
  cash-or-nothing digital.
* `value_digitalCall_eq_bboB1`: under `BSCallHyp`, the Black–Scholes value of the digital call
  contract `Contracts.digitalCall K T` is the parity's vanilla leg `e^{−rT}·B₁` (call side),
  through `Contracts.BlackScholes.value_digitalCall`.

**Scope, disclosed honestly**: this is a transcription of the QuantLib closed form, not a
from-first-principles reflection-principle derivation of the barrier density. The in–out
identity here is the closed-form counterpart of the measure-theoretic parity
`knockIn_add_knockOut_eq_vanilla` (`BarrierParity.lean`): the barrier-hit event and its
complement partition the payoff, so knock-in + knock-out must equal the vanilla leg `B₁` —
and the 16-branch table satisfies it branch-by-branch (a misplaced `+`/`−` sign on any one of
the 14 sign-bearing QuantLib branches breaks it; the other two branches are the constant `0`),
though by pure term cancellation once the table is fixed. The vanilla leg alone is
grounded beyond transcription: `value_digitalCall_eq_bboB1` proves that, on the call side and
at the risk-neutral drift, `e^{−rT}·B₁` is the Black–Scholes value of the digital call contract. The
knock-in and knock-out terms are not proved to be prices. The `variance
= 0` and `(H/S)^{2μ}` overflow edge cases QuantLib special-cases numerically, and the
already-knocked-in/knocked-out spot guards `AnalyticBinaryBarrierEngine::calculate()` applies
*before* calling `payoffAtExpiry` (a `DownOut`/`UpOut` priced at `0` once the spot has already
crossed the barrier, a `DownIn`/`UpIn` re-priced as a plain vanilla digital via
`AnalyticEuropeanEngine` once it has), are all out of scope — this file formalizes exactly
`payoffAtExpiry`'s own closed form, for a spot strictly on the live side of the barrier.

## References

* [Haug, *The Complete Guide to Option Pricing Formulas*][Haug2007], ch. 4
* [Rubinstein and Reiner (1991)][RubinsteinReiner1991]

## Tags

digital barrier option, Rubinstein–Reiner, cash-or-nothing, knock-in knock-out, exotic option,
closed-form pricing, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory
open scoped NNReal

/-- `φ(isCall) = 1` for a call, `−1` for a put (QuantLib's `phi`). -/
noncomputable def bboPhiOf (isCall : Bool) : ℝ := if isCall then 1 else -1

/-- **`x₁`**: the `B₁`-side exponent for the payoff struck at `X`. -/
noncomputable def bboX1 (S X mu σ T phi : ℝ) : ℝ :=
  phi * (Real.log (S / X) / (σ * Real.sqrt T) + mu * σ * Real.sqrt T)

/-- **`x₂`**: the `B₂`-side exponent, struck at the barrier `H` instead of `X`. -/
noncomputable def bboX2 (S H mu σ T phi : ℝ) : ℝ :=
  phi * (Real.log (S / H) / (σ * Real.sqrt T) + mu * σ * Real.sqrt T)

/-- **`y₁`**: the `B₃`-side exponent, built from the reflected log `log(H²/(SX))`. -/
noncomputable def bboY1 (S X H mu σ T eta : ℝ) : ℝ :=
  eta * (Real.log (H ^ 2 / (S * X)) / (σ * Real.sqrt T) + mu * σ * Real.sqrt T)

/-- **`y₂`**: the `B₄`-side exponent, built from `log(H/S)`. -/
noncomputable def bboY2 (S H mu σ T eta : ℝ) : ℝ :=
  eta * (Real.log (H / S) / (σ * Real.sqrt T) + mu * σ * Real.sqrt T)

/-- **`(H/S)^{2μ}`**, written as `exp(2μ·log(H/S))` — algebraically the same value for
`S, H > 0`. QuantLib's own overflow guard evaluates this factor together with its `Φ(y)`
multiplier as one logged product, not this factor alone. -/
noncomputable def bboHS2mu (S H mu : ℝ) : ℝ := Real.exp (2 * mu * Real.log (H / S))

/-- **`B₁`**: the vanilla (barrier-free) digital `α`-factor for the `isCall` side — cash-or-nothing
or asset-or-nothing depending on which `mu`/`K` substitution is made (see the module docstring);
the price itself is `discount·K·B₁`, not `B₁` alone. -/
noncomputable def bboB1 (S X mu σ T : ℝ) (isCall : Bool) : ℝ :=
  Phi (bboX1 S X mu σ T (bboPhiOf isCall))

/-- **`B₂`**: `B₁` with the strike replaced by the barrier `H`. -/
noncomputable def bboB2 (S H mu σ T : ℝ) (isCall : Bool) : ℝ :=
  Phi (bboX2 S H mu σ T (bboPhiOf isCall))

/-- **`B₃`**: the reflected term paired with `B₁` across the barrier. -/
noncomputable def bboB3 (S X H mu σ T eta : ℝ) : ℝ :=
  bboHS2mu S H mu * Phi (bboY1 S X H mu σ T eta)

/-- **`B₄`**: the reflected term paired with `B₂` across the barrier. -/
noncomputable def bboB4 (S H mu σ T eta : ℝ) : ℝ :=
  bboHS2mu S H mu * Phi (bboY2 S H mu σ T eta)

/-- **Down-barrier knock-in value** (`η = 1`), QuantLib's `DownIn` switch case: `B₃` when
`isCall` and the strike dominates the barrier (`xGeH`), `B₁ − B₂ + B₄` when `isCall` and
`X < H`, `B₂ − B₃ + B₄` for a put with `X ≥ H`, and `B₁` for a put with `X < H`. -/
noncomputable def bboDownInAlpha (S X H mu σ T : ℝ) (isCall xGeH : Bool) : ℝ :=
  match isCall, xGeH with
  | true, true => bboB3 S X H mu σ T 1
  | true, false => bboB1 S X mu σ T true - bboB2 S H mu σ T true + bboB4 S H mu σ T 1
  | false, true => bboB2 S H mu σ T false - bboB3 S X H mu σ T 1 + bboB4 S H mu σ T 1
  | false, false => bboB1 S X mu σ T false

/-- **Down-barrier knock-out value** (`η = 1`), QuantLib's `DownOut` switch case: `B₁ − B₃`,
`B₂ − B₄`, `B₁ − B₂ + B₃ − B₄`, or `0`, selected the same way as `bboDownInAlpha`. -/
noncomputable def bboDownOutAlpha (S X H mu σ T : ℝ) (isCall xGeH : Bool) : ℝ :=
  match isCall, xGeH with
  | true, true => bboB1 S X mu σ T true - bboB3 S X H mu σ T 1
  | true, false => bboB2 S H mu σ T true - bboB4 S H mu σ T 1
  | false, true =>
      bboB1 S X mu σ T false - bboB2 S H mu σ T false + bboB3 S X H mu σ T 1 - bboB4 S H mu σ T 1
  | false, false => 0

/-- **Up-barrier knock-in value** (`η = −1`), QuantLib's `UpIn` switch case: `B₁`, `B₂ − B₃ + B₄`,
`B₁ − B₂ + B₄`, or `B₃`, selected the same way as `bboDownInAlpha` (note the branches swap
relative to `DownIn`: the `isCall ∧ xGeH` branch is `B₁` here, not `B₃`). -/
noncomputable def bboUpInAlpha (S X H mu σ T : ℝ) (isCall xGeH : Bool) : ℝ :=
  match isCall, xGeH with
  | true, true => bboB1 S X mu σ T true
  | true, false => bboB2 S H mu σ T true - bboB3 S X H mu σ T (-1) + bboB4 S H mu σ T (-1)
  | false, true => bboB1 S X mu σ T false - bboB2 S H mu σ T false + bboB4 S H mu σ T (-1)
  | false, false => bboB3 S X H mu σ T (-1)

/-- **Up-barrier knock-out value** (`η = −1`), QuantLib's `UpOut` switch case: `0`,
`B₁ − B₂ + B₃ − B₄`, `B₂ − B₄`, or `B₁ − B₃`. -/
noncomputable def bboUpOutAlpha (S X H mu σ T : ℝ) (isCall xGeH : Bool) : ℝ :=
  match isCall, xGeH with
  | true, true => 0
  | true, false =>
      bboB1 S X mu σ T true - bboB2 S H mu σ T true + bboB3 S X H mu σ T (-1)
        - bboB4 S H mu σ T (-1)
  | false, true => bboB2 S H mu σ T false - bboB4 S H mu σ T (-1)
  | false, false => bboB1 S X mu σ T false - bboB3 S X H mu σ T (-1)

/-- **In–out parity, down-barrier family**: for every call/put choice and every
strike-vs-barrier regime, the down-knock-in and down-knock-out values (QuantLib's `DownIn` and
`DownOut` switch cases, `η = 1` throughout) sum to the vanilla digital α-factor `B₁` — the
closed-form counterpart of `knockIn_add_knockOut_eq_vanilla`'s partition identity (not derived
from it here). Each of the
four `(isCall, xGeH)` branches cancels its `B₂, B₃, B₄` terms against the paired branch
independently (so a transposed sign on any one of the seven sign-bearing `Down*` branches
would break exactly that case; the eighth, the knock-out put with `X < H`, is the constant
`0`). On the call side, `value_digitalCall_eq_bboB1` identifies `e^{−rT}·B₁` with the value
of the digital call contract. -/
theorem bboDownIn_add_DownOut (S X H mu σ T : ℝ) (isCall xGeH : Bool) :
    bboDownInAlpha S X H mu σ T isCall xGeH + bboDownOutAlpha S X H mu σ T isCall xGeH
      = bboB1 S X mu σ T isCall := by
  cases isCall <;> cases xGeH <;>
    simp only [bboDownInAlpha, bboDownOutAlpha] <;> ring

/-- **In–out parity, up-barrier family**: the same parity for `UpIn`/`UpOut` (`η = −1`
throughout). -/
theorem bboUpIn_add_UpOut (S X H mu σ T : ℝ) (isCall xGeH : Bool) :
    bboUpInAlpha S X H mu σ T isCall xGeH + bboUpOutAlpha S X H mu σ T isCall xGeH
      = bboB1 S X mu σ T isCall := by
  cases isCall <;> cases xGeH <;>
    simp only [bboUpInAlpha, bboUpOutAlpha] <;> ring

/-- **The vanilla leg is Black–Scholes' cash-or-nothing factor.** At the risk-neutral drift
`μ = (r − σ²/2)/σ²`, the `B₁` exponent `x₁ = log(S/X)/(σ√T) + μσ√T` is exactly Black–Scholes'
`d₂` with the same strike/rate/vol (`bsd2 S X r σ T`, `Models/BlackScholes/Call.lean`): the two
disagree by `μσ²T − (r − σ²/2)T = 0`. -/
theorem bboB1_eq_Phi_bsd2 (S X r σ T mu : ℝ) (hσ : σ ≠ 0) (hT : 0 < T)
    (hmu : mu = (r - σ ^ 2 / 2) / σ ^ 2) :
    bboB1 S X mu σ T true = Phi (bsd2 S X r σ T) := by
  have hsqrt : σ * Real.sqrt T ≠ 0 :=
    mul_ne_zero hσ (ne_of_gt (Real.sqrt_pos.mpr hT))
  simp only [bboB1, bboX1, bboPhiOf, ite_true, one_mul, bsd2, bsd1]
  congr 1
  rw [hmu]
  field_simp
  simp only [Real.sq_sqrt (le_of_lt hT)]
  ring

/-- **The parity's vanilla leg is the price of the digital call contract.** Under `BSCallHyp`
and at the risk-neutral drift `μ = (r − σ²/2)/σ²`, the value of the contract
`Contracts.digitalCall K T` (pay `1` at `T` if `S_T > K`) in the Black–Scholes model is the
discounted vanilla leg `e^{−rT}·B₁` (call side) of both parity theorems:
`Contracts.BlackScholes.value_digitalCall` prices it at `e^{−rT}·Φ(d₂)`, and
`bboB1_eq_Phi_bsd2` identifies `Φ(d₂)` with `B₁`. -/
theorem value_digitalCall_eq_bboB1 {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {S_0 K r σ mu : ℝ} {T : ℝ≥0} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) (hmu : mu = (r - σ ^ 2 / 2) / σ ^ 2) :
    (Contracts.digitalCall K T).value Q (fun _ _ ↦ Real.exp (-r * T))
        (Contracts.BlackScholes.assets S_0 r σ T Z)
      = Real.exp (-r * T) * bboB1 S_0 K mu σ T true := by
  rw [Contracts.BlackScholes.value_digitalCall h,
    bboB1_eq_Phi_bsd2 S_0 K r σ T mu h.σ_pos.ne' h.T_pos hmu]

end MathFin
