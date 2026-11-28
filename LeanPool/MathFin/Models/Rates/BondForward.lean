/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.NoArbitrageDerivations

/-!
# Bond forward price from no-arbitrage

A forward contract on a coupon bond, struck at forward price `X`, maturing at
the forward-expiry date `t_fe`, has zero time-0 value exactly when discounting
the strike `X` paid at `t_fe` back to today equals the bond's price net of the
discounted coupons it sheds before `t_fe`,

  `Df(t_fe) · X = P₀ - Σ_{t ≤ t_fe} Df(t) · CF(t)`,

equivalently (the usual cash-and-carry forward-price statement: each coupon
`CF(t)` paid at `t ≤ t_fe` is kept along the way and is worth `Df(t) · CF(t)`
today)

  `X = (P₀ - Σ_{t ≤ t_fe} Df(t) · CF(t)) / Df(t_fe)`.

Here `s` is the caller-supplied set of coupon dates in `(0, t_fe]`; nothing in
`Finset ι` itself enforces that range, so passing it correctly is the
caller's responsibility. The coupon-stripped spot `P₀ - Σ Df(t)·CF(t)` plays
the role of `S₀` in `forward_price_from_no_arbitrage`
(`MathFin/Pricing/NoArbitrageDerivations.lean`), and
`bondForwardPrice_from_no_arbitrage` derives the forward price from it: in a
finite-state market whose state prices price the bond as its pre-expiry coupons
plus its value at `t_fe`, the forward contract paying `B(t_fe) - X` is worth
zero exactly at `X = bondForwardPrice`.

## Main definitions

* `bondForwardPrice`: the no-arbitrage forward price `X = (P₀ - Σ Df(t)·CF(t)) / Df(t_fe)` of a
  coupon bond, with the coupons paid before the forward expiry `t_fe` discounted out.

## Main results

* `bondForwardPrice_from_no_arbitrage`: the forward price derived from
  `forward_price_from_no_arbitrage`, with the coupon-stripped bond as the asset.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull]

## Tags

bond forward price, cash-and-carry, coupon-bearing bond, forward contract, no-arbitrage pricing,
state prices, MSC 91G30, JEL G13
-/

@[expose] public section

namespace MathFin

variable {ι : Type*}

/-- The **bond forward price**: the no-arbitrage forward price
`X = (P₀ - Σ Df(t)·CF(t)) / Df(t_fe)`. -/
noncomputable def bondForwardPrice (s : Finset ι) (Df : ι → ℝ) (CF : ι → ℝ)
    (P0 Df_fe : ℝ) : ℝ :=
  (P0 - ∑ t ∈ s, Df t * CF t) / Df_fe

/-- **Bond forward price from no-arbitrage.** A finite-state market with state
prices `q` on the states `Ω` at the forward-expiry date `t_fe`: the zero-coupon
bond to `t_fe` costs `Df_fe = Σ q ω` (`Df_fe ≠ 0`), and the bond, worth `B ω`
(ex-coupon) at `t_fe` in state `ω`, is priced as its coupons paid up to `t_fe`
plus its value then, `P₀ = Σ Df(t)·CF(t) + Σ q ω · B ω`. Then the forward
contract paying `B - X` at `t_fe` is worth zero iff `X = bondForwardPrice`:
this is `forward_price_from_no_arbitrage` with the coupon-stripped bond
`P₀ - Σ Df(t)·CF(t)` as the spot. -/
theorem bondForwardPrice_from_no_arbitrage {Ω : Type*} (states : Finset Ω) (q B : Ω → ℝ)
    (s : Finset ι) (Df CF : ι → ℝ) (P0 Df_fe X : ℝ) (hDf : Df_fe ≠ 0)
    (h_zcb : ∑ ω ∈ states, q ω = Df_fe)
    (h_bond : P0 = ∑ t ∈ s, Df t * CF t + ∑ ω ∈ states, q ω * B ω) :
    ∑ ω ∈ states, q ω * (B ω - X) = 0 ↔ X = bondForwardPrice s Df CF P0 Df_fe :=
  forward_price_from_no_arbitrage states q B Df_fe _ X hDf h_zcb (eq_sub_of_add_eq' h_bond.symm)

end MathFin
