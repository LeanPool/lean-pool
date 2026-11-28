/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.Caplet
public import LeanPool.MathFin.Models.Rates.HullWhiteBondPriceAt

/-!
# Bond prices at `t > 0` in the Hull–White model

For the Hull–White discount factor `D t = exp(−∫₀ᵗ r)` (`HullWhite.bondRate`, continuous forcing
`θ`) and the natural filtration of the driving Brownian motion, `bondPrice` is the affine form of
the time-`0` price of the forcing seen from `t`, at the remaining maturity (`bondPrice_hullWhite`),
read off the conditional Laplace transform of the Wiener integral
(`HullWhite.bondRate_condExp`):

  `P(t, T) = A_t(T − t)·exp(−B(T − t)·r_t)`,   `A_t = bondA (θ(t + ·))`.

It is the Hull–White counterpart of `bondPrice_vasicek` (`Models/Rates/VasicekBond.lean`),
with the same proof; Vasicek is the constant forcing (`HullWhite.bondRate_const`).

## Main results

* `bondPrice_hullWhite` — `bondPrice` in the Hull–White model, almost surely.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  section 3.3.1
* [J. Hull and A. White, *Pricing interest-rate-derivative securities*][HullWhite1990]

## Tags

Hull–White model, zero-coupon bond price, affine term structure, short rate, Wiener integral,
MSC 91G30, JEL E43, JEL G12
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The Hull–White bond price at time `t`.** With `D t = exp(−∫₀ᵗ r)` along the integrated
Hull–White rate for continuous forcing `θ` and `𝓕` the natural filtration of the driving Brownian
motion, the price at `t` of one unit paid at `T` is `P(t, T) = A_t(T − t)·exp(−B(T − t)·r_t)`
almost surely, where `r_t` is the short rate in its Wiener representation, `B` is Vasicek's
coefficient and `A_t = bondA (θ(t + ·))` is the coefficient of the time-`0` price
(`HullWhite.bondPrice_affine`) of the forcing shifted to `t`. The measure is read as the pricing
measure. -/
theorem bondPrice_hullWhite (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    {θ : ℝ → ℝ} (hθ : Continuous θ) (κ σ r₀ : ℝ) (hκ : 0 < κ) {t T : ℝ≥0} (htT : t ≤ T) :
    bondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
        (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) t T
      =ᵐ[μ] fun ω ↦ HullWhite.bondA (fun s ↦ θ ((t : ℝ) + s)) σ κ ((T - t : ℝ≥0) : ℝ)
        * Real.exp (-(vasicekBondB κ ((T - t : ℝ≥0) : ℝ)
          * HullWhite.integratedRate hB θ κ σ r₀ hκ t ω)) := by
  filter_upwards [HullWhite.bondRate_condExp hB hBm hθ κ σ r₀ hκ htT] with ω h
  change (μ[fun ω ↦ Real.exp (-HullWhite.bondRate hB θ κ σ r₀ hκ T ω) | _]) ω
    / Real.exp (-HullWhite.bondRate hB θ κ σ r₀ hκ t ω) = _
  rw [h, mul_div_cancel_left₀ _ (Real.exp_pos _).ne']

end MathFin.Contracts
