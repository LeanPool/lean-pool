/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.Caplet
public import LeanPool.MathFin.Models.Rates.GSRBondPriceAt

/-!
# Bond prices at `t > 0` in the GSR model

For the GSR discount factor `D t = exp(−∫₀ᵗ r)` (`gsrIntegratedRate`, two-piece volatility) and the
natural filtration of the driving Brownian motion, `bondPrice` is the affine form of
`gsrBondPrice_condExp` (`Models/Rates/HullWhiteBond.lean` and `VasicekBond.lean` are the
constant-volatility counterparts):

  `P(t, T) = A(t, T)·exp(−B(T − t)·r_t)`,   `A = gsrBondA`.

## Main results

* `bondPrice_gsr` — `bondPrice` in the GSR model, almost surely.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  section 3.3.1
* [J. Hull and A. White, *Pricing interest-rate-derivative securities*][HullWhite1990]
* [The QuantLib contributors, *QuantLib*][QuantLib], Gsr model

## Tags

Gaussian short rate, GSR model, affine bond price, zero-coupon bond, conditional expectation,
MSC 91G30, JEL E43, JEL G12
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The GSR bond price at time `t`.** With `D t = exp(−∫₀ᵗ r)` along the GSR integrated rate
(volatility `σ₁` up to `T*`, `σ₂` after) and `𝓕` the natural filtration of the driving Brownian
motion, the price at `t` of one unit paid at `T ≥ T*` is `P(t, T) = A(t, T)·exp(−B(T − t)·r_t)`
almost surely, where `r_t` is the short rate in its Wiener representation (`gsrShortRate`), `B` is
Vasicek's coefficient and `A = gsrBondA`. The measure is read as the pricing measure. -/
theorem bondPrice_gsr (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    (r₀ θ σ1 σ2 : ℝ) {κ : ℝ} (hκ : 0 < κ) {Tstar t T : ℝ≥0} (htT : t ≤ T) (hTstarT : Tstar ≤ T) :
    bondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
        (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) t T
      =ᵐ[μ] fun ω ↦ gsrBondA θ κ σ1 σ2 (Tstar : ℝ) t T
        * Real.exp (-(vasicekBondB κ ((T : ℝ) - t)
          * gsrShortRate hB r₀ θ σ1 σ2 hκ Tstar t ω)) := by
  filter_upwards [gsrBondPrice_condExp hB hBm r₀ θ σ1 σ2 hκ htT hTstarT] with ω h
  change (μ[fun ω ↦ Real.exp (-gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar T ω) | _]) ω
    / Real.exp (-gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar t ω) = _
  rw [h, mul_div_cancel_left₀ _ (Real.exp_pos _).ne']

end MathFin.Contracts
