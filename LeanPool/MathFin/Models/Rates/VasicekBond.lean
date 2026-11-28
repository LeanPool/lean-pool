/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.Caplet
public import LeanPool.MathFin.Models.Rates.HullWhiteBond

/-!
# Bond prices at `t > 0` in the Vasicek model

`bondPrice Q 𝓕 D t T = 𝔼_Q[D T | 𝓕 t] / D t` (`Models/Rates/Caplet.lean`) is the price at `t`
of one unit paid at `T`, for any stochastic discount factor `D`. For the Vasicek discount factor
`D t = exp(−∫₀ᵗ r)` and the natural filtration of the driving Brownian motion it is the affine
form of the time-`0` price at the remaining maturity (`bondPrice_vasicek`):

  `P(t, T) = A(T − t)·exp(−B(T − t)·r_t)`.

It is the Hull–White price (`bondPrice_hullWhite`) at the constant forcing `θ ≡ κθ_v`
(`HullWhite.bondRate_const`, `HullWhite.bondA_const`, `HullWhite.integratedRate_const`).

## Main results

* `bondPrice_vasicek` — `bondPrice` in the Vasicek model, almost surely.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  section 3.2.1
* [O. Vasicek, *An equilibrium characterization of the term structure*][Vasicek1977]

## Tags

Vasicek model, bond price, affine term structure, conditional expectation, short rate,
zero-coupon bond, MSC 91G30, JEL E43
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The Vasicek bond price at time `t`.** With `D t = exp(−∫₀ᵗ r)` along the Vasicek integrated
rate and `𝓕` the natural filtration of the driving Brownian motion, the price at `t` of one unit
paid at `T` is `P(t, T) = A(T − t)·exp(−B(T − t)·r_t)` almost surely, where `r_t` is the short
rate in its Wiener representation and `A`, `B` are the coefficients of the time-`0` price at the
remaining maturity (`vasicekBondPrice_affine`). The measure is read as the pricing measure. -/
theorem bondPrice_vasicek (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) {t T : ℝ≥0} (htT : t ≤ T) :
    bondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
        (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) t T
      =ᵐ[μ] fun ω ↦ vasicekBondA θ σ κ ((T - t : ℝ≥0) : ℝ)
        * Real.exp (-(vasicekBondB κ ((T - t : ℝ≥0) : ℝ)
          * (vasicekSDEMean r₀ θ κ t + vasicekDiffusionTerm hB κ σ hκ.le t ω))) := by
  have hD : shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)
      = shortRateDiscount (HullWhite.bondRate hB (fun _ ↦ κ * θ) κ σ r₀ hκ) := by
    funext T ω
    simp only [shortRateDiscount, HullWhite.bondRate_const]
  rw [hD]
  filter_upwards [bondPrice_hullWhite hB hBm continuous_const κ σ r₀ hκ htT] with ω h
  rw [h, HullWhite.bondA_const θ σ hκ.ne', HullWhite.integratedRate_const]

end MathFin.Contracts
