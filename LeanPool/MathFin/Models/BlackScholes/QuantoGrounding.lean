/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.Dividends
public import LeanPool.MathFin.Probability.Brownian.BrownianMartingale

/-!
# The quanto correction, derived from a joint-Gaussian FX model

`Models/BlackScholes/Dividends.quantoForward` *posits* the quanto-adjusted forward
`S_hat = S₀·exp((r_dom − ρ σ_S σ_FX)·T)` — the drift adjustment `−ρ σ_S σ_FX` is baked into the
definition. This file **derives** it: under the domestic risk-neutral measure the foreign
asset's forward picks up exactly the log-covariance term `−ρ σ_S σ_FX` from the change of
measure that converts the foreign numéraire to the domestic one.

The domestic-measure expectation is the foreign-measure expectation weighted by the FX
Radon–Nikodym density `exp(−σ_FX√T·Z_FX − ½σ_FX²T)` (a Girsanov/Esscher tilt in the FX
driver). With the standard decomposition of the correlated FX driver into the asset driver
plus an independent component, `Z_FX = ρ Z_S + √(1−ρ²) Z_⊥`, the density-weighted expectation
factors through two independent Gaussian MGFs, and the cross-term `ρ σ_S σ_FX` emerges:

  `𝔼[S_T · exp(−σ_FX√T Z_FX − ½σ_FX²T)] = S₀·exp((r_dom − ρ σ_S σ_FX)·T) = quantoForward`.

This is the multi-asset analogue of `MargrabeGrounding` — the correction is *earned* from the
correlation, not assumed. It consumes only the standard-normal MGF and the independence
factorisation of the expectation.

## Main results

* `quantoForward_of_gaussian` — the density-weighted foreign expectation of the foreign
  terminal equals `quantoForward`, deriving the `−ρ σ_S σ_FX` drift adjustment.

## References

* [Reiner (1992)][Reiner1992]

## Tags

quanto option, quanto adjustment, foreign exchange correlation, change of measure, drift adjustment,
MSC 91G20, JEL G13, JEL F31
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- **The quanto forward, derived from a joint-Gaussian FX model.** With the foreign terminal
`S_T = S₀·exp((r_dom − σ_S²/2)T + σ_S√T·Z_S)` and the correlated FX log-driver
`Z_FX = ρ Z_S + √(1−ρ²) Z_⊥` (`Z_S`, `Z_⊥` independent `N(0,1)`), the FX-density-weighted
foreign expectation equals the quanto-adjusted forward — the `−ρ σ_S σ_FX` drift adjustment is
the log-covariance produced by the change of measure, not an assumption. -/
theorem quantoForward_of_gaussian
    (S₀ r_dom σ_S σ_FX ρ T : ℝ) (hT : 0 ≤ T) (hρ : ρ ^ 2 ≤ 1)
    {Z_S Z_perp : Ω → ℝ}
    (hZS : HasLaw Z_S (gaussianReal 0 1) μ) (hZperp : HasLaw Z_perp (gaussianReal 0 1) μ)
    (hZSm : Measurable Z_S) (hZperpm : Measurable Z_perp)
    (hindep : IndepFun Z_S Z_perp μ) :
    ∫ ω, (S₀ * Real.exp ((r_dom - σ_S ^ 2 / 2) * T + σ_S * Real.sqrt T * Z_S ω))
        * Real.exp (-(σ_FX * Real.sqrt T)
            * (ρ * Z_S ω + Real.sqrt (1 - ρ ^ 2) * Z_perp ω) - σ_FX ^ 2 * T / 2) ∂μ
      = quantoForward S₀ r_dom ρ σ_S σ_FX T := by
  set E : ℝ := (r_dom - σ_S ^ 2 / 2) * T - σ_FX ^ 2 * T / 2 with hE
  set a : ℝ := (σ_S - ρ * σ_FX) * Real.sqrt T with ha
  set b : ℝ := -(σ_FX * Real.sqrt (1 - ρ ^ 2)) * Real.sqrt T with hb
  -- Pointwise: the integrand is `S₀·exp(E + a·Z_S + b·Z_⊥)`, an exponential affine in the drivers.
  have hpt : (fun ω ↦ (S₀ * Real.exp ((r_dom - σ_S ^ 2 / 2) * T + σ_S * Real.sqrt T * Z_S ω))
        * Real.exp (-(σ_FX * Real.sqrt T)
            * (ρ * Z_S ω + Real.sqrt (1 - ρ ^ 2) * Z_perp ω) - σ_FX ^ 2 * T / 2))
      = fun ω ↦ S₀ * Real.exp (E + a * Z_S ω + b * Z_perp ω) := by
    funext ω
    rw [hE, ha, hb, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  -- Factor the affine form in the two independent drivers via the shared MGF lemma.
  rw [hpt, integral_const_mul, integral_exp_affine_indep hZS hZperp hZSm hZperpm hindep]
  -- Final algebra: the cross-term `−ρ σ_S σ_FX` emerges from `a²`.
  have ha2 : a ^ 2 = (σ_S - ρ * σ_FX) ^ 2 * T := by rw [ha, mul_pow, Real.sq_sqrt hT]
  have hb2 : b ^ 2 = σ_FX ^ 2 * (1 - ρ ^ 2) * T := by
    rw [hb, show (-(σ_FX * Real.sqrt (1 - ρ ^ 2)) * Real.sqrt T) ^ 2
        = σ_FX ^ 2 * (Real.sqrt (1 - ρ ^ 2)) ^ 2 * (Real.sqrt T) ^ 2 from by ring,
      Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - ρ ^ 2), Real.sq_sqrt hT]
  rw [quantoForward, ha2, hb2, hE,
    show (r_dom - ρ * σ_S * σ_FX) * T
      = ((r_dom - σ_S ^ 2 / 2) * T - σ_FX ^ 2 * T / 2)
        + (σ_S - ρ * σ_FX) ^ 2 * T / 2 + σ_FX ^ 2 * (1 - ρ ^ 2) * T / 2 from by ring]

end MathFin
