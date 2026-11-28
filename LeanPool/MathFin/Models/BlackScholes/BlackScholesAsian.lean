/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Contracts.Instruments.Options
public import LeanPool.MathFin.Pricing.Value
public import LeanPool.MathFin.Models.BlackScholes.AsianGeometricN

/-!
# The geometric Asian call priced along the Black–Scholes path

`Models/BlackScholes/BlackScholes.lean` observes the underlying only at maturity, so its model map
is constant in time. A path-dependent instrument needs the price at several dates:
`BlackScholes.pathAssets` is the Black–Scholes market as a model map with the whole geometric
Brownian path, `S_u = S₀ exp((r − σ²/2)u + σ B_u)`, for a Brownian motion `B`.

Nothing new is proved about the geometric Asian option. The contract's value is the discounted
expected payoff (`Contract.value_pay`), which is exactly the integral
`MathFin.geomAsianN_call_price` evaluates once the observation product is rewritten as the
geometric mean of the path values.

## Main definitions

* `BlackScholes.pathAssets` — the geometric Brownian path as a model map `Unit → ℝ≥0 → Ω → ℝ`.

## Main results

* `BlackScholes.value_geomAsianCall` — `geomAsianCall K T τ` is worth the call price at the
  effective spot `geomAsianEffSpot` and volatility `geomAsianEffVol`.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 15.6
* [A. G. Z. Kemna and A. C. F. Vorst, *A pricing method for options based on average asset
  values*][KemnaVorst1990]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 4.5
* [Zhang, *Exotic Options*][ZhangExoticOptions]

## Tags

geometric Asian option, path-dependent option, geometric Brownian motion, Black–Scholes path,
MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The Black–Scholes market along a Brownian path as a model map: the single asset is
`S_u = S₀ exp((r − σ²/2)u + σ B_u)` at every time `u`. -/
noncomputable def pathAssets (S_0 r σ : ℝ) (B : ℝ≥0 → Ω → ℝ) : Unit → ℝ≥0 → Ω → ℝ :=
  fun _ u ω ↦ S_0 * Real.exp ((r - σ ^ 2 / 2) * u + σ * B u ω)

/-- **The geometric Asian call's Black–Scholes value** is the call price at the effective spot
and volatility of `geomAsianN_call_price`. For a pre-Brownian `B` under a probability measure
`μ`, averaging dates `τ` all at most the maturity `T > 0`, positive spot, strike and volatility,
and a nondegenerate log-driver variance, the value of `geomAsianCall K T τ` at the discount
`e^{−rT}` is `S_hat₀ Φ(d₁) − K e^{−rT} Φ(d₂)` with `S_hat₀ = geomAsianEffSpot` and volatility
`geomAsianEffVol`. -/
theorem value_geomAsianCall {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) {T : ℝ≥0} {n : ℕ} (hn : 0 < n) (τ : Fin n → ℝ≥0)
    (hτT : ∀ i, τ i ≤ T) {S_0 K r σ : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ)
    (hT : 0 < (T : ℝ)) (hV : 0 < geomAsianVar τ) :
    (geomAsianCall K T τ).value μ (fun _ _ ↦ Real.exp (-r * T)) (pathAssets S_0 r σ B)
      = geomAsianEffSpot S_0 r σ T τ *
          Phi (bsd1 (geomAsianEffSpot S_0 r σ T τ) K r (geomAsianEffVol σ T τ) T)
        - K * Real.exp (-r * T) *
          Phi (bsd2 (geomAsianEffSpot S_0 r σ T τ) K r (geomAsianEffVol σ T τ) T) := by
  rw [geomAsianCall, Contract.value_pay]
  refine Eq.trans ?_ (geomAsianN_call_price hB T hn τ hτT S_0 K r σ T hS₀ hK hσ hT hV)
  refine integral_congr_ae (.of_forall fun ω ↦ ?_)
  have hpos (i : Fin n) : 0 ≤ S_0 * Real.exp ((r - σ ^ 2 / 2) * (τ i : ℝ) + σ * B (τ i) ω) :=
    (mul_pos hS₀ (Real.exp_pos _)).le
  simp only [Payoff.eval, Payoff.eval_obsProd, scenarioAt, pathAssets, List.map_ofFn,
    List.prod_ofFn, Function.comp_def, NNReal.coe_inv, NNReal.coe_natCast]
  rw [Real.finsetProd_rpow _ _ fun i _ ↦ hpos i]

end MathFin.Contracts.BlackScholes
