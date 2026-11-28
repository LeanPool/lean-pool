/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Contracts.Instruments.Options
public import LeanPool.MathFin.Pricing.Value
public import LeanPool.MathFin.Models.BlackScholes.MargrabeGrounding

/-!
# The exchange option priced in the two-asset Black–Scholes model

`Models/BlackScholes/BlackScholes.lean` prices the one-underlying instruments; the exchange option
`exchangeOption T` observes two underlyings, so it gets its own model map.
`BlackScholes.assets₂` is the two-asset Black–Scholes market at maturity: asset `i` is
`bsTerminal Sⁱ₀ r σᵢ T (Wᵢ ω)`, read at every time like `BlackScholes.assets`.

Nothing new is proved about Margrabe's formula. The contract's value is the discounted expected
exchange payoff (`Contract.value_pay`), which is exactly the integral `margrabe_exchange_price`
evaluates under the model measure, for jointly Gaussian standard-normal drivers.

## Main definitions

* `BlackScholes.assets₂` — the two-asset Black–Scholes terminal market as a model map
  `Fin 2 → ℝ≥0 → Ω → ℝ`.

## Main results

* `BlackScholes.value_exchangeOption` — `exchangeOption T` is worth `margrabePrice S¹₀ S²₀ σ_eff T`.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [W. Margrabe, *The value of an option to exchange one asset for another*][Margrabe1978]

## Tags

exchange option, Margrabe formula, two-asset model, outperformance option, MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The two-asset Black–Scholes market as a model map: asset `0` is `bsTerminal S₁ r σ₁ T (W₁ ω)`,
asset `1` is `bsTerminal S₂ r σ₂ T (W₂ ω)`, at every time. -/
noncomputable def assets₂ (S₁ S₂ r σ₁ σ₂ T : ℝ) (W₁ W₂ : Ω → ℝ) : Fin 2 → ℝ≥0 → Ω → ℝ :=
  fun i _ ω ↦ ![bsTerminal S₁ r σ₁ T (W₁ ω), bsTerminal S₂ r σ₂ T (W₂ ω)] i

/-- **The exchange option's Black–Scholes value is Margrabe's price.** For two Black–Scholes
terminals driven by a jointly Gaussian pair of standard-normal drivers with correlation `ρ`, the
value of `exchangeOption T` at the discount `e^{−rT}` is `margrabePrice S¹₀ S²₀ σ_eff T`, with
`σ_eff² = σ₁² + σ₂² − 2ρσ₁σ₂`. -/
theorem value_exchangeOption {P : Measure Ω} [IsProbabilityMeasure P]
    {W₁ W₂ : Ω → ℝ} {σ₁ σ₂ ρ σeff S1 S2 r : ℝ} {T : ℝ≥0}
    (hjoint : HasGaussianLaw (fun ω ↦ (W₁ ω, W₂ ω)) P)
    (hW₁meas : Measurable W₁) (hW₂meas : Measurable W₂)
    (hW₁ : HasLaw W₁ (gaussianReal 0 1) P) (hW₂ : HasLaw W₂ (gaussianReal 0 1) P)
    (hcov : cov[W₁, W₂; P] = ρ)
    (hS1 : 0 < S1) (hS2 : 0 < S2) (hσeff : 0 < σeff) (hT : 0 < (T : ℝ))
    (hσeff_sq : σeff ^ 2 = σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂) :
    (exchangeOption T).value P (fun _ _ ↦ Real.exp (-(r * T)))
        (assets₂ S1 S2 r σ₁ σ₂ T W₁ W₂)
      = margrabePrice S1 S2 σeff T := by
  rw [exchangeOption, Contract.value_pay]
  refine Eq.trans ?_ (margrabe_exchange_price hjoint hW₁meas hW₂meas hW₁ hW₂ hcov hS1 hS2
    hσeff hT hσeff_sq (r := r) (σ₁ := σ₁) (σ₂ := σ₂))
  refine integral_congr_ae (.of_forall fun ω ↦ ?_)
  simp [Payoff.eval, scenarioAt, assets₂]

end MathFin.Contracts.BlackScholes
