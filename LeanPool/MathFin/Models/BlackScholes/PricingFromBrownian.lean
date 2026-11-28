/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.BSCallHypFromBrownian
public import LeanPool.MathFin.Models.BlackScholes.Put
public import LeanPool.MathFin.Models.BlackScholes.Digital
public import LeanPool.MathFin.Models.BlackScholes.PowerCall
public import LeanPool.MathFin.Models.BlackScholes.StockNumeraire
public import LeanPool.MathFin.Models.BlackScholes.Dividends
public import LeanPool.MathFin.Models.BlackScholes.DividendsGreeks
public import LeanPool.MathFin.Models.Credit.KMVMertonStructural

/-!
# Pricing entry points from a pre-Brownian motion (phase 31)

This file restates the Black–Scholes-family pricing formulas that are stated under the
marginal hypothesis `BSCallHyp` or `BachelierHyp` (call, put, put-call parity, the
Bachelier call, digitals, the power call, the call and put with a dividend yield, the
stock-numeraire exercise probability, KMV–Merton) with that hypothesis discharged by a
pre-Brownian motion `W : ℝ≥0 → Ω → ℝ` (`IsPreBrownianReal W Q` from the `BrownianMotion`
package).

Each corollary composes an existing pricing formula with `BSCallHyp.of_isPreBrownian` (or
`BachelierHyp.of_isPreBrownian`): the scaled `Z := W T.toNNReal / √T` discharges the
marginal-Gaussian hypothesis. All but the dividend put are term-mode one-liners; the dividend
put also folds the discount `e^{−rT} = e^{−qT}·e^{−(r−q)T}` into the closed form `bsPDiv`.

## Why this matters

The pricing theorems take the marginal `Z ~ N(0, 1)` as a hypothesis. The scaling lemma
(`scaled_isPreBrownian_eval_law`) shows that this marginal comes from any pre-Brownian motion,
so each formula listed above holds for the terminal value of an actual Brownian model. Only
the time-`T` marginal is used: nothing here concerns the price process before `T`.

## Main results

* `bs_call_formula_via_brownian`: BS call price formula from BM.
* `bs_put_formula_via_brownian`: BS put price formula from BM.
* `bs_put_call_parity_via_brownian`: put-call parity from BM.
* `bachelier_call_formula_via_brownian`: Bachelier call price formula from BM.
* `bs_dividends_put_formula_via_brownian`: the Black–Scholes–Merton put with a continuous
  dividend yield `q`, as the closed form `bsPDiv`, from BM. Consumed by
  `Models/BlackScholes/American/AmericanPutEuropeanBound`, which bounds the American put value below
  by it.

## Tags

Black–Scholes formula, Bachelier model, put–call parity, dividend yield, Brownian motion,
digital option, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **BS call pricing formula from a pre-Brownian motion**. Given a pre-
Brownian process `W` under `Q`, the BS call price formula

  `e^{−rT} · E[max(S_T − K, 0)] = S_0 · Φ(d_1) − K · e^{−rT} · Φ(d_2)`

holds for `S_T := bsTerminal S_0 r σ T (W T.toNNReal · / √T)`. -/
theorem bs_call_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        max (bsTerminal S_0 r σ T (W T.toNNReal ω / Real.sqrt T) - K) 0 ∂Q
      = S_0 * Phi (bsd1 S_0 K r σ T) -
        K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) :=
  bs_call_formula (BSCallHyp.of_isPreBrownian Q W hW hS_0 hK hσ hT)

/-- **BS put pricing formula from a pre-Brownian motion**. -/
theorem bs_put_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        max (K - bsTerminal S_0 r σ T (W T.toNNReal ω / Real.sqrt T)) 0 ∂Q
      = K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T)) -
        S_0 * Phi (-(bsd1 S_0 K r σ T)) :=
  bs_put_formula (BSCallHyp.of_isPreBrownian Q W hW hS_0 hK hσ hT)

/-- **Put-call parity from a pre-Brownian motion**. -/
theorem bs_put_call_parity_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    (∫ ω, Real.exp (-r * T) *
        max (bsTerminal S_0 r σ T (W T.toNNReal ω / Real.sqrt T) - K) 0 ∂Q)
      - (∫ ω, Real.exp (-r * T) *
        max (K - bsTerminal S_0 r σ T (W T.toNNReal ω / Real.sqrt T)) 0 ∂Q)
      = S_0 - K * Real.exp (-r * T) :=
  bs_put_call_parity (BSCallHyp.of_isPreBrownian Q W hW hS_0 hK hσ hT)

/-- **Bachelier call pricing formula from a pre-Brownian motion**. -/
theorem bachelier_call_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {S_0 K σ T : ℝ}
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, max (bachelierTerminal S_0 σ T
        (W T.toNNReal ω / Real.sqrt T) - K) 0 ∂Q
      = (S_0 - K) * Phi (bachelierD S_0 K σ T) +
        σ * Real.sqrt T *
          gaussianPDFReal 0 1 (bachelierD S_0 K σ T) :=
  bachelier_call_formula (BachelierHyp.of_isPreBrownian Q W hW hK hσ hT)

/-- **Cash-or-nothing digital from a pre-Brownian motion**. -/
theorem bs_cash_or_nothing_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        (Set.Ioi K).indicator (fun _ ↦ (1 : ℝ))
          (bsTerminal S_0 r σ T (W T.toNNReal ω / Real.sqrt T)) ∂Q
      = Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) :=
  bs_cash_or_nothing_formula (BSCallHyp.of_isPreBrownian Q W hW hS_0 hK hσ hT)

/-- **Asset-or-nothing digital from a pre-Brownian motion**. -/
theorem bs_asset_or_nothing_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        (Set.Ioi K).indicator (fun s ↦ s)
          (bsTerminal S_0 r σ T (W T.toNNReal ω / Real.sqrt T)) ∂Q
      = S_0 * Phi (bsd1 S_0 K r σ T) :=
  bs_asset_or_nothing_formula (BSCallHyp.of_isPreBrownian Q W hW hS_0 hK hσ hT)

/-- **Powered call from a pre-Brownian motion**. -/
theorem bs_power_call_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {S_0 K r σ T : ℝ} (a : ℕ) (ha : 0 < a)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        max (bsPowerTerminal S_0 r σ T a
          (W T.toNNReal ω / Real.sqrt T) - K) 0 ∂Q =
      bsPowerEffectiveSpot S_0 r σ T a *
        Phi (bsd1 (bsPowerEffectiveSpot S_0 r σ T a) K r ((a : ℝ) * σ) T) -
      K * Real.exp (-r * T) *
        Phi (bsd2 (bsPowerEffectiveSpot S_0 r σ T a) K r ((a : ℝ) * σ) T) :=
  bs_power_call_formula a ha hK (BSCallHyp.of_isPreBrownian Q W hW hS_0 hK hσ hT)

/-- **BS-with-dividends call from a pre-Brownian motion**. The drift used
in the marginal hypothesis is `r − q`. -/
theorem bs_dividends_call_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {S_0 K r q σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        max (bsTerminal S_0 (r - q) σ T
          (W T.toNNReal ω / Real.sqrt T) - K) 0 ∂Q
      = S_0 * Real.exp (-(q * T)) * Phi (bsd1 S_0 K (r - q) σ T)
        - K * Real.exp (-(r * T)) * Phi (bsd2 S_0 K (r - q) σ T) :=
  bs_dividends_call_formula
    (BSCallHyp.of_isPreBrownian (r := r - q) Q W hW hS_0 hK hσ hT)

/-- **Black–Scholes–Merton put with a continuous dividend yield, from a pre-Brownian
motion.** With the stock drifting at `r − q` under `Q` and discounting at `r`, the discounted
expected put payoff is the closed form

  `bsPDiv K r q σ S_0 T = e^{−qT}·(K·e^{−(r−q)T}·Φ(−d₂) − S_0·Φ(−d₁))`,

`d₁, d₂` taken at rate `r − q`. It is `bs_put_formula` at rate `r − q`, multiplied by
`e^{−qT}`: `e^{−rT} = e^{−qT}·e^{−(r−q)T}`. -/
theorem bs_dividends_put_formula_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {S_0 K r q σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) *
        max (K - bsTerminal S_0 (r - q) σ T (W T.toNNReal ω / Real.sqrt T)) 0 ∂Q
      = bsPDiv K r q σ S_0 T := by
  rw [bsPDiv, bsP, ← neg_mul (r - q),
    ← bs_put_formula (BSCallHyp.of_isPreBrownian (r := r - q) Q W hW hS_0 hK hσ hT),
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
  simp only [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Stock-numeraire exercise probability from a pre-Brownian motion**. -/
theorem stockNumeraire_exercise_probability_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    (∫ ω, (Set.Ioi (-bsd2 S_0 K r σ T)).indicator
      (fun z ↦ Real.exp (-r * T) * bsTerminal S_0 r σ T z / S_0)
        (W T.toNNReal ω / Real.sqrt T) ∂Q) =
        Phi (bsd1 S_0 K r σ T) :=
  stockNumeraire_exercise_probability
    (BSCallHyp.of_isPreBrownian Q W hW hS_0 hK hσ hT)

/-- **KMV-Merton default probability from a pre-Brownian motion**. -/
theorem kmvPD_eq_one_sub_survival_probability_via_brownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {V_0 F r σ_V T : ℝ}
    (hV : 0 < V_0) (hF : 0 < F) (hσ : 0 < σ_V) (hT : 0 < T) :
    kmvPD V_0 F r σ_V T =
      1 - (Q {ω | bsTerminal V_0 r σ_V T
        (W T.toNNReal ω / Real.sqrt T) > F}).toReal :=
  kmvPD_eq_one_sub_survival_probability hV hF
    (BSCallHyp.of_isPreBrownian Q W hW hV hF hσ hT)

end MathFin
