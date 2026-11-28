/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.PDE
public import Mathlib.Algebra.Order.Star.Real

/-!
# Lookback call lower bound

The lookback call's payoff `max(M − K, 0)` (with `M = max_{t ∈ [0,T]} S_t`)
dominates the vanilla call payoff `max(S_T − K, 0)` because `S_T ≤ M`.
Discounted to today, this gives the static lower bound:

`lookbackCall ≥ vanillaCall`.

## Main results

* `lookback_payoff_ge_vanilla`: `max(S − K, 0) ≤ max(M − K, 0)` when `S ≤ M`.
* `bsV_le_lookbackCall`: under the Black–Scholes lognormal hypothesis, the Black–Scholes
  call `bsV K r σ S₀ T` is at most `e^{−rT}·𝔼[max(M − K, 0)]` for any random variable
  `M ≥ S_T` (a.s.) whose call payoff is integrable — the running maximum is one such `M`.
  The law of the running maximum is not used, and no closed form for the lookback is
  claimed.

## References

* [M. B. Goldman, H. B. Sosin and M. A. Gatto, *Path dependent options: buy at the low, sell at the
  high*][GoldmanSosinGatto1979]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 26.8

## Tags

lookback option, running maximum, path-dependent option, static lower bound, exotic option,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory

/-- **Lookback call payoff lower bound**: if `S ≤ M` (the running max), then
`max(S − K, 0) ≤ max(M − K, 0)`. -/
lemma lookback_payoff_ge_vanilla (M S K : ℝ) (h : S ≤ M) :
    max (S - K) 0 ≤ max (M - K) 0 :=
  max_le_max (by linarith) le_rfl

/-- **The Black–Scholes call is a lower bound for the lookback call.** Under `BSCallHyp`, for
any random variable `M` dominating the terminal price `S_T = bsTerminal S₀ r σ T Z` almost
surely (the running maximum is one) and with an integrable call payoff, the Black–Scholes
call price is at most the discounted expected lookback payoff:
`bsV K r σ S₀ T ≤ e^{−rT}·𝔼[max(M − K, 0)]`. The integrability hypothesis is needed: without
it the Bochner integral on the right is `0`. -/
theorem bsV_le_lookbackCall {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    [IsProbabilityMeasure Q] {S_0 K r σ T : ℝ} {Z M : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z)
    (hM : ∀ᵐ ω ∂Q, bsTerminal S_0 r σ T (Z ω) ≤ M ω)
    (hint : Integrable (fun ω ↦ max (M ω - K) 0) Q) :
    bsV K r σ S_0 T ≤ ∫ ω, Real.exp (-r * T) * max (M ω - K) 0 ∂Q := by
  rw [← integral_bsCall_payoff_eq_bsV h]
  refine integral_mono_ae
    (((integrable_bsTerminal h.Z_law S_0 r σ T).sub' (integrable_const K)).pos_part.const_mul _)
    (hint.const_mul _) ?_
  filter_upwards [hM] with ω hω
  exact mul_le_mul_of_nonneg_left (lookback_payoff_ge_vanilla _ _ K hω) (Real.exp_pos _).le

end MathFin
