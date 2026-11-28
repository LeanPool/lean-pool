/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.StrikeGreeks
public import LeanPool.MathFin.Models.BlackScholes.StrikeConvexity

/-!
# Breeden-Litzenberger: implied risk-neutral PDF from option prices

The Breeden-Litzenberger identity says the risk-neutral PDF of the terminal
asset price `S_T`, evaluated at strike `K`, equals `e^{rT}` times the second
strike-derivative of the European call price:

  `f_{S_T}(K) = e^{rT} · ∂²_K C(K)`.

Specialising to the BS model: `∂²_K bsV = e^{-rT} · ϕ(d_2)/(K σ √T)`
(`hasDerivAt_deriv_bsV_K` in `StrikeGreeks.lean`), so

  `f_{S_T}(K) = ϕ(d_2(K)) / (K σ √T)`,

which is the lognormal density at `K` (parameters
`log S_0 + (r − σ²/2)T, σ² T`). This file defines `lognormalTerminalPDF` as that
formula. It proves neither that `S_T` has it as its density nor, beyond the
differential identity at the end, that it integrates to 1. Both are proved
downstream, for the Black–Scholes price (the jump-diffusion without jumps at the
drift `r − σ²/2`): the law of the price is `lognormalTerminalPDF(K) dK` on `(0, ∞)`
(`jumpDiffusionIncrementLaw_zero_map_mul_exp`) and the formula integrates to one
(`lintegral_lognormalTerminalPDF_eq_one`), in `JumpDiffusionDigital.lean`. Merton's
Poisson mixture of these formulas is `mertonTerminalPDF` (`MertonStrikeGreeks.lean`).

## Structural connection: PDF positivity = strike-convexity of the price

The non-negativity `0 ≤ f_{S_T}(K)` is *not* an independent fact. It is the
infinitesimal manifestation of a convexity chain:

1. The call **payoff** is convex in `K` (`convexOn_call_payoff` in
   `StrikeConvexity.lean`).
2. Risk-neutral expectation preserves convexity: integration against a positive
   measure does, for any law with a finite mean (`convexOn_integral_call`; the
   finite-state form is `callPrice_finiteState_convexOn_K`).
3. So the call **price** `K ↦ bsV K r σ S T` is convex in `K`.
4. So `∂²_K bsV ≥ 0`.
5. By Breeden-Litzenberger, `∂²_K bsV = e^{-rT} · f_{S_T}(K)`, so
   `f_{S_T}(K) ≥ 0`.

Every step is formal. Step 3 is step 2 for the standard normal law, the
Black–Scholes price being the discounted expected payoff (`bs_call_formula`,
`bsV_strike_convexOn`); it does not use the sign of the closed form. The
positivity of the standard normal law still enters, as `ϕ ≥ 0` inside
`bs_call_formula` (Mathlib's `integral_gaussianReal_eq_integral_smul`), and that
is also the fact `lognormalTerminalPDF_nonneg` uses. So the two proofs of the
sign of the density share their root: `lognormalTerminalPDF_nonneg` reads it off
the formula, and `lognormalTerminalPDF_nonneg_via_strike_convexity`, steps
3 → 4 → 5, explains it by the convexity of the payoff.

## Main definitions

* `lognormalTerminalPDF`: the lognormal density of `S_T` at strike `K`, written through the
  Black–Scholes `d₂`: `ϕ(d₂(K)) / (K · σ · √T)`.

## Main results

* `breedenLitzenberger`: `∂²_K bsV(K) = e^{-rT} · lognormalTerminalPDF(K)`.
* `lognormalTerminalPDF_nonneg`: `0 ≤ lognormalTerminalPDF`, directly.
* `lognormalTerminalPDF_nonneg_via_strike_convexity`: the same, from the strike
  convexity of the price.

## References

* [Breeden and Litzenberger, *Prices of state-contingent claims implicit in option
  prices*][BreedenLitzenberger1978]

## Tags

risk-neutral density, implied distribution, second strike derivative, state price density,
option-implied PDF, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- **Lognormal PDF of `S_T`** at strike `K`, expressed via the BS `d_2`
parameter: `f(K) = ϕ(d_2(K)) / (K · σ · √T)`. -/
noncomputable def lognormalTerminalPDF (S_0 r σ T K : ℝ) : ℝ :=
  gaussianPDFReal 0 1 (bsd2 S_0 K r σ T) / (K * σ * Real.sqrt T)

/-- **Breeden-Litzenberger formula** under the Black-Scholes model: the second
strike-derivative of the call price is the discounted lognormal density,
`∂²C/∂K² = e^{-rT} · lognormalTerminalPDF(K)`. This is `hasDerivAt_deriv_bsV_K` with the value
read as a density, since `lognormalTerminalPDF` unfolds to `ϕ(d₂) / (K σ √T)`. -/
theorem breedenLitzenberger {S_0 r σ : ℝ} (hS : 0 < S_0) (hσ : 0 < σ)
    {K T : ℝ} (hK : 0 < K) (hT : 0 < T) :
    HasDerivAt (deriv fun k ↦ bsV k r σ S_0 T)
      (Real.exp (-(r * T)) * lognormalTerminalPDF S_0 r σ T K) K :=
  (hasDerivAt_deriv_bsV_K hS hσ hK hT).congr_deriv (mul_div_assoc _ _ _)

/-- **Implied PDF non-negativity**, directly: `ϕ ≥ 0` and `K σ √T > 0`. The route through the
strike convexity of the price is `lognormalTerminalPDF_nonneg_via_strike_convexity`. That
`lognormalTerminalPDF` is a probability density is not proved here; it is
`lintegral_lognormalTerminalPDF_eq_one` (`JumpDiffusionDigital.lean`). -/
theorem lognormalTerminalPDF_nonneg
    {S_0 r σ T K : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    0 ≤ lognormalTerminalPDF S_0 r σ T K := by
  unfold lognormalTerminalPDF
  have h_pdf_nn : 0 ≤ gaussianPDFReal 0 1 (bsd2 S_0 K r σ T) :=
    gaussianPDFReal_nonneg _ _ _
  have h_den_pos : 0 < K * σ * Real.sqrt T :=
    mul_pos (mul_pos hK hσ) (Real.sqrt_pos.mpr hT)
  exact div_nonneg h_pdf_nn h_den_pos.le

/-! ## PDF non-negativity ← strike convexity

The proof of `lognormalTerminalPDF_nonneg` above uses direct positivity of the
gaussian PDF (one-line). This section records the **structural derivation**
through `bsV_strike_convexOn`, exhibiting PDF non-negativity as the
infinitesimal face of the K-convexity principle: convexity makes
`0 ≤ ∂²_K bsV` (`deriv_deriv_nonneg_of_convexOn`), and Breeden-Litzenberger
identifies `∂²_K bsV` with `e^{-rT} · PDF(K)`. -/

/-- **PDF non-negativity as a corollary of strike convexity**, the sign of the density derived
from the convexity of the payoff.

The derivation chain made explicit:

1. `bsV_strike_convexOn`: the BS call *price* is convex in K on `(0, ∞)`.
2. `deriv_deriv_nonneg_of_convexOn`: so `0 ≤ ∂²_K bsV` there, since its strike
   derivative is monotone (`ConvexOn.monotoneOn_deriv`).
3. `breedenLitzenberger`: `∂²_K bsV = e^{-rT} · PDF`.
4. So `0 ≤ e^{-rT} · PDF`. Dividing by positive `e^{-rT}` gives the result.

The complementary `lognormalTerminalPDF_nonneg` proof above is shorter
(direct gaussian-PDF positivity); this proof takes the sign from
`bsV`-convexity. `bsV_strike_convexOn` comes from the convexity of the
payoff integrated against the standard normal law (`convexOn_integral_call`,
`bs_call_formula`), not from the sign of the closed form. The positivity of that
law still enters: `bs_call_formula` evaluates the Gaussian integral through
Mathlib's `integral_gaussianReal_eq_integral_smul`, which uses `ϕ ≥ 0`
(`toReal_gaussianPDF`), the fact the direct proof uses. So the two routes share
their root; this one explains the sign rather than reading it off the formula. -/
theorem lognormalTerminalPDF_nonneg_via_strike_convexity
    {S_0 r σ T K : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    0 ≤ lognormalTerminalPDF S_0 r σ T K := by
  have h := deriv_deriv_nonneg_of_convexOn (bsV_strike_convexOn (r := r) hS₀ hσ hT) isOpen_Ioi
    (fun _ hk ↦ (hasDerivAt_bsV_K hS₀ hσ hk hT).differentiableAt) (Set.mem_Ioi.mpr hK)
  rw [(breedenLitzenberger hS₀ hσ hK hT).deriv] at h
  exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp h

/-! ## Change of variables to standard normal (folded from `LognormalCOV.lean`)

The implied PDF and the standard-normal PDF are related by the substitution
`K ↦ z = −bsd2(K)`, whose Jacobian is `dz/dK = −1/(K σ √T)`. The
differential identity below packages this.

The integration-to-1 claim is `lintegral_lognormalTerminalPDF_eq_one`
(`JumpDiffusionDigital.lean`), the mass of the law of the price, through the
measure-level change of variables `y ↦ Seʸ` (`map_mul_exp_withDensity`); this file
states only the differential. -/

/-- **Differential change-of-variables identity** between the lognormal PDF
of `S_T` and the standard-normal PDF:
`f(K) · K · σ · √T = ϕ(bsd2(K))`. -/
theorem lognormalTerminalPDF_change_of_variables
    {S_0 r σ T K : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    lognormalTerminalPDF S_0 r σ T K * (K * σ * Real.sqrt T) =
      gaussianPDFReal 0 1 (bsd2 S_0 K r σ T) := by
  unfold lognormalTerminalPDF
  have hsqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_den_ne : K * σ * Real.sqrt T ≠ 0 :=
    (mul_pos (mul_pos hK hσ) hsqrtT_pos).ne'
  field_simp

end MathFin
