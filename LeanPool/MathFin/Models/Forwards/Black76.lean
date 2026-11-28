/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.GarmanNormalForm

/-!
# Black-76 formula for options on futures

The **Black formula** (Black 1976) prices European options on futures
contracts. Under the risk-neutral measure, the futures price is a
martingale (zero drift), so

    F_T = F · exp(-σ²T/2 + σ √T · Z),   Z ~ N(0, 1).

The European call payoff `max(F_T − K, 0)` discounted gives

    V_Black = e^{−rT} · [F · Φ(d_1) − K · Φ(d_2)],

where `d_1 = (log(F/K) + σ²T/2) / (σ √T)` and `d_2 = d_1 − σ √T`.

This is identical to `bs_call_formula` specialized to `r = 0` in the
BS-drift, then post-discounted by `e^{-rT}` (the discount-rate is now
**independent** of the underlying's drift). The proof is therefore a
direct algebraic specialization.

## Main definitions

* `blackPayerSwaption`: `A · [F Φ(d₁) − K Φ(d₂)]` with `d_i = bsd_i F K 0 σ T`.
* `blackReceiverSwaption`: `A · [K Φ(−d₂) − F Φ(−d₁)]`.
* `blackCaplet`: `α · [F Φ(d₁) − K Φ(d₂)]`, the accrual-scaled Black-76 call on the forward
  rate `F`.
* `blackFloorlet`: `α · [K Φ(−d₂) − F Φ(−d₁)]`, the put counterpart.

## Main results

* `black_futures_formula`: under `BSCallHyp Q F K 0 σ T Z`, the discounted expected futures-call
  payoff is `e^{−rT}(F Φ(d₁) − K Φ(d₂))`.
* `black_futures_price_eq_bsVGarman`: that price is an instance of `bsVGarman`.
* `black_futures_formula_atm`: at `K = F` it equals `e^{−rT} F (2Φ(σ√T/2) − 1)`.
* `swaption_payer_receiver_parity`: `blackPayerSwaption − blackReceiverSwaption = A (F − K)`.
* `caplet_floorlet_parity`: `blackCaplet − blackFloorlet = α (F − K)`.
* `blackPayerSwaption_eq_bsVGarman`: for `A > 0`, the payer swaption is `bsVGarman (F·A) K A σ T`.
* `blackCaplet_eq_blackPayerSwaption`, `blackFloorlet_eq_blackReceiverSwaption`: the caplet and
  floorlet are the payer and receiver swaption with the accrual `α` in place of the annuity.

## References

* [F. Black, *The pricing of commodity contracts*][Black1976]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 18.7; 29.2

## Tags

Black-76, Black formula, options on futures, futures option pricing, lognormal futures,
European call on futures, MSC 91G20, JEL G13, JEL Q02
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- **Black-76 formula** for European call options on futures.

Given the risk-neutral hypothesis `BSCallHyp Q F K 0 σ T Z` (i.e., the futures
price has zero drift under `Q`), the discounted expected payoff under an
**independent** discount rate `r` is

    e^{-rT} · [F · Φ(d_1) − K · Φ(d_2)],

where `d_i = bsdi F K 0 σ T`.

Real derivation: applies `bs_call_formula` with `r = 0` (no
intra-formula discounting) and multiplies through by the external
discount factor `e^{-rT}`. -/
theorem black_futures_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {F K σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q F K 0 σ T Z) (r : ℝ) :
    ∫ ω, Real.exp (-r * T) * max (bsTerminal F 0 σ T (Z ω) - K) 0 ∂Q
      = Real.exp (-r * T) *
          (F * Phi (bsd1 F K 0 σ T) - K * Phi (bsd2 F K 0 σ T)) := by
  rw [integral_const_mul]
  have h_bs := bs_call_formula h
  -- Specialize r=0 in bs_call_formula
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, mul_one] at h_bs
  -- h_bs : ∫ ω, max (bsTerminal F 0 σ T (Z ω) - K) 0 ∂Q
  --        = F * Phi (bsd1 F K 0 σ T) - K * Phi (bsd2 F K 0 σ T)
  rw [h_bs]

/-- **Black-76 price is a Garman-normal-form instance**: the discounted
expected futures-call payoff equals `bsVGarman` at `A = F · e^{−rT}`,
`DF = e^{−rT}` — the forward numéraire. Routes `black_futures_formula`
through `Models/BlackScholes/GarmanNormalForm`'s `black76_RHS_eq_bsVGarman`, making
the "Black-76 is the same formula as standard BS" unification load-bearing
from the consumer side. -/
theorem black_futures_price_eq_bsVGarman {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {F K σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q F K 0 σ T Z) (r : ℝ) :
    ∫ ω, Real.exp (-r * T) * max (bsTerminal F 0 σ T (Z ω) - K) 0 ∂Q
      = bsVGarman (F * Real.exp (-(r * T))) K (Real.exp (-(r * T))) σ T := by
  rw [black_futures_formula h r, neg_mul]
  exact black76_RHS_eq_bsVGarman F K r σ T h.S_0_pos h.K_pos

/-- **The at-the-money Black-76 call**: at strike `K = F`, `d₁ = σ√T/2 = −d₂`, so the
discounted expected futures-call payoff is `e^{−rT} · F · (2Φ(σ√T/2) − 1)`. Derived from
`black_futures_formula` and `Φ(x) + Φ(−x) = 1`. -/
theorem black_futures_formula_atm {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {F σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q F F 0 σ T Z) (r : ℝ) :
    ∫ ω, Real.exp (-r * T) * max (bsTerminal F 0 σ T (Z ω) - F) 0 ∂Q
      = Real.exp (-r * T) * F * (2 * Phi (σ * Real.sqrt T / 2) - 1) := by
  have hd1 : bsd1 F F 0 σ T = σ * Real.sqrt T / 2 := by
    have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr h.T_pos).ne'
    rw [bsd1, div_self h.S_0_pos.ne', Real.log_one, div_eq_iff (mul_ne_zero h.σ_pos.ne' hs)]
    linear_combination (-(σ ^ 2) / 2) * Real.mul_self_sqrt h.T_pos.le
  have hd2 : bsd2 F F 0 σ T = -(σ * Real.sqrt T / 2) := by rw [bsd2, hd1]; ring
  rw [black_futures_formula h r, hd2, hd1]
  linear_combination (-(Real.exp (-r * T) * F)) * Phi_add_Phi_neg (σ * Real.sqrt T / 2)

/-! ## Black model for swaptions (folded from `Swaption.lean`)

A swaption with strike `K`, forward swap rate `F`, annuity `A`, vol `σ`,
expiry `T` prices via the Black-76 formula scaled by the annuity numéraire.

Payer-receiver parity `V^payer − V^receiver = A · (F − K)` is the swap-rate
analog of put-call parity, with the same one-line proof via `Φ` symmetry. -/

/-- **Payer swaption price under the Black model**: `A · [F · Φ(d_1) − K · Φ(d_2)]`. -/
noncomputable def blackPayerSwaption (A F K σ T : ℝ) : ℝ :=
  A * (F * Phi (bsd1 F K 0 σ T) - K * Phi (bsd2 F K 0 σ T))

/-- **Receiver swaption price under the Black model**:
`A · [K · Φ(−d_2) − F · Φ(−d_1)]`. -/
noncomputable def blackReceiverSwaption (A F K σ T : ℝ) : ℝ :=
  A * (K * Phi (-(bsd2 F K 0 σ T)) - F * Phi (-(bsd1 F K 0 σ T)))

/-- **Payer-receiver swaption parity**: `V^payer − V^receiver = A · (F − K)`.
The same `Phi`-symmetry proof as put-call parity, scaled by the annuity. -/
theorem swaption_payer_receiver_parity (A F K σ T : ℝ) :
    blackPayerSwaption A F K σ T - blackReceiverSwaption A F K σ T =
      A * (F - K) := by
  unfold blackPayerSwaption blackReceiverSwaption
  have h_d1 := Phi_add_Phi_neg (bsd1 F K 0 σ T)
  have h_d2 := Phi_add_Phi_neg (bsd2 F K 0 σ T)
  linear_combination A * F * h_d1 - A * K * h_d2

/-- **The payer swaption is a Garman normal form**: `blackPayerSwaption A F K σ T
= bsVGarman (F·A) K A σ T`, the annuity `A` in the discount-factor slot and
`F·A` the asset. Makes explicit that `GarmanNormalForm`'s docstring earmark for
the swaption is a genuine instance (`A_annuity·F` asset, `A_annuity` discount),
so the payer/receiver parity above is the Garman-level parity in disguise. -/
theorem blackPayerSwaption_eq_bsVGarman (A F K σ T : ℝ) (hA : 0 < A) :
    blackPayerSwaption A F K σ T = bsVGarman (F * A) K A σ T := by
  have hd1 : bsd1 F K 0 σ T = gbsd1 (F * A) K A σ T := by
    unfold bsd1 gbsd1
    rw [mul_div_mul_right F K hA.ne']
    ring_nf
  have hd2 : bsd2 F K 0 σ T = gbsd2 (F * A) K A σ T := by
    unfold bsd2 gbsd2; rw [hd1]
  unfold blackPayerSwaption bsVGarman
  rw [hd1, hd2]; ring

/-! ## Black-76 caplet and floorlet

A **caplet** is a European call on a forward rate, scaled by the accrual factor
`α` over the accrual period; a **floorlet** is its put counterpart. Both follow
the same no-separate-discount convention as the swaption above — the forward
numéraire absorbs the drift, so the discount does not appear in the formula.

Written out, the caplet is `α · [F Φ(d₁) − K Φ(d₂)]`, which is the payer
swaption's formula with the accrual factor sitting in the annuity slot. That is
not a coincidence worth hiding: `blackCaplet_eq_blackPayerSwaption` records it,
and caplet-floorlet parity is then the payer-receiver parity already proved
above, applied. -/

/-- **Black-76 caplet price**: `α · [F Φ(d₁) − K Φ(d₂)]`, the accrual-scaled
Black-76 call on the forward rate `F`, with `d_i = bsd_i F K 0 σ T`. -/
noncomputable def blackCaplet (F K σ T α : ℝ) : ℝ :=
  α * (F * Phi (bsd1 F K 0 σ T) - K * Phi (bsd2 F K 0 σ T))

/-- **Black-76 floorlet price**: `α · [K Φ(−d₂) − F Φ(−d₁)]`, the put counterpart
of `blackCaplet`. -/
noncomputable def blackFloorlet (F K σ T α : ℝ) : ℝ :=
  α * (K * Phi (-(bsd2 F K 0 σ T)) - F * Phi (-(bsd1 F K 0 σ T)))

/-- **The caplet is a payer swaption in disguise**: same Black-76 shape, with the
accrual factor `α` where the swaption carries its annuity `A`. The two
instruments differ in their numéraire story, not in their formula. -/
theorem blackCaplet_eq_blackPayerSwaption (F K σ T α : ℝ) :
    blackCaplet F K σ T α = blackPayerSwaption α F K σ T := rfl

/-- **The floorlet is a receiver swaption in disguise**, by the same reading. -/
theorem blackFloorlet_eq_blackReceiverSwaption (F K σ T α : ℝ) :
    blackFloorlet F K σ T α = blackReceiverSwaption α F K σ T := rfl

/-- **Caplet-floorlet parity**: `V^caplet − V^floorlet = α · (F − K)`, the
forward-rate analogue of put-call parity. Given the structural identity above it
*is* payer-receiver parity, so it is that theorem applied rather than the same
`Phi`-symmetry argument run a second time. -/
theorem caplet_floorlet_parity (F K σ T α : ℝ) :
    blackCaplet F K σ T α - blackFloorlet F K σ T α = α * (F - K) :=
  swaption_payer_receiver_parity α F K σ T

end MathFin
