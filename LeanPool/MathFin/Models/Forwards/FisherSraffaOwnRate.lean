/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.NoArbitrageDerivations

/-!
# Fisher/Sraffa own-rate-of-interest identity

A commodity's **own rate of interest** `b` (Keynes, *General Theory* ch. 17;
Sraffa 1932) is the real return of holding and lending the commodity itself.
Fisher's exact identity relates `b` to the rate of change `i` of the commodity's
money price (the inflation rate, for the composite consumption good) and the
resulting **money (nominal) rate** `r`:

  `1 + r = (1 + b)(1 + i)`,

and **Sraffa's implied own rate** is defined from a spot price `S`, forward
price `F`, financing rate `m` and maturity `T` as

  `b = ((1 + m)^T · S / F)^{1/T} − 1`;

`sraffaOwnRate_spec` shows that this `b` solves the cost-of-carry equation
`(1 + b)^T = (1 + m)^T · S / F`. Conversely, `sraffaOwnRate_eq_of_no_arbitrage` derives
the forward from the library's no-arbitrage forward (`forward_price_from_no_arbitrage`,
`Pricing/NoArbitrageDerivations.lean`) and shows that Sraffa's formula returns the own
rate: in a finite-state market whose discount factor is `(1 + m)^{−T}` and in which a unit of
the commodity lent today returns `(1 + b)^T` units at `T` (priced at the spot `S₀`), the
zero-value forward `F` satisfies `sraffaOwnRate m S₀ F T = b`.

Expanding the Fisher identity gives the familiar linear approximation
`r ≈ b + i`; its error term is exactly `b · i` — the identity is an exact
equality for real numbers, so the "approximation" enters only when `b · i`
is treated as second-order-small and dropped.

## Main definitions

* `fisherMoneyRate`: the money rate `(1 + b)(1 + i) - 1` from an own rate `b` and a price-change
  rate `i`.
* `sraffaOwnRate`: Sraffa's implied own rate `((1 + m)^T * S / F)^(1/T) - 1` from the financing
  rate `m`, spot `S`, forward `F` and maturity `T`.

## Main results

* `fisher_linear_approx_error`: `fisherMoneyRate b i − (b + i) = b * i`, the
  exact statement underlying `r ≈ b + i` for small `b, i`.
* `sraffaOwnRate_spec`: `(1 + sraffaOwnRate m S F T)^T = (1+m)^T · S / F`
  for `T ≠ 0` and `(1+m)^T · S / F ≥ 0`, the defining equation Sraffa's formula
  inverts.
* `sraffaOwnRate_eq_of_no_arbitrage`: Sraffa's formula applied to the no-arbitrage
  forward of a commodity with own rate `b` returns `b`.
* `fisherMoneyRate_sraffaOwnRate_one`: over one period, Fisher's identity holds with the
  own rate implied by Sraffa's formula and the forward premium `F/S − 1` as the rate of
  change of the money price: `fisherMoneyRate (sraffaOwnRate m S F 1) (F/S − 1) = m`.

## References

* [J. M. Keynes, *The General Theory of Employment, Interest and Money*][Keynes1936], ch. 17
* [P. Sraffa, *Dr.~Hayek on money and capital*][Sraffa1932]

## Tags

own rate of interest, Fisher equation, Sraffa, Keynes, cost of carry, forward price, MSC 91G30,
JEL E43, JEL Q02
-/

@[expose] public section

namespace MathFin

/-! ### Fisher's exact identity -/

/-- **Fisher money (nominal) rate**: `r = (1+b)(1+i) − 1`, exactly solving
`1 + r = (1+b)(1+i)` for the nominal rate `r` given a commodity's own rate of
interest `b` and the rate of change `i` of its money price. -/
noncomputable def fisherMoneyRate (b i : ℝ) : ℝ := (1 + b) * (1 + i) - 1

/-- **Linear approximation error**: `r − (b+i) = b·i` exactly. The usual
first-order approximation `r ≈ b + i` drops this cross term, which is
genuinely second-order small when `b, i` are both small. -/
theorem fisher_linear_approx_error (b i : ℝ) :
    fisherMoneyRate b i - (b + i) = b * i := by
  unfold fisherMoneyRate; ring

/-! ### Sraffa's implied own rate -/

/-- **Sraffa's implied own rate**: `b = ((1+m)^T · S/F)^{1/T} − 1`, from the
financing rate `m`, spot price `S`, forward price `F` and maturity `T`: the
cost-of-carry relation `F = S·(1+m)^T / (1+b)^T` solved for `b`. -/
noncomputable def sraffaOwnRate (m S F T : ℝ) : ℝ :=
  ((1 + m) ^ T * (S / F)) ^ (1 / T) - 1

/-- **Sraffa's defining equation**: `(1 + b)^T = (1+m)^T · S/F`, where
`b = sraffaOwnRate m S F T`. Requires `(1+m)^T · S/F ≥ 0` (holds e.g. for
`m ≥ -1`, `S, F > 0`) and `T ≠ 0` so the `1/T`-th root inverts the `T`-th
power. -/
theorem sraffaOwnRate_spec (m S F T : ℝ) (hT : T ≠ 0)
    (hpos : 0 ≤ (1 + m) ^ T * (S / F)) :
    (1 + sraffaOwnRate m S F T) ^ T = (1 + m) ^ T * (S / F) := by
  unfold sraffaOwnRate
  have h1 : 1 + (((1 + m) ^ T * (S / F)) ^ (1 / T) - 1)
      = ((1 + m) ^ T * (S / F)) ^ (1 / T) := by ring
  rw [h1, ← Real.rpow_mul hpos, one_div, inv_mul_cancel₀ hT, Real.rpow_one]

/-! ### Sraffa's own rate from the no-arbitrage forward -/

/-- **Sraffa's formula returns the own rate of the no-arbitrage forward.** In a finite-state
market with state prices `q`, discount factor `∑ q = (1 + m)^{−T}` (money rate `m`), and a
commodity whose loan in kind earns the own rate `b` — the claim on `(1 + b)^T` units at `T`
is priced at the spot `S₀`, `∑ q·(1 + b)^T·S_T = S₀` — the forward with zero value at strike
`F` (`∑ q·(S_T − F) = 0`) satisfies `sraffaOwnRate m S₀ F T = b`. The forward is the
library's `forward_price_from_no_arbitrage` applied to the in-kind claim:
`(1 + b)^T · F = S₀ · (1 + m)^T`. -/
theorem sraffaOwnRate_eq_of_no_arbitrage {ι : Type*} (s : Finset ι) (q S : ι → ℝ)
    (m b S₀ F T : ℝ) (hm : 0 < 1 + m) (hb : 0 < 1 + b) (hT : T ≠ 0) (hS₀ : 0 < S₀)
    (h_bond : ∑ i ∈ s, q i = (1 + m) ^ (-T))
    (h_own : ∑ i ∈ s, q i * ((1 + b) ^ T * S i) = S₀)
    (h_fwd : ∑ i ∈ s, q i * (S i - F) = 0) :
    sraffaOwnRate m S₀ F T = b := by
  have h0 : ∑ i ∈ s, q i * ((1 + b) ^ T * S i - (1 + b) ^ T * F) = 0 := by
    rw [← mul_zero ((1 + b) ^ T), ← h_fwd, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hF' := (forward_price_from_no_arbitrage s q (fun i ↦ (1 + b) ^ T * S i)
    ((1 + m) ^ (-T)) S₀ ((1 + b) ^ T * F) (Real.rpow_pos_of_pos hm _).ne' h_bond h_own).mp h0
  rw [Real.rpow_neg hm.le, div_inv_eq_mul] at hF'
  have hF0 : F ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hF'
    exact (mul_pos hS₀ (Real.rpow_pos_of_pos hm T)).ne' hF'.symm
  have key : (1 + m) ^ T * (S₀ / F) = (1 + b) ^ T := by
    rw [mul_div_assoc', div_eq_iff hF0]
    linear_combination -1 * hF'
  rw [sraffaOwnRate, key, ← Real.rpow_mul hb.le, mul_one_div_cancel hT, Real.rpow_one,
    add_sub_cancel_left]

/-- **Fisher's identity at Sraffa's own rate.** Over one period, the money rate `m`
decomposes by Fisher's identity into the own rate implied by Sraffa's formula and the
forward premium `F/S − 1` (the rate of change of the commodity's money price read off the
forward): `fisherMoneyRate (sraffaOwnRate m S F 1) (F/S − 1) = m`, for `S, F ≠ 0`. -/
theorem fisherMoneyRate_sraffaOwnRate_one (m S F : ℝ) (hS : S ≠ 0) (hF : F ≠ 0) :
    fisherMoneyRate (sraffaOwnRate m S F 1) (F / S - 1) = m := by
  have h : (1 + m) * (S / F) * (F / S) = 1 + m := by field_simp
  simp only [fisherMoneyRate, sraffaOwnRate, Real.rpow_one, div_one]
  linear_combination h

end MathFin
