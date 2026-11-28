/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.Value
public import LeanPool.MathFin.Models.Rates.MacaulayModified
public import LeanPool.MathFin.Models.Rates.CouponBonds
public import LeanPool.MathFin.Models.Rates.InterestRateSwap
public import LeanPool.MathFin.Models.Rates.FRA

/-!
# Bonds and swaps on a deterministic curve

On a deterministic discount curve the library's fixed-income closed forms are the values of
contracts. A coupon bond is a schedule of fixed cash flows (`fixedFlows`,
`Contracts/Instruments/FixedIncome.lean`), and in every model it is worth the sum of its
discounted flows (`value_fixedFlows_deterministic`):

* discounted at a yield `y`, with integer payment times, it is `bondPriceDisc`
  (`pathPV_fixedFlows_yieldDiscount`), the price the durations and convexities of
  `Models/Rates/` are taken of;
* `n` level payments on a grid of step `Δt`, discounted on the flat continuous curve `zcb r 0`,
  are `annuityValue` (`pathPV_fixedFlows_zcb`).

A swap on the curve `P` exchanges a fixed leg, `δK` at each payment date, for a floating leg that
pays the simple forward rate the curve implies for each accrual period,
`δ · fraForwardRate (P Tᵢ) (P Tᵢ₊₁) δ` at `Tᵢ₊₁`. The floating coupons are fixed by the curve,
which is what makes this the deterministic-rates model, where a floating rate is known in advance.
The floating leg telescopes to `P(T₀) − P(Tₙ)` (`pathPV_floatingLeg`), the fixed leg is `K` times
the annuity (`pathPV_fixedLeg`), so the payer swap is worth `payerSwapValue` (`value_payerSwap`),
and it is worth zero exactly at the par rate (`value_payerSwap_eq_zero_iff`). With one accrual
period the swap is a forward-rate agreement, worth `fraValue` (`value_payerSwap_one_eq_fraValue`).
With a stochastic discount the same contracts are priced in `Models/Rates/ShortRate.lean`.

## Main definitions

* `yieldDiscount` — discounting at a yield with annual compounding.
* `floatingLeg`, `fixedLeg`, `payerSwap` — the legs of a swap on a deterministic curve.

## Main results

* `pathPV_fixedFlows_yieldDiscount`, `pathPV_fixedFlows_zcb` — bonds and annuities.
* `pathPV_floatingLeg`, `pathPV_fixedLeg`, `value_payerSwap`, `value_payerSwap_eq_zero_iff`,
  `value_payerSwap_one_eq_fraValue` — swaps and FRAs.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026], the contract layer these values
  are read through
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  Section 1.5
* [Fabozzi, *Bond Markets, Analysis and Strategies*][FabozziBMAS], ch. 2
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 7

## Tags

coupon bond, interest rate swap, par swap rate, forward rate agreement, annuity, floating leg,
deterministic curve, MSC 91G30, JEL E43, JEL G12
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Discounting at a yield `y` with annual compounding, `(1 + y)^{−τ}`; a discount factor for
`1 + y > 0`. -/
noncomputable def yieldDiscount (y : ℝ) : ℝ≥0 → ℝ := fun τ ↦ (1 + y) ^ (-(τ : ℝ))

/-- **A coupon bond at a yield is `bondPriceDisc`.** Discounted at the yield `y`, cash flows
`c i` at integer times `t i` are worth `∑ cᵢ / (1 + y)^{tᵢ}`. -/
theorem pathPV_fixedFlows_yieldDiscount {y : ℝ} (hy : 0 ≤ 1 + y) (s : Scenario ι) (t : ℕ → ℕ)
    (c : ℕ → ℝ) (n : ℕ) :
    (fixedFlows (fun i ↦ (t i : ℝ≥0)) c n : Contract ι).pathPV (yieldDiscount y) s
      = bondPriceDisc (Finset.range n) t c y := by
  rw [pathPV_fixedFlows, bondPriceDisc]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [yieldDiscount, NNReal.coe_natCast, Real.rpow_neg hy, Real.rpow_natCast, div_eq_inv_mul]

/-- **Level payments on the flat continuous curve are `annuityValue`.** `n` payments of `c` at
`Δt, 2Δt, …, nΔt`, discounted by `zcb r 0`, are worth `∑ c e^{−r(i+1)Δt}`. -/
theorem pathPV_fixedFlows_zcb (s : Scenario ι) (n : ℕ) (c r : ℝ) (Δt : ℝ≥0) :
    (fixedFlows (fun i ↦ (i + 1 : ℝ≥0) * Δt) (fun _ ↦ c) n : Contract ι).pathPV
        (fun τ ↦ zcb r 0 τ) s = annuityValue n c r Δt := by
  rw [pathPV_fixedFlows, annuityValue]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [zcb, sub_zero, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  ring

variable (P : ℝ≥0 → ℝ) (T : ℕ → ℝ≥0) (δ : ℝ) (n : ℕ)

/-- The **floating leg** of a swap on the deterministic discount curve `P`, with payment dates
`T 1, …, T n` and accrual `δ`: at `T (i + 1)` it pays `δ` times the simple forward rate the curve
implies for `[T i, T (i + 1)]`. -/
noncomputable def floatingLeg : Contract ι :=
  fixedFlows (fun i ↦ T (i + 1)) (fun i ↦ δ * fraForwardRate (P (T i)) (P (T (i + 1))) δ) n

/-- The **fixed leg** of a swap with fixed rate `K`: `δK` at each of `T 1, …, T n`. -/
noncomputable def fixedLeg (K : ℝ) : Contract ι := fixedFlows (fun i ↦ T (i + 1)) (fun _ ↦ δ * K) n

/-- The **payer swap**: receive the floating leg, pay the fixed leg. -/
noncomputable def payerSwap (K : ℝ) : Contract ι :=
  .both (floatingLeg P T δ n) (.scale (-1) (fixedLeg T δ n K))

variable {P T δ}

/-- **The floating leg telescopes.** Discounted on its own curve, each forward-rate coupon is
worth `P(Tᵢ) − P(Tᵢ₊₁)`, so the leg is worth `P(T₀) − P(Tₙ)`. -/
theorem pathPV_floatingLeg (hδ : δ ≠ 0) (hP : ∀ i, P (T i) ≠ 0) (s : Scenario ι) :
    (floatingLeg P T δ n : Contract ι).pathPV P s = P (T 0) - P (T n) := by
  rw [floatingLeg, pathPV_fixedFlows]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, fraForwardRate]
    field_simp [hP (n + 1)]
    ring

/-- The fixed leg is worth `K` times the annuity of its payment dates. -/
theorem pathPV_fixedLeg (K : ℝ) (s : Scenario ι) :
    (fixedLeg T δ n K : Contract ι).pathPV P s
      = K * annuity δ (fun i ↦ P (T (i + 1))) (Finset.range n) := by
  rw [fixedLeg, pathPV_fixedFlows, annuity, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **A payer swap on a deterministic curve is worth `payerSwapValue`** in every model: the
floating leg `P(T₀) − P(Tₙ)` less `K` times the annuity. -/
theorem value_payerSwap {Q : Measure Ω} [IsProbabilityMeasure Q] (X : ι → ℝ≥0 → Ω → ℝ)
    (hδ : δ ≠ 0) (hP : ∀ i, P (T i) ≠ 0) (K : ℝ) :
    (payerSwap P T δ n K : Contract ι).value Q (fun t _ ↦ P t) X
      = payerSwapValue (P (T 0)) (P (T n)) K (annuity δ (fun i ↦ P (T (i + 1))) (Finset.range n)) :=
  Contract.value_eq_of_pathPV_eq X fun _ ↦ by
    rw [payerSwap, Contract.pathPV_both, Contract.pathPV_scale, pathPV_floatingLeg n hδ hP,
      pathPV_fixedLeg, payerSwapValue]
    ring

/-- **A forward-rate agreement is a one-period payer swap.** With one accrual period `[T₀, T₁]`
the swap's floating coupon is the simple forward rate `fraForwardRate (P T₀) (P T₁) δ` and the
fixed coupon is `δK`, both paid at `T₁`; its value in every model is `fraValue`
(`Models/Rates/FRA.lean`): `δ · P(T₁) · (F − K)`. -/
theorem value_payerSwap_one_eq_fraValue {Q : Measure Ω} [IsProbabilityMeasure Q]
    (X : ι → ℝ≥0 → Ω → ℝ) (hδ : δ ≠ 0) (hP : ∀ i, P (T i) ≠ 0) (K : ℝ) :
    (payerSwap P T δ 1 K : Contract ι).value Q (fun t _ ↦ P t) X
      = fraValue δ (P (T 1)) (fraForwardRate (P (T 0)) (P (T 1)) δ) K := by
  rw [value_payerSwap 1 X hδ hP, fraValue_forwardRate_eq_discount_difference _ _ _ _ hδ (hP 1),
    payerSwapValue, annuity]
  simp only [Finset.sum_range_one, zero_add]
  ring

/-- **A payer swap is worth zero exactly at the par swap rate.** -/
theorem value_payerSwap_eq_zero_iff {Q : Measure Ω} [IsProbabilityMeasure Q]
    (X : ι → ℝ≥0 → Ω → ℝ) (hδ : δ ≠ 0) (hP : ∀ i, P (T i) ≠ 0)
    (hA : annuity δ (fun i ↦ P (T (i + 1))) (Finset.range n) ≠ 0) (K : ℝ) :
    (payerSwap P T δ n K : Contract ι).value Q (fun t _ ↦ P t) X = 0
      ↔ K = parSwapRate (P (T 0)) (P (T n))
        (annuity δ (fun i ↦ P (T (i + 1))) (Finset.range n)) := by
  rw [value_payerSwap n X hδ hP]
  exact payerSwapValue_eq_zero_iff _ _ _ hA

end MathFin.Contracts
