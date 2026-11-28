/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.ZCB

-- pointers: MathFin/Models/Rates/ZCB.lean
-- main-module: MathFin/Models/Rates/InterestRateSwap.lean
-- benchmark: benchmarks/mathematical_finance.json
-- benchmark-id: mf-fixedincome-swap
-- source-issue: 66
-- new-defs: annuity, payerSwapValue, parSwapRate

/-!
# Vanilla interest-rate swap

The annuity, the payer-swap value, the par swap
rate, and the par identity — the swap is worth zero iff the fixed rate is the
par rate. The identity is pure annuity algebra, proved for any nonzero annuity
and instantiated on the `zcb` curve, where positivity of the discount factors
is a theorem (`zcb_pos`), not an assumption. The annuity here is the numéraire
`A` consumed by `blackPayerSwaption` in `MathFin/Models/Forwards/Black76.lean`.

## Main definitions

* `annuity`: the fixed-leg PV01 `A = δ · ∑ i ∈ s, P i` of a payment schedule `s` with daycount
  fraction `δ`.
* `payerSwapValue`: the payer-swap value, the floating leg `P₀ − Pₙ` minus the fixed leg `K · A`.
* `parSwapRate`: the par swap rate `S = (P₀ − Pₙ) / A`.

## Main results

* `annuity_pos`: the annuity of a nonempty schedule with positive daycount and positive discount
  factors is positive.
* `payerSwapValue_eq_zero_iff`: for a nonzero annuity `A`, the payer swap is worth zero iff
  `K = parSwapRate P0 Pn A`.
* `payerSwapValue_zcb_eq_zero_iff`: the same par identity on the `zcb` curve, for `δ > 0` and a
  nonempty schedule.

## Tags

interest rate swap, par swap rate, payer swap, annuity factor, swap valuation, fixed leg, MSC 91G30,
JEL G13
-/


@[expose] public section

namespace MathFin

/-- Annuity (fixed-leg PV01) of a payment schedule `s` with daycount fraction
`δ` and discount factors `P`: `A = δ · ∑ i ∈ s, P i`. -/
def annuity {ι : Type*} (δ : ℝ) (P : ι → ℝ) (s : Finset ι) : ℝ := δ * ∑ i ∈ s, P i

/-- Payer-swap value over given discount factors: the floating leg `P₀ − Pₙ`
minus the fixed leg `K · A`, `A` the annuity of the fixed schedule. -/
def payerSwapValue (P0 Pn K A : ℝ) : ℝ := P0 - Pn - K * A

/-- Par swap rate: the fixed rate that makes the payer swap worth zero,
`S = (P₀ − Pₙ) / A`. -/
noncomputable def parSwapRate (P0 Pn A : ℝ) : ℝ := (P0 - Pn) / A

/-- The annuity of a nonempty schedule with positive daycount and positive
discount factors is positive. -/
theorem annuity_pos {ι : Type*} {δ : ℝ} {P : ι → ℝ} {s : Finset ι} (hδ : 0 < δ)
    (hP : ∀ i ∈ s, 0 < P i) (hs : s.Nonempty) : 0 < annuity δ P s :=
  mul_pos hδ (Finset.sum_pos hP hs)

/-- **The par identity**: a payer swap is worth zero iff its fixed rate is the
par swap rate — pure algebra, valid for any nonzero annuity. -/
theorem payerSwapValue_eq_zero_iff (P0 Pn K : ℝ) {A : ℝ} (hA : A ≠ 0) :
    payerSwapValue P0 Pn K A = 0 ↔ K = parSwapRate P0 Pn A := by
  change P0 - Pn - K * A = 0 ↔ K = (P0 - Pn) / A
  rw [sub_eq_zero, eq_div_iff hA]
  exact eq_comm

/-- The par identity on the `zcb` curve: a positive daycount and a nonempty
payment schedule make the annuity positive (`zcb` is a positive exponential),
so no positivity hypotheses are needed. -/
theorem payerSwapValue_zcb_eq_zero_iff {ι : Type*} (r δ K T0 Tn : ℝ) (T : ι → ℝ)
    (s : Finset ι) (hδ : 0 < δ) (hs : s.Nonempty) :
    payerSwapValue (zcb r 0 T0) (zcb r 0 Tn) K (annuity δ (fun i ↦ zcb r 0 (T i)) s) = 0 ↔
      K = parSwapRate (zcb r 0 T0) (zcb r 0 Tn) (annuity δ (fun i ↦ zcb r 0 (T i)) s) :=
  payerSwapValue_eq_zero_iff _ _ _
    (annuity_pos hδ (fun i _ ↦ zcb_pos r 0 (T i)) hs).ne'

end MathFin
