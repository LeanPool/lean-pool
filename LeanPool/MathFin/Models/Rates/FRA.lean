/-
Copyright (c) 2026 Aleksey Salkutsan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksey Salkutsan
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.ZCB

-- pointers: MathFin/Models/Rates/ZCB.lean
-- main-module: MathFin/Models/Rates/FRA.lean
-- benchmark: benchmarks/mathematical_finance.json
-- benchmark-id: mf-fixedincome-fra
-- source-issue: 67
-- new-defs: fraForwardRate, fraValue

/-!
# Forward-rate agreement

The simple forward rate over one accrual period is

`F = (P(0,T₁) / P(0,T₂) - 1) / δ`,

and the time-zero value of the corresponding forward-rate agreement is

`V = δ * P(0,T₂) * (F - K)`.

## Main definitions

* `fraForwardRate`: the simple forward rate implied by discount factors `P₁`, `P₂` over an accrual
  period of length `δ`.
* `fraValue`: the time-zero value of a forward-rate agreement.

## Main results

* `fraValue_forwardRate_eq_discount_difference` expands the FRA value to
  `P(0,T₁) - P(0,T₂) - δ * P(0,T₂) * K`.
* `fraValue_zcb_eq_discount_difference` instantiates that identity on the
  library's zero-coupon-bond curve.
* `fraValue_zcb_eq_zero_iff` proves that the FRA has zero value exactly at the
  simple forward rate, with denominator nonvanishing derived from `zcb_pos`.

## Tags

forward rate agreement, simple forward rate, FRA value, discount factor, zero-coupon curve,
MSC 91G30, JEL G13
-/


@[expose] public section

namespace MathFin

/-- Simple forward rate implied by discount factors `P₁`, `P₂` over an accrual
period of length `δ`. -/
noncomputable def fraForwardRate (P1 P2 δ : ℝ) : ℝ := (P1 / P2 - 1) / δ

/-- Time-zero value of a forward-rate agreement. -/
def fraValue (δ P2 F K : ℝ) : ℝ := δ * P2 * (F - K)

/-- Substituting the simple forward rate into the FRA value gives the
discount-factor difference net of the fixed payment. -/
theorem fraValue_forwardRate_eq_discount_difference (P1 P2 δ K : ℝ)
    (hδ : δ ≠ 0) (hP2 : P2 ≠ 0) :
    fraValue δ P2 (fraForwardRate P1 P2 δ) K = P1 - P2 - δ * P2 * K := by
  unfold fraValue fraForwardRate
  field_simp

/-- The FRA value identity on the deterministic zero-coupon-bond curve. -/
theorem fraValue_zcb_eq_discount_difference (r δ K T1 T2 : ℝ) (hδ : δ ≠ 0) :
    fraValue δ (zcb r 0 T2) (fraForwardRate (zcb r 0 T1) (zcb r 0 T2) δ) K =
      zcb r 0 T1 - zcb r 0 T2 - δ * zcb r 0 T2 * K :=
  fraValue_forwardRate_eq_discount_difference _ _ _ _ hδ (zcb_pos r 0 T2).ne'

/-- On the zero-coupon-bond curve, the FRA has zero value exactly when its
fixed rate is the simple forward rate. -/
theorem fraValue_zcb_eq_zero_iff (r δ K T1 T2 : ℝ) (hδ : δ ≠ 0) :
    fraValue δ (zcb r 0 T2) (fraForwardRate (zcb r 0 T1) (zcb r 0 T2) δ) K = 0 ↔
      K = fraForwardRate (zcb r 0 T1) (zcb r 0 T2) δ := by
  unfold fraValue
  have hscale : δ * zcb r 0 T2 ≠ 0 := mul_ne_zero hδ (zcb_pos r 0 T2).ne'
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact (hscale h).elim
    · exact (sub_eq_zero.mp h).symm
  · intro h
    rw [h, sub_self, mul_zero]

end MathFin
