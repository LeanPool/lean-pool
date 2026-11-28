/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF

/-!
# Yield curve bootstrapping

Standard practitioner method to extract zero-coupon bond (ZCB) prices from a
sequence of coupon-bond prices at successive maturities.

Given a coupon bond paying coupon `c i` at time `T_i` for `i ∈ sprev` (the
earlier maturities) plus `c_last + F` at the new (longest) maturity `T_n`,
with observed price `P`, the new ZCB price `B_last` satisfies:

  `P = (∑_{i ∈ sprev} c i · B i) + (c_last + F) · B_last`,

so

  `B_last = (P − ∑_{i ∈ sprev} c i · B i) / (c_last + F)`,

provided `c_last + F ≠ 0`.

Applied recursively, starting from a single-period bond (where `sprev = ∅` and
`B_last = P / (c_last + F)`), this identity is how the discount curve is bootstrapped
from coupon-bond market data. Only the single steps are proved here; the recursion over
instruments is the search-based `boot` of `Models/Rates/Bootstrapping.lean`, where
`swapBootstrap_recovers_couponBondFactor` shows that bisection on a zero-value swap
recovers the factor named by `bootstrap_solve`.

## Main definitions

* `couponBondPricingEq`: the proposition `P = (∑ i ∈ sprev, c i * B i) + (c_last + F) * B_last`,
  the price of a coupon bond with previously known maturities `sprev` and one new maturity.

## Main results

* `bootstrap_solve`: from the pricing equation, recovers `B_last` as a
  closed-form ratio.
* `bootstrap_solve_first`: bootstrap base case for the first bond with empty
  previous schedule: `B_1 = P_1 / (c_1 + F)`.
* `bootstrap_solve_second`: bootstrap step for the second bond:
  `B_2 = (P_2 − c · B_1) / (c + F)`.
* `bootstrap_consistency`: the bootstrapped price, plugged back into the pricing
  equation, recovers the bond price.

## References

* [Fabozzi, *Fixed Income Mathematics*][FabozziFIM], Ch 9
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], Ch 4.6

## Tags

bootstrapping, zero-coupon bond, coupon bond, discount curve, yield curve construction, JEL E43,
MSC 91G30
-/

@[expose] public section

namespace MathFin

/-- Coupon-bond pricing equation expressed in terms of previously-known ZCB
prices `B : ι → ℝ` and the new ZCB `B_last`. -/
def couponBondPricingEq {ι : Type*} (sprev : Finset ι) (c B : ι → ℝ)
    (P c_last F B_last : ℝ) : Prop :=
  P = (∑ i ∈ sprev, c i * B i) + (c_last + F) * B_last

/-- **Bootstrap solve identity**: from the coupon-bond pricing equation, the
new ZCB price `B_last` is recovered as a closed-form ratio. -/
lemma bootstrap_solve {ι : Type*} (sprev : Finset ι) (c B : ι → ℝ)
    (P c_last F B_last : ℝ) (h : c_last + F ≠ 0)
    (hP : couponBondPricingEq sprev c B P c_last F B_last) :
    B_last = (P - ∑ i ∈ sprev, c i * B i) / (c_last + F) := by
  unfold couponBondPricingEq at hP
  field_simp
  linarith

/-- **First-bond bootstrap** (empty previous schedule): a single-period coupon
bond with cash flow `c_last + F` at maturity gives `B_last = P / (c_last + F)`. -/
lemma bootstrap_solve_first (P c_last F B_last : ℝ) (h : c_last + F ≠ 0)
    (hP : P = (c_last + F) * B_last) :
    B_last = P / (c_last + F) := by
  rw [hP]
  field_simp

/-- **Second-bond bootstrap step**: with one previous ZCB price `B_1` and a
two-period bond paying coupon `c` at both dates plus face `F` at the second,
`B_2 = (P − c · B_1) / (c + F)`. -/
lemma bootstrap_solve_second (P c F B_1 B_2 : ℝ) (h : c + F ≠ 0)
    (hP : P = c * B_1 + (c + F) * B_2) :
    B_2 = (P - c * B_1) / (c + F) := by
  rw [hP]
  field_simp
  ring

/-- **Recursive consistency**: the bootstrapped ZCB price, plugged back into
the pricing equation, recovers the original bond price. -/
lemma bootstrap_consistency {ι : Type*} (sprev : Finset ι) (c B : ι → ℝ)
    (P c_last F : ℝ) (h : c_last + F ≠ 0) :
    couponBondPricingEq sprev c B P c_last F
      ((P - ∑ i ∈ sprev, c i * B i) / (c_last + F)) := by
  unfold couponBondPricingEq
  field_simp
  ring

end MathFin
