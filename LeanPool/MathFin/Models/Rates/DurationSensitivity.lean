/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.MacaulayModified
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Duration as price sensitivity (first-principles derivation)

For a coupon bond with discrete-compounded yield `y` and cashflows `c_i` at
times `t_i ∈ ℕ`,

  `P(y) = Σ c_i / (1 + y)^{t_i}`.

The **modified duration** is `D_mod(y) = ModNum(y) / P(y)` where
`ModNum(y) = Σ t_i · c_i / (1 + y)^{t_i + 1}`.

The classical sensitivity identity states

  `dP/dy = -D_mod · P`,    equivalently    `P'(y) = -ModNum(y)`.

Pre-existing content in `Models.Rates.MacaulayModified` defines `bondPriceDisc`,
`macaulayNumerator`, `modifiedNumerator`, and proves the algebraic relation
`ModNum = MacNum / (1 + y)`. It does **not** derive duration as the price
derivative — the connection between duration and price sensitivity is
exactly the first-principles claim formalized here.

## Building blocks

* `hasDerivAt_coupon_term`: per-cashflow derivative
  `d/dy [c / (1+y)^n] = -n · c / (1+y)^(n+1)`.
* `hasDerivAt_bondPriceDisc`: sum over cashflows gives
  `dP/dy = -ModNum(y)`.
* `bondPriceDisc_deriv_eq_neg_modified_duration_times_price`: the
  duration-sensitivity identity in its usual form
  `P'(y) / P(y) = -D_mod(y)` (for `P(y) ≠ 0`).

## Main results

* `hasDerivAt_coupon_term`: `d/dy [c / (1+y)^n] = -n · c / (1+y)^(n+1)`.
* `hasDerivAt_bondPriceDisc`: for `1 + y ≠ 0`, the bond price `P(y) = Σ c_i / (1 + y)^{t_i}` has
  derivative `-ModNum(y)` at `y`.
* `bondPriceDisc_deriv_eq_neg_modified_duration_times_price`: for `1 + y ≠ 0`, the derivative `P'`
  satisfies `P' / P(y) = -(ModNum(y) / P(y))`, i.e. `P'/P = -D_mod`.

## Tags

modified duration, price sensitivity, interest rate risk, bond duration, yield derivative,
coupon bond, MSC 91G30, JEL G12
-/

@[expose] public section

namespace MathFin

open Finset

variable {ι : Type*}

/-- **Per-cashflow derivative**: `d/dy [c / (1+y)^n] = -n · c / (1+y)^(n+1)`.

Proof: chain rule via `HasDerivAt.pow` on `(1 + y')^n`, then `HasDerivAt.div`
with a constant numerator. The `n = 0` and `n ≥ 1` cases are bundled by the
final `field_simp + ring`. -/
lemma hasDerivAt_coupon_term (c_val : ℝ) (n : ℕ) {y : ℝ} (hy : 1 + y ≠ 0) :
    HasDerivAt (fun y' ↦ c_val / (1 + y') ^ n)
               (-((n : ℝ) * c_val / (1 + y) ^ (n + 1))) y := by
  have h_base : HasDerivAt (fun y' : ℝ ↦ (1 : ℝ) + y') 1 y :=
    (hasDerivAt_id y).const_add 1
  have h_pow : HasDerivAt (fun y' : ℝ ↦ (1 + y') ^ n)
               ((n : ℝ) * (1 + y) ^ (n - 1) * 1) y := h_base.pow n
  have h_pow_ne : (1 + y) ^ n ≠ 0 := pow_ne_zero _ hy
  have h_const : HasDerivAt (fun _ : ℝ ↦ c_val) 0 y := hasDerivAt_const y c_val
  have h_div := h_const.div h_pow h_pow_ne
  rw [show (-((n : ℝ) * c_val / (1 + y) ^ (n + 1)))
        = (0 * (1 + y) ^ n - c_val * ((n : ℝ) * (1 + y) ^ (n - 1) * 1)) / ((1 + y) ^ n) ^ 2 from by
      cases n with
      | zero => simp
      | succ m =>
        simp only [Nat.add_sub_cancel]
        have h_pow_m_ne : (1 + y) ^ m ≠ 0 := pow_ne_zero _ hy
        field_simp
        ring]
  exact h_div

/-- **Bond price has derivative `-ModNum(y)`**: the modified duration
numerator is the negative slope of the bond price.

Proof: term-by-term derivative via `hasDerivAt_coupon_term`, summed over
the cashflow finset. The sum-of-functions vs function-of-sums identification
is handled by `Finset.sum_apply`. -/
theorem hasDerivAt_bondPriceDisc
    (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) {y : ℝ} (hy : 1 + y ≠ 0) :
    HasDerivAt (bondPriceDisc s t c)
               (-modifiedNumerator s t c y) y := by
  unfold bondPriceDisc modifiedNumerator
  rw [show -∑ i ∈ s, (t i : ℝ) * c i / (1 + y) ^ (t i + 1) =
      ∑ i ∈ s, (-((t i : ℝ) * c i / (1 + y) ^ (t i + 1))) from by
    rw [← Finset.sum_neg_distrib]]
  apply HasDerivAt.fun_sum
  intros i _
  exact hasDerivAt_coupon_term (c i) (t i) hy

/-- **Duration-sensitivity identity**: `P'(y) / P(y) = -D_mod(y)`, where
`D_mod = ModNum / P` is the modified duration.

This is the operational content of duration: it measures the *percentage*
sensitivity of bond price to yield. Combined with
`modifiedNumerator_eq_macaulayNumerator_div`, gives the standard
discrete-compounding identity `D_mod = D_Mac / (1 + y)`. -/
theorem bondPriceDisc_deriv_eq_neg_modified_duration_times_price
    (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) {y : ℝ}
    (hy : 1 + y ≠ 0) :
    ∃ P' : ℝ, HasDerivAt (bondPriceDisc s t c) P' y ∧
      P' / bondPriceDisc s t c y =
        -(modifiedNumerator s t c y / bondPriceDisc s t c y) := by
  refine ⟨-modifiedNumerator s t c y, hasDerivAt_bondPriceDisc s t c hy, ?_⟩
  rw [neg_div]

end MathFin
