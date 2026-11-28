/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.ZCB
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Periodic compounding against the continuously compounded bond

An account that accrues simple interest `y` per period and reinvests it grows like `(1 + y) ^ n`
over `n` periods. This file places that geometric growth next to the library's continuously
compounded zero-coupon bond `zcb r t T = exp (−r (T − t))` (`Models/Rates/ZCB.lean`), in three
statements:

* `one_add_pow_mul_zcb_log`: compounding at `y > −1` per period is exactly continuous compounding
  at the equivalent rate `log (1 + y)`, with time measured in periods: discounting the grown
  balance by `zcb (log (1 + y)) 0 n` returns the initial balance. This is the conversion
  `R_c = m · log (1 + R_m / m)` with `m = 1`.
* `one_add_mul_pow_le_inv_zcb`: at the *same* nominal rate `r`, `n` periods of length `t` (with
  `r t ≥ −1`) never out-accrue continuous compounding over the elapsed time `n · t`:
  `(1 + r t)^n ≤ 1 / zcb r 0 (n t)` (from `1 + x ≤ exp x`).
* `tendsto_one_add_div_pow_inv_zcb`: splitting a horizon `T` into `n` equal periods,
  `(1 + r T / n) ^ n → 1 / zcb r 0 T = exp (r T)` (Mathlib's `Real.tendsto_one_add_div_pow_exp`).

`eq_mul_pow_of_succ` is the closed form of the recurrence `I (n + 1) = I n · c` that every
per-period accrual index satisfies. The DeFi protocol modules (`Markets/DeFi/Compound`,
`Markets/DeFi/Dai`, `Markets/DeFi/Aave`) instantiate these lemmas for their accrual indices.

## Main results

* `eq_mul_pow_of_succ`: if `I (n + 1) = I n · c` for every `n`, then `I n = I 0 · c ^ n`.
* `one_add_pow_mul_zcb_log`: for `y > −1`, `(1 + y) ^ n · zcb (log (1 + y)) 0 n = 1`, so periodic
  compounding at `y` is continuous compounding at the rate `log (1 + y)`.
* `one_add_mul_pow_le_inv_zcb`: for `r t ≥ −1`, `(1 + r t) ^ n ≤ (zcb r 0 (n t))⁻¹`.
* `tendsto_one_add_div_pow_inv_zcb`: `(1 + r T / n) ^ n` tends to `(zcb r 0 T)⁻¹ = exp (r T)` as
  `n → ∞`.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], §4.2 (measuring interest rates;
  continuous compounding and the conversion between compounding frequencies).

## Tags

compound interest, continuous compounding, periodic compounding, effective rate, zero-coupon bond,
exponential limit, MSC 91G30, JEL G12
-/

@[expose] public section

namespace MathFin

open Filter Topology

/-- **The closed form of a per-period accrual index**: if `I (n + 1) = I n · c` for every `n`,
then `I n = I 0 · c ^ n`. -/
theorem eq_mul_pow_of_succ {I : ℕ → ℝ} {c : ℝ} (h : ∀ n, I (n + 1) = I n * c) :
    ∀ n, I n = I 0 * c ^ n
  | 0 => by simp
  | n + 1 => by rw [h n, eq_mul_pow_of_succ h n, pow_succ, mul_assoc]

/-- **Per-period compounding is continuous compounding at the equivalent rate.** With time
measured in periods, compounding at `y > −1` per period for `n` periods and then discounting by
the zero-coupon bond at the continuously compounded rate `log (1 + y)` returns exactly one:
`(1 + y) ^ n · zcb (log (1 + y)) 0 n = 1`. -/
theorem one_add_pow_mul_zcb_log {y : ℝ} (hy : -1 < y) (n : ℕ) :
    (1 + y) ^ n * zcb (Real.log (1 + y)) 0 n = 1 := by
  rw [zcb, ← Real.exp_log (pow_pos (by linarith : (0 : ℝ) < 1 + y) n), Real.log_pow,
    ← Real.exp_add, Real.exp_eq_one_iff]
  ring

/-- **Periodic compounding never out-accrues continuous compounding at the same rate.** For
`n` periods of length `t` at the nominal rate `r` (with `r t ≥ −1`),
`(1 + r t) ^ n ≤ 1 / zcb r 0 (n t) = exp (r · n t)`, since `1 + x ≤ exp x`. -/
theorem one_add_mul_pow_le_inv_zcb {r t : ℝ} (h : -1 ≤ r * t) (n : ℕ) :
    (1 + r * t) ^ n ≤ (zcb r 0 (n * t))⁻¹ := by
  rw [zcb, sub_zero, ← Real.exp_neg, neg_neg, show r * (n * t) = n * (r * t) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (r * t)]) n

/-- **Continuous compounding is the limit of periodic compounding.** Splitting the horizon `T`
into `n` equal periods at the nominal rate `r`, the accrual factor `(1 + r T / n) ^ n` tends to
`1 / zcb r 0 T = exp (r T)`. -/
theorem tendsto_one_add_div_pow_inv_zcb (r T : ℝ) :
    Tendsto (fun n : ℕ ↦ (1 + r * T / n) ^ n) atTop (𝓝 (zcb r 0 T)⁻¹) := by
  rw [zcb, sub_zero, ← Real.exp_neg, neg_neg]
  exact Real.tendsto_one_add_div_pow_exp (r * T)

end MathFin
