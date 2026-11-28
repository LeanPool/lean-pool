/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.PeriodicCompounding

/-!
# Compound: utilization, affine borrow rate, cToken exchange-rate monotonicity

Adapted from the Compound whitepaper (R. Leshner and G. Hayes, "Compound: The Money
Market Protocol", v1.0, February 2019): §2.3 Interest Rate Model (utilization,
affine borrow rate), §3.1 cToken Contracts (exchange rate) and §3.2.1 Market Dynamics
(interest-rate index, reserve-factor accrual).

## Main definitions

* `utilization`: `borrows / (cash + borrows)`.
* `borrowRate`: the affine rate `base + slope * U`.
* `exchangeRate`: the cToken rate `(cash + borrows - reserves) / totalSupply`.

## Main results

* `utilization_mem_Icc`: for nonnegative cash and borrows, `U ∈ [0, 1]`.
* `borrowRate`, `borrowRate_monotone`: the affine rate `r = base + slope · U`,
  monotone in `U` when `slope ≥ 0`.
* `exchangeRate_mono`: over one accrual period, with cash and a positive total
  supply unchanged, the exchange rate does not decrease, **under the explicit
  hypothesis that the reserve-factor cut does not exceed the accrued
  interest** (`reservesAdded ≤ interest`) — the whitepaper's reserve-factor
  accrual equations give this (`reservesAdded = interest · reserveFactor` with
  `reserveFactor ∈ [0,1]` and `interest ≥ 0`), but it is stated as a standalone
  hypothesis on the accrued amounts rather than re-derived from `reserveFactor`.
* `borrowIndex_eq_mul_pow`, `borrowIndex_le_inv_zcb`, `tendsto_borrowIndex`: the interest-rate
  index of §3.2.1, `Index_n = Index_{n−1} · (1 + r·t)` at a per-block rate `r` over periods of
  length `t`, against the library's zero-coupon bond (`Models/Rates/PeriodicCompounding.lean`):
  at a constant rate it is `Index_0 · (1 + r t)^n`, never above continuous compounding
  `Index_0 / zcb r 0 (n t)`, and accruing a horizon `T` in `n` equal periods converges to
  `Index_0 / zcb r 0 T`. Rates that change between periods are not covered.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], §4.2
* [R. Leshner and G. Hayes, *Compound: The Money Market Protocol*][LeshnerHayes2019], §3.2.1

## Tags

Compound protocol, money market, utilization rate, cToken, exchange rate, borrow index, lending,
MSC 91G80, JEL G23
-/

@[expose] public section

namespace MathFin

open Filter Topology

namespace DeFi

namespace Compound

/-- **Compound utilization rate**: the fraction of the pool's assets
(cash + outstanding borrows) that is currently borrowed out, per the
whitepaper's §2.3 definition. (The deployed interest-rate-model contract
additionally nets reserves out of the denominator; that refinement is not
formalized here.) -/
noncomputable def utilization (cash borrows : ℝ) : ℝ :=
  borrows / (cash + borrows)

/-- For nonnegative cash and borrows the utilization lies in `[0, 1]` (it is `0` for an
empty pool, by the `x / 0 = 0` convention). -/
theorem utilization_mem_Icc {cash borrows : ℝ} (hcash : 0 ≤ cash) (hborrows : 0 ≤ borrows) :
    utilization cash borrows ∈ Set.Icc 0 1 :=
  ⟨div_nonneg hborrows (add_nonneg hcash hborrows),
    div_le_one_of_le₀ (by linarith) (add_nonneg hcash hborrows)⟩

/-- **Compound affine borrow-rate model**: `r(U) = base + slope · U`. Takes
`U` directly (rather than `cash`/`borrows`) so it applies uniformly whether
`U` comes from `utilization` or from the on-chain reserves-netted refinement
noted on `utilization`. -/
def borrowRate (base slope U : ℝ) : ℝ :=
  base + slope * U

/-- **Borrow rate is monotone nondecreasing in utilization** when the
slope is nonnegative. -/
theorem borrowRate_monotone {base slope : ℝ} (hslope : 0 ≤ slope) :
    Monotone (borrowRate base slope) := by
  intro U V hUV
  unfold borrowRate
  gcongr

/-- **Compound cToken exchange rate**: the redeemable-underlying-per-cToken
rate `(Cash + Borrows − Reserves) / TotalSupply`. -/
noncomputable def exchangeRate (cash borrows reserves totalSupply : ℝ) : ℝ :=
  (cash + borrows - reserves) / totalSupply

/-- **cToken exchange-rate monotonicity under interest accrual.**
Suppose a period accrues `interest` of new borrows, of which
`reservesAdded` is cut to reserves. **Explicit hypothesis**
`reservesAdded ≤ interest` — the whitepaper's reserve-factor accrual equations give
this (`reservesAdded = interest · reserveFactor` with `reserveFactor ∈ [0,1]` and
`interest ≥ 0`), but we state it as a standalone hypothesis on the
accrued amounts rather than re-deriving it from `reserveFactor` here. Under
it, with cash and supply unchanged and `totalSupply > 0`, the exchange rate after
accrual is at least the rate before. -/
theorem exchangeRate_mono
    {cash borrows reserves totalSupply interest reservesAdded : ℝ}
    (htotalSupply : 0 < totalSupply)
    (hreservesAdded : reservesAdded ≤ interest) :
    exchangeRate cash borrows reserves totalSupply ≤
      exchangeRate cash (borrows + interest) (reserves + reservesAdded) totalSupply := by
  unfold exchangeRate
  rw [div_le_div_iff_of_pos_right htotalSupply]
  linarith

/-- **Compound interest-rate index** (whitepaper §3.2.1, Market Dynamics): each transaction
compounds the index by the interest for the period, `Index_n = Index_{n−1} · (1 + r·t)`. At a
constant per-block rate `r` and period length `t`, the index is `Index_0 · (1 + r t)^n`. -/
theorem borrowIndex_eq_mul_pow (index : ℕ → ℝ) (r t : ℝ)
    (hrec : ∀ n, index (n + 1) = index n * (1 + r * t)) (n : ℕ) :
    index n = index 0 * (1 + r * t) ^ n :=
  eq_mul_pow_of_succ hrec n

/-- **Per-period accrual never exceeds continuous compounding at the same rate.** At a constant
rate `r` with `r t ≥ −1` and a nonnegative initial index, after `n` periods of length `t` the
index is at most `Index_0 / zcb r 0 (n t) = Index_0 · exp (r · n t)`. -/
theorem borrowIndex_le_inv_zcb (index : ℕ → ℝ) {r t : ℝ} (h0 : 0 ≤ index 0) (hrt : -1 ≤ r * t)
    (hrec : ∀ n, index (n + 1) = index n * (1 + r * t)) (n : ℕ) :
    index n ≤ index 0 * (zcb r 0 (n * t))⁻¹ := by
  rw [borrowIndex_eq_mul_pow index r t hrec n]
  exact mul_le_mul_of_nonneg_left (one_add_mul_pow_le_inv_zcb hrt n) h0

/-- **Accruing ever more often converges to continuous compounding.** Splitting a horizon `T`
into `n` equal accrual periods at the constant rate `r`, the index `Index_0 · (1 + r (T/n))^n`
tends to `Index_0 / zcb r 0 T = Index_0 · exp (r T)`. -/
theorem tendsto_borrowIndex (index₀ r T : ℝ) :
    Tendsto (fun n : ℕ ↦ index₀ * (1 + r * (T / n)) ^ n) atTop
      (𝓝 (index₀ * (zcb r 0 T)⁻¹)) := by
  simpa only [mul_div_assoc] using (tendsto_one_add_div_pow_inv_zcb r T).const_mul index₀

end Compound

end DeFi

end MathFin
