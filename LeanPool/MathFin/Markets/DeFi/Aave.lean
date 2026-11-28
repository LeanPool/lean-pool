/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.PeriodicCompounding
public import Mathlib.Algebra.Order.Star.Real

/-!
# Aave v2: kinked interest-rate model, health factor, liquidity index

Adapted from the Aave v2 whitepaper (Aave, "Aave Protocol V2", 2020,
<https://github.com/aave/protocol-v2/blob/master/aave-v2-whitepaper.pdf>),
§5 ("Formal Definitions"), which states the kinked borrow-rate model and the
health factor; the liquidity-index recurrence is §3.1 ("aTokens").

## Main definitions

* `kinkedRate`: the piecewise-linear Aave v2 borrow rate in the utilization `U`, with optimal
  utilization `Uopt` and slopes `slope1`, `slope2`.
* `healthFactorV1`: the single-asset health factor
  `collateral * liquidationThreshold / (borrows + fees)`.
* `healthFactorV2`: the multi-asset health factor summed over `i ∈ s`.
* `liquidityIndexStep`: the per-period growth factor `R * U * ΔT / Tyear + 1` of the liquidity
  index.
* `stableRateUpdate`: the stable-rate weighted average after a new stable-rate borrow.

## Main results

* `kinkedRate_apply_optimal`: the rate at the kink is `R₀ + slope1`, for
  `Uopt ≠ 0` (the value of the `U ≤ Uopt` branch).
* `kinkedRate_eq_affine_add_hinge`: for `Uopt ≠ 0` the kinked curve is an affine rate plus
  `(slope2/(1 − Uopt) − slope1/Uopt) · max (U − Uopt) 0`, a call payoff on utilization struck
  at the kink; hence `continuous_kinkedRate`, the curve is continuous (at the kink included).
* `kinkedRate_monotone`: the curve is monotone nondecreasing on `[0, 1]`
  when `0 < Uopt < 1` and both slopes are nonnegative.
* `healthFactorV1`, `healthFactorV2`: the single-asset and multi-asset
  (summed) health-factor definitions; `healthFactorV1_lt_one_iff`, the liquidation criterion
  `Hf < 1 ↔ collateral · LT < debt` (whitepaper §5: below `1` the loan "can be liquidated").
  The probability of `Hf < 1` at a horizon, for lognormal collateral, is
  `prob_healthFactorV1_lt_one_eq_kmvPD` in
  `MathFin/Markets/DeFi/LiquidationAsStructuralDefault.lean`.
* `liquidityIndexStep`, `liquidityIndex_eq_prod_mul`: the linear recurrence
  `LI_t = (R_t·U_t·ΔT/T_year + 1)·LI_{t-1}`
  and its closed-form (product) solution, matching the whitepaper's
  `LiquidityRate_t = BorrowRate_t·U_t` exactly (`R` here stands for
  `BorrowRate`). **Scope disclosure**: the deployed
  `DefaultReserveInterestRateStrategy` contract additionally multiplies by
  `(1 − reserveFactor)`, a refinement not in the whitepaper and not modeled
  here (equivalently, the `reserveFactor = 0` simplification relative to the
  on-chain contract).
* `liquidityIndex_eq_pow_mul`, `tendsto_liquidityIndexStep_pow`: at a constant borrow rate and
  utilization the index grows by a power of one step factor, and splitting a horizon into `n`
  equal update intervals, that power tends to `1 / zcb (R·U) 0 (T/Tyear)` — continuous
  compounding at the liquidity rate, the library's zero-coupon bond
  (`Models/Rates/PeriodicCompounding.lean`). Time-varying rates are not covered by the limit.
* `stableRateUpdate`, `stableRateUpdate_mem_interval`: the weighted-average new
  stable rate, shown to lie in `[SRprev, SRnew]` when the new borrower's rate is
  at least the pool's prior average, the prior stable debt is nonnegative and
  the new borrow is positive.

## Tags

Aave protocol, lending pool, borrow rate, utilization, health factor, liquidation, liquidity index,
MSC 91G80, JEL G23
-/

@[expose] public section

namespace MathFin

open Filter Topology

namespace DeFi

namespace Aave

/-- **Aave v2 kinked borrow-rate model** (whitepaper §5, Formal Definitions): below the optimal
utilization `U_opt`, the rate rises linearly from `R₀` with slope `slope1/U_opt`;
above it, it rises linearly from `R₀ + slope1` with slope `slope2/(1-U_opt)`.
`U_opt ∈ (0,1)` is the kink location. -/
noncomputable def kinkedRate (R₀ slope1 slope2 Uopt U : ℝ) : ℝ :=
  if U ≤ Uopt then R₀ + U / Uopt * slope1
  else R₀ + slope1 + (U - Uopt) / (1 - Uopt) * slope2

/-- **The rate at the kink** is `R₀ + slope1` — the value the `U ≤ Uopt`
branch takes at `U = Uopt`. That the `else` branch approaches the same value is
`continuous_kinkedRate`. -/
theorem kinkedRate_apply_optimal (R₀ slope1 slope2 Uopt : ℝ) (hU : Uopt ≠ 0) :
    kinkedRate R₀ slope1 slope2 Uopt Uopt = R₀ + slope1 := by
  unfold kinkedRate
  rw [ite_eq_left le_rfl, div_self hU, one_mul]

/-- **The kinked rate is an affine rate plus a call on utilization.** For `Uopt ≠ 0`,

  `kinkedRate R₀ slope1 slope2 Uopt U = R₀ + (slope1/Uopt)·U + c · max (U − Uopt) 0`,

with `c = slope2/(1−Uopt) − slope1/Uopt` the jump in slope at the kink. Below the kink only the
affine part is active; above it the hinge `max (U − Uopt) 0`, the payoff of a call on
utilization struck at `Uopt`, adds the jump. -/
theorem kinkedRate_eq_affine_add_hinge (R₀ slope1 slope2 : ℝ) {Uopt : ℝ} (hU : Uopt ≠ 0)
    (U : ℝ) :
    kinkedRate R₀ slope1 slope2 Uopt U
      = R₀ + slope1 / Uopt * U + (slope2 / (1 - Uopt) - slope1 / Uopt) * max (U - Uopt) 0 := by
  unfold kinkedRate
  split_ifs with h
  · rw [max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left (sub_nonneg.mpr (not_le.mp h).le)]
    linear_combination -div_mul_cancel₀ slope1 hU

/-- **The kinked rate is continuous** for `Uopt ≠ 0`, at the kink included: by
`kinkedRate_eq_affine_add_hinge` it is an affine function plus a multiple of
`max (U − Uopt) 0`. -/
theorem continuous_kinkedRate (R₀ slope1 slope2 : ℝ) {Uopt : ℝ} (hU : Uopt ≠ 0) :
    Continuous (kinkedRate R₀ slope1 slope2 Uopt) := by
  rw [funext (kinkedRate_eq_affine_add_hinge R₀ slope1 slope2 hU)]
  fun_prop

/-- **Monotonicity on `[0,1]`**: if `0 < Uopt < 1` and both slopes are
nonnegative, the kinked rate is monotone nondecreasing in utilization `U`. -/
theorem kinkedRate_monotone {R₀ slope1 slope2 Uopt : ℝ}
    (hUopt0 : 0 < Uopt) (hUopt1 : Uopt < 1)
    (hs1 : 0 ≤ slope1) (hs2 : 0 ≤ slope2) :
    MonotoneOn (kinkedRate R₀ slope1 slope2 Uopt) (Set.Icc 0 1) := by
  intro U hU V hV hUV
  simp only [Set.mem_Icc] at hU hV
  unfold kinkedRate
  have h1mUopt : 0 < 1 - Uopt := by linarith
  by_cases hUle : U ≤ Uopt <;> by_cases hVle : V ≤ Uopt
  · rw [ite_eq_left hUle, ite_eq_left hVle]
    gcongr
  · rw [ite_eq_left hUle, ite_eq_right hVle]
    have h1 : U / Uopt * slope1 ≤ slope1 :=
      mul_le_of_le_one_left hs1 ((div_le_one hUopt0).mpr hUle)
    have h2 : 0 ≤ (V - Uopt) / (1 - Uopt) * slope2 :=
      mul_nonneg (div_nonneg (by linarith [not_le.mp hVle]) h1mUopt.le) hs2
    linarith
  · exact absurd ((not_le.mp hUle).trans_le (hUV.trans hVle)) (lt_irrefl _)
  · rw [ite_eq_right hUle, ite_eq_right hVle]
    have : (U - Uopt) / (1 - Uopt) ≤ (V - Uopt) / (1 - Uopt) :=
      (div_le_div_iff_of_pos_right h1mUopt).mpr (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right this hs2]

/-- **Aave v1/v2 single-asset health factor**: collateral weighted by its
liquidation threshold, over total debt (borrows plus accrued fees). Values
`> 1` indicate a safe position. -/
noncomputable def healthFactorV1 (collateral liquidationThreshold borrows fees : ℝ) : ℝ :=
  collateral * liquidationThreshold / (borrows + fees)

/-- **Health factor safety criterion**: `1 < Hf ↔ debt < collateral·LT`, when
total debt is positive. -/
theorem one_lt_healthFactorV1_iff
    {collateral liquidationThreshold borrows fees : ℝ} (hdebt : 0 < borrows + fees) :
    1 < healthFactorV1 collateral liquidationThreshold borrows fees ↔
      borrows + fees < collateral * liquidationThreshold := by
  unfold healthFactorV1
  rw [lt_div_iff₀ hdebt, one_mul]

/-- **Liquidation criterion**: `Hf < 1 ↔ collateral·LT < debt`, when total debt is positive.
The Aave v2 whitepaper (§5, Formal Definitions) calls a loan with `Hf < 1` undercollateralised
and liquidatable. -/
theorem healthFactorV1_lt_one_iff
    {collateral liquidationThreshold borrows fees : ℝ} (hdebt : 0 < borrows + fees) :
    healthFactorV1 collateral liquidationThreshold borrows fees < 1 ↔
      collateral * liquidationThreshold < borrows + fees := by
  rw [healthFactorV1, div_lt_one hdebt]

/-- **Aave v2 multi-asset health factor**: summed over the borrower's
assets `i ∈ s`, collateral weighted by each asset's liquidation threshold
over total borrows across assets. -/
noncomputable def healthFactorV2 {ι : Type*} (s : Finset ι)
    (collateral liquidationThreshold borrows : ι → ℝ) : ℝ :=
  (∑ i ∈ s, collateral i * liquidationThreshold i) / ∑ i ∈ s, borrows i

/-- **Multi-asset health factor safety criterion**, the `healthFactorV2`
analogue of `one_lt_healthFactorV1_iff`. -/
theorem one_lt_healthFactorV2_iff {ι : Type*} {s : Finset ι}
    {collateral liquidationThreshold borrows : ι → ℝ}
    (hdebt : 0 < ∑ i ∈ s, borrows i) :
    1 < healthFactorV2 s collateral liquidationThreshold borrows ↔
      ∑ i ∈ s, borrows i < ∑ i ∈ s, collateral i * liquidationThreshold i := by
  unfold healthFactorV2
  rw [lt_div_iff₀ hdebt, one_mul]

/-- **Aave v2 liquidity-index recurrence** (whitepaper §3.1, aTokens): the
index accrues each period by the per-period yield `R · U · ΔT / T_year`,
where `R` stands for the borrow rate, matching the whitepaper's
`LiquidityRate_t = BorrowRate_t·U_t` exactly. **Scope disclosure**: the
deployed `DefaultReserveInterestRateStrategy` contract additionally
multiplies by `(1 − reserveFactor)`, a refinement not in the whitepaper and
not modeled here. -/
noncomputable def liquidityIndexStep (R U ΔT Tyear : ℝ) : ℝ :=
  R * U * ΔT / Tyear + 1

/-- **Closed form of the liquidity-index recurrence**: given a sequence
`LI` satisfying `LI (n+1) = liquidityIndexStep (R (n+1)) (U (n+1)) ΔT Tyear * LI n`
for every step, the index after `n` steps equals the initial index times the
product of all per-step growth factors. Proved by induction on `n`. -/
theorem liquidityIndex_eq_prod_mul
    (LI R U : ℕ → ℝ) (ΔT Tyear : ℝ)
    (hrec : ∀ n, LI (n + 1) = liquidityIndexStep (R (n + 1)) (U (n + 1)) ΔT Tyear * LI n) :
    ∀ n, LI n = (∏ t ∈ Finset.range n, liquidityIndexStep (R (t + 1)) (U (t + 1)) ΔT Tyear) * LI 0
  | 0 => by simp
  | (n + 1) => by
      rw [hrec n, liquidityIndex_eq_prod_mul LI R U ΔT Tyear hrec n,
        Finset.prod_range_succ]
      ring

/-- **Constant rates: the index grows by a power of one step factor.** If the borrow rate `R`
and utilization `U` do not change, `liquidityIndex_eq_prod_mul` collapses to
`LI n = liquidityIndexStep R U ΔT Tyear ^ n · LI 0`. -/
theorem liquidityIndex_eq_pow_mul (LI : ℕ → ℝ) (R U ΔT Tyear : ℝ)
    (hrec : ∀ n, LI (n + 1) = liquidityIndexStep R U ΔT Tyear * LI n) (n : ℕ) :
    LI n = liquidityIndexStep R U ΔT Tyear ^ n * LI 0 := by
  simpa using liquidityIndex_eq_prod_mul LI (fun _ ↦ R) (fun _ ↦ U) ΔT Tyear hrec n

/-- **Frequent updates converge to continuous compounding at the liquidity rate.** At a constant
borrow rate `R` and utilization `U`, splitting a horizon `T` into `n` equal update intervals
`T / n` gives the index growth `liquidityIndexStep R U (T / n) Tyear ^ n`, which tends to
`1 / zcb (R·U) 0 (T / Tyear) = exp (R·U·T/Tyear)` as `n → ∞`. Each step accrues linear
interest; the limit is the zero-coupon bond's continuous compounding. -/
theorem tendsto_liquidityIndexStep_pow (R U T Tyear : ℝ) :
    Tendsto (fun n : ℕ ↦ liquidityIndexStep R U (T / n) Tyear ^ n) atTop
      (𝓝 (zcb (R * U) 0 (T / Tyear))⁻¹) := by
  have h (n : ℕ) : liquidityIndexStep R U (T / n) Tyear = 1 + R * U * (T / Tyear) / n := by
    unfold liquidityIndexStep
    ring
  simpa only [h] using tendsto_one_add_div_pow_inv_zcb (R * U) (T / Tyear)

/-- **Aave v2 stable-rate weighted average** (whitepaper §3.4): when a new
stable-rate borrow of size `SBnew` at rate `SRnew` joins an existing stable
debt pool `SDprev` at average rate `SRprev`, the new pool average is the
debt-weighted mean of the two rates. -/
noncomputable def stableRateUpdate (SRprev SDprev SRnew SBnew : ℝ) : ℝ :=
  (SRprev * SDprev + SRnew * SBnew) / (SDprev + SBnew)

/-- **The updated stable rate lies between** the previous average and the new
borrower's rate **when the new borrower's rate is at least the prior average**
(`hle : SRprev ≤ SRnew`), the prior stable debt is nonnegative and the new borrow
is positive. It is a weighted average with nonnegative weights and positive total
weight, so it cannot exceed (resp. fall below) the larger (resp. smaller) of the
two inputs. -/
theorem stableRateUpdate_mem_interval
    {SRprev SDprev SRnew SBnew : ℝ}
    (hSDprev : 0 ≤ SDprev) (hSBnew : 0 < SBnew) (hle : SRprev ≤ SRnew) :
    SRprev ≤ stableRateUpdate SRprev SDprev SRnew SBnew ∧
      stableRateUpdate SRprev SDprev SRnew SBnew ≤ SRnew := by
  unfold stableRateUpdate
  have hden : 0 < SDprev + SBnew := by linarith
  constructor
  · rw [le_div_iff₀ hden]; nlinarith
  · rw [div_le_iff₀ hden]; nlinarith

end Aave

end DeFi

end MathFin
