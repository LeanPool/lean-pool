/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.PeriodicCompounding

/-!
# Dai (MakerDAO): liquidation inequality and stability-fee compounding

Adapted from the MakerDAO whitepaper (Maker, "The Maker Protocol:
MakerDAO's Multi-Collateral Dai (MCD) System", 2020,
<https://makerdao.com/en/whitepaper>): the collateralization /
liquidation criterion from the "Liquidation of Risky Maker Vaults" section,
and the "Liquidation Ratio" / "Stability Fee" parameter entries under
"Risk Parameters Controlled by Maker Governance" (these are named
parameter entries, not sub-sections of the paper).

## Main definitions

* `isLiquidatable`: the predicate `collateral / debt < liquidationRatio` on a vault.

## Main results

* `isLiquidatable_iff_mul`: cross-multiplied equivalent form (no division), for
  `debt > 0`.
* `debt_eq_debt_zero_mul_pow`: the compounding recurrence
  `debt (n+1) = debt n · (1 + fee)` has closed form `debt n = debt 0 · (1+fee)^n`
  (the library's `eq_mul_pow_of_succ`, `Models/Rates/PeriodicCompounding.lean`).
* `debt_mul_zcb_log_eq`: per-period stability-fee compounding *is* continuous compounding at
  the rate `log (1 + fee)`: discounting the debt after `n` periods by the zero-coupon bond
  `zcb (log (1 + fee)) 0 n` returns the initial debt, for `fee > −1`. The Multi-Collateral Dai
  `Jug` compounds its per-second rate (`duty`) over the elapsed seconds, so a period here is a
  second and `log (1 + fee)` is the continuously compounded per-second rate.

The probability that a vault with lognormal collateral is liquidatable at a horizon is in
`MathFin/Markets/DeFi/LiquidationAsStructuralDefault.lean` (`prob_isLiquidatable_eq_kmvPD`).

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], §4.2
* [MakerDAO, *The Maker Protocol: MakerDAO's Multi-Collateral Dai (MCD) System*][MakerDAO2020]
* [MakerDAO, *MakerDAO technical documentation*][MakerDAOTechDocs], Rates Module

## Tags

MakerDAO, stablecoin, vault liquidation, collateralization ratio, stability fee, compounding,
MSC 91G80, JEL G23
-/

@[expose] public section

namespace MathFin

namespace DeFi

namespace Dai

/-- **Dai liquidation predicate**: a vault is liquidatable once its
collateralization ratio `collateral / debt` falls below the protocol's
liquidation ratio. -/
noncomputable def isLiquidatable (collateral debt liquidationRatio : ℝ) : Prop :=
  collateral / debt < liquidationRatio

/-- **Division-free equivalent** of the liquidation predicate, valid when
debt is positive: `collateral / debt < LR ↔ collateral < LR · debt`. -/
theorem isLiquidatable_iff_mul
    {collateral debt liquidationRatio : ℝ} (hdebt : 0 < debt) :
    isLiquidatable collateral debt liquidationRatio ↔ collateral < liquidationRatio * debt := by
  unfold isLiquidatable
  rw [div_lt_iff₀ hdebt]

/-- **Dai stability-fee compounding**: given a vault-debt sequence
satisfying `debt (n+1) = debt n · (1 + fee)` at every step, the debt after
`n` periods equals the initial debt compounded at the per-period stability
fee, `debt n = debt 0 · (1 + fee)^n`: the closed form of a per-period accrual index,
`eq_mul_pow_of_succ`. -/
theorem debt_eq_debt_zero_mul_pow
    (debt : ℕ → ℝ) (fee : ℝ)
    (hrec : ∀ n, debt (n + 1) = debt n * (1 + fee)) :
    ∀ n, debt n = debt 0 * (1 + fee) ^ n :=
  eq_mul_pow_of_succ hrec

/-- **Stability-fee compounding is continuous compounding at the rate `log (1 + fee)`.** If the
vault debt compounds at the per-period fee `fee > −1`, then discounting the debt after `n`
periods by the zero-coupon bond at the continuously compounded rate `log (1 + fee)` (time in
periods) returns the initial debt: `debt n · zcb (log (1 + fee)) 0 n = debt 0`. -/
theorem debt_mul_zcb_log_eq (debt : ℕ → ℝ) {fee : ℝ} (hfee : -1 < fee)
    (hrec : ∀ n, debt (n + 1) = debt n * (1 + fee)) (n : ℕ) :
    debt n * zcb (Real.log (1 + fee)) 0 n = debt 0 := by
  rw [debt_eq_debt_zero_mul_pow debt fee hrec n, mul_assoc, one_add_pow_mul_zcb_log hfee n,
    mul_one]

end Dai

end DeFi

end MathFin
