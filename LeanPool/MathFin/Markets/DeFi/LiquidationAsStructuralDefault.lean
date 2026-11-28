/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Markets.DeFi.Aave
public import LeanPool.MathFin.Markets.DeFi.Dai
public import LeanPool.MathFin.Models.Credit.KMVMerton

/-!
# Lending-protocol liquidation as Merton structural default

A collateralised loan in a lending protocol is liquidatable once the collateral value falls
below a multiple of the debt: a Dai vault once `collateral / debt < LR` (`Dai.isLiquidatable`),
an Aave position once its health factor `collateral · LT / debt` drops below `1`. With the
collateral value lognormal and the debt fixed, "liquidatable at the horizon `T`" is exactly
Merton's (1974) default event `V_T < F` with default barrier `F = LR · debt`, respectively
`F = debt / LT`. Its probability is the library's KMV default probability
`kmvPD = Φ(−d₂)` (`Models/Credit/KMVMerton.lean`).

The lognormal hypothesis is the library's `BSCallHyp Q C₀ F μ σ T Z`: `Z` is standard normal
under `Q` and the collateral value at `T` is `bsTerminal C₀ μ σ T (Z ·)`. Its rate slot `μ` is
used as the collateral's drift, so `Q` may be the physical measure (drift `μ`) or the
risk-neutral one (`μ = r`). The strike slot carries the barrier.

## Main results

* `bsTerminal_lt_iff`: the shortfall region `S_T(z) < K ↔ z < −d₂`, the strict mirror of
  `bsTerminal_gt_K_iff`.
* `prob_bsTerminal_lt_eq_kmvPD`: `Q(S_T < K) = kmvPD S₀ K μ σ T = Φ(−d₂)`.
* `prob_isLiquidatable_eq_kmvPD`: the probability that a Dai vault is liquidatable at `T`.
* `prob_healthFactorV1_lt_one_eq_kmvPD`: the probability that an Aave single-asset health factor
  is below `1` at `T`.

## Scope

The event is checked at the single date `T`. Protocols liquidate at the first time the threshold
is crossed, a first-passage event before `T` whose probability this file does not compute. The
debt is a fixed number at `T` (accrue it first, e.g. with
`Dai.debt_mul_zcb_log_eq`); only one collateral asset is risky.

## References

* [Aave, *Aave Protocol V2 whitepaper*][Aave2020], §5
* [R. C. Merton, *On the pricing of corporate debt: the risk structure of interest
  rates*][Merton1974]

## Tags

Merton structural model, default probability, DeFi lending, liquidation, health factor, KMV,
MSC 91G40, MSC 91G80, JEL G33
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

/-- **Shortfall-region identification**: `S_T(z) < K ↔ z < −d₂`, the strict mirror of
`bsTerminal_gt_K_iff`. -/
lemma bsTerminal_lt_iff {S_0 K r σ T : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ)
    (hT : 0 < T) (z : ℝ) :
    bsTerminal S_0 r σ T z < K ↔ z < -bsd2 S_0 K r σ T := by
  have hb : 0 < σ * Real.sqrt T := mul_pos hσ (Real.sqrt_pos.mpr hT)
  have hcore : bsTerminal S_0 r σ T z < K ↔
      (r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z < Real.log (K / S_0) := by
    rw [bsTerminal, mul_comm S_0, ← lt_div_iff₀ hS_0]
    exact (Real.lt_log_iff_exp_lt (div_pos hK hS_0)).symm
  rw [hcore, bsd2_eq hσ hT, ← neg_div, lt_div_iff₀ hb,
    show Real.log (K / S_0) = -Real.log (S_0 / K) by
      rw [Real.log_div hK.ne' hS_0.ne', Real.log_div hS_0.ne' hK.ne']; ring]
  constructor <;> intro h <;> linarith

/-- **The lognormal shortfall probability is the Merton–KMV default probability**: under
`BSCallHyp`, `Q(S_T < K) = kmvPD S₀ K μ σ T = Φ(−d₂)`. The strict and non-strict events have the
same probability because the standard normal law has no atoms. -/
theorem prob_bsTerminal_lt_eq_kmvPD {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    [IsProbabilityMeasure Q] {S_0 K μ σ T : ℝ} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K μ σ T Z) :
    (Q {ω | bsTerminal S_0 μ σ T (Z ω) < K}).toReal = kmvPD S_0 K μ σ T := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  have hset : {ω | bsTerminal S_0 μ σ T (Z ω) < K} = Z ⁻¹' Set.Iio (-bsd2 S_0 K μ σ T) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio]
    exact bsTerminal_lt_iff hS_0 hK hσ hT (Z ω)
  have : NullSingletonClass (gaussianReal (0 : ℝ) 1) := nullSingletonClass_gaussianReal one_ne_zero
  rw [hset, ← Measure.map_apply_of_aemeasurable hZ.aemeasurable measurableSet_Iio, hZ.map_eq,
    measure_congr (Iio_ae_eq_Iic (μ := gaussianReal 0 1)), ← Phi_def, kmvPD,
    kmvDistanceToDefault_eq_bsd2 _ _ _ _ _ hS_0 hK]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]

/-- **Probability that a Dai vault is liquidatable at the horizon.** With collateral value
`bsTerminal C₀ μ σ T (Z ·)` (lognormal, `BSCallHyp`), debt `D > 0` at `T` and liquidation ratio
`LR`, the probability that `collateral / debt < LR` at `T` is the Merton–KMV default probability
with barrier `LR · D`: `Φ(−d₂(C₀, LR·D, μ, σ, T))`. A check at `T` only, not the first passage
before `T`. -/
theorem prob_isLiquidatable_eq_kmvPD {C_0 D LR μ σ T : ℝ} {Z : Ω → ℝ} (hD : 0 < D)
    (h : BSCallHyp Q C_0 (LR * D) μ σ T Z) :
    (Q {ω | DeFi.Dai.isLiquidatable (bsTerminal C_0 μ σ T (Z ω)) D LR}).toReal
      = kmvPD C_0 (LR * D) μ σ T := by
  simp_rw [DeFi.Dai.isLiquidatable_iff_mul hD]
  exact prob_bsTerminal_lt_eq_kmvPD h

/-- **Probability that an Aave health factor is below `1` at the horizon.** With collateral value
`bsTerminal C₀ μ σ T (Z ·)` (lognormal, `BSCallHyp`), liquidation threshold `LT > 0` and total debt
`B + F > 0` at `T`, the probability that `healthFactorV1 < 1` (the whitepaper's liquidation
criterion) is the Merton–KMV default probability with barrier `(B + F) / LT`. A check at `T` only,
not the first passage before `T`. -/
theorem prob_healthFactorV1_lt_one_eq_kmvPD {C_0 LT B F μ σ T : ℝ} {Z : Ω → ℝ}
    (hdebt : 0 < B + F) (hLT : 0 < LT) (h : BSCallHyp Q C_0 ((B + F) / LT) μ σ T Z) :
    (Q {ω | DeFi.Aave.healthFactorV1 (bsTerminal C_0 μ σ T (Z ω)) LT B F < 1}).toReal
      = kmvPD C_0 ((B + F) / LT) μ σ T := by
  simp_rw [DeFi.Aave.healthFactorV1_lt_one_iff hdebt, ← lt_div_iff₀ hLT]
  exact prob_bsTerminal_lt_eq_kmvPD h

end MathFin
