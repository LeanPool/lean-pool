/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.ExchangeOption
public import LeanPool.MathFin.Models.BlackScholes.MargrabeGrounding
public import LeanPool.MathFin.Probability.Gaussian.BivariateNormalCDF
public import Mathlib.Algebra.Order.Star.Real

/-!
# Stulz (1982): the two-asset rainbow (max/min) closed form

R. M. Stulz ("Options on the minimum or the maximum of two risky assets: analysis and
applications", *Journal of Financial Economics* 10 (1982), 161–185) prices a call on
`max(S¹_T, S²_T)` or `min(S¹_T, S²_T)` struck at `K` by a pair of bivariate-normal-CDF closed
forms. This module transcribes those closed forms; that they are the discounted expected payoffs
is Stulz's theorem and is not proved here (see **Scope**). Unlike `BasketMomentMatching.lean`'s
`n`-asset moment-matching approximation, Stulz's formula is exact, but only for `n = 2`.

The formulas are those of E. G. Haug, *The Complete Guide to Option Pricing Formulas*, 2nd ed.,
McGraw-Hill (2007), in the cost-of-carry convention `bᵢ` (`bᵢ = r` for a non-dividend asset,
`bᵢ = r - qᵢ` under a continuous yield `qᵢ`, `bᵢ = 0` for a futures-style asset). With

  `v = √(σ₁² + σ₂² − 2ρσ₁σ₂)`                          (`stulzEffVol`, the Margrabe spread vol)
  `ρ₁ = (σ₁ − ρσ₂) / v`, `ρ₂ = (σ₂ − ρσ₁) / v`          (`stulzRho1`, `stulzRho2`)
  `yᵢ = (log(Sᵢ/K) + (bᵢ + σᵢ²/2)T) / (σᵢ√T)`           (`stulzY1`, `stulzY2`)
  `d = (log(S¹/S²) + (b₁ − b₂ + v²/2)T) / (v√T)`         (`stulzD`)

the call-on-the-max and call-on-the-min prices are

  `C_max = S¹e^{(b₁−r)T} N₂(y₁, d; ρ₁) + S²e^{(b₂−r)T} N₂(y₂, −d+v√T; ρ₂)`
          `− Ke^{−rT}(1 − N₂(−y₁+σ₁√T, −y₂+σ₂√T; ρ))`,
  `C_min = S¹e^{(b₁−r)T} N₂(y₁, −d; −ρ₁) + S²e^{(b₂−r)T} N₂(y₂, d−v√T; −ρ₂)`
          `− Ke^{−rT} N₂(y₁−σ₁√T, y₂−σ₂√T; ρ)`.

## Main definitions

* `stulzEffVol`: the spread volatility `√(σ₁² + σ₂² - 2ρσ₁σ₂)`.
* `stulzRho1`, `stulzRho2`: the correlations `(σ₁ - ρσ₂)/v` and `(σ₂ - ρσ₁)/v` of each log-asset
  with the log-spread.
* `stulzY1`, `stulzY2`: the Black-Scholes `d₁` of each asset against strike `K` at its
  cost-of-carry.
* `stulzD`: the Margrabe-style `d₁` of the ratio `S¹/S²` at the spread volatility.
* `stulzCallMax`, `stulzCallMin`: the closed forms of Stulz (1982), as transcribed by Haug, for
  calls on the maximum and the minimum of two assets. That they equal discounted expected
  payoffs is not proved here.

## Main results

* `stulzRho1_sq_le_one`, `stulzRho2_sq_le_one`: `ρ₁, ρ₂` are genuine correlations (`ρᵢ² ≤ 1`)
  whenever `ρ² ≤ 1` — an algebraic fact, unconditional on `v ≠ 0` (Lean's `0/0 = 0` convention
  makes the degenerate `v = 0` case trivially satisfy it too).
* `stulz_max_min_payoff_parity`: the **payoff-level** identity behind Stulz's whole
  construction, `max(max(a,b)−K,0) + max(min(a,b)−K,0) = max(a−K,0) + max(b−K,0)` — pure
  algebra, no probability.
* `stulzCallMax_add_stulzCallMin`: the matching **price-level** identity, for `S¹, S², K > 0`
  and `ρ² ≤ 1`: `C_max + C_min` equals the sum of two *ordinary* one-asset Black-Scholes calls
  on `S¹` and `S²` (`bsVGarman`, `GarmanNormalForm.lean`). It is the price-level counterpart of
  the payoff identity, but it is not derived from it: the proof consumes only
  `bivariateNormalCDF_flip_snd` / `bivariateNormalCDF_neg_neg`, the two general bivariate-CDF
  identities of `BivariateNormalCDF.lean`, with no separate probabilistic derivation.

* `stulzD_eq_margrabeD1`: at equal costs of carry, Stulz's ratio argument `d` is Margrabe's
  `d₁` at the spread volatility `v` (`ExchangeOption.lean`).
* `tendsto_stulzCallMax_zero_strike`: as the strike `K ↓ 0`, with `b₁ = b₂ = r`, the
  call-on-the-max closed form tends to `S² + margrabePrice S¹ S² v T`, the closed-form price
  of the better-of-two payoff `max(S¹_T, S²_T) = S²_T + max(S¹_T − S²_T, 0)`. The strike
  terms `y₁, y₂ → ∞` and each `N₂(yᵢ, ·; ρᵢ)` tends to its second margin
  (`tendsto_bivariateNormalCDF_atTop_fst`). This checks `stulzD` and `stulzEffVol` against
  Margrabe's formula, which the parity identity below does not; it does not check `ρ₁`, `ρ₂`,
  which drop out in the limit.
* `tendsto_stulzCallMax_zero_strike_betterOfTwo`: in the two-GBM model of
  `MargrabeGrounding.lean`, that limit is the discounted expected better-of-two payoff
  `𝔼_P[e^{−rT}max(S¹_T, S²_T)]` (`integral_betterOfTwo`). Stulz's formula itself, for `K > 0`,
  is still not derived as an expected payoff.

**Scope.** `stulzCallMax_add_stulzCallMin` is a partial consistency check on the closed forms.
Its proof uses only `ρ₁² ≤ 1` and `ρ₂² ≤ 1`, so it holds for any values of `d`, `v`, `ρ₁`, `ρ₂`
with those bounds: it checks the strike term, `y₁`, `y₂` and that `C_min`'s arguments are the
sign flips of `C_max`'s, but not `stulzD`, `stulzEffVol`, `stulzRho1` or `stulzRho2`. It is
not a from-first-principles derivation from a joint two-GBM model — the same scope
as `GarmanNormalForm.lean`'s own specializations, which take the one-asset BS closed form as
given rather than re-deriving it from Girsanov. Deriving `C_max` itself from a bivariate
lognormal expectation is a separate, harder project (the two-asset analogue of
`MargrabeGrounding.lean`).

## References

* [R. M. Stulz, *Options on the minimum or the maximum of two risky assets: analysis and
  applications*][Stulz1982]

## Tags

rainbow option, Stulz formula, call on maximum, call on minimum, bivariate normal, Margrabe,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Real

/-- **Effective spread volatility** `v = √(σ₁² + σ₂² − 2ρσ₁σ₂)` — the same quantity as the
Margrabe effective vol (the square root of `margrabe_effective_variance`'s log-spread variance
divided by `T`). -/
noncomputable def stulzEffVol (σ1 σ2 ρ : ℝ) : ℝ :=
  √(σ1 ^ 2 + σ2 ^ 2 - 2 * ρ * σ1 * σ2)

/-- **Correlation of `Y₁ = log S¹` with the log-spread**: `ρ₁ = (σ₁ − ρσ₂) / v`. -/
noncomputable def stulzRho1 (σ1 σ2 ρ : ℝ) : ℝ :=
  (σ1 - ρ * σ2) / stulzEffVol σ1 σ2 ρ

/-- **Correlation of `Y₂ = log S²` with the log-spread**: `ρ₂ = (σ₂ − ρσ₁) / v`. -/
noncomputable def stulzRho2 (σ1 σ2 ρ : ℝ) : ℝ :=
  (σ2 - ρ * σ1) / stulzEffVol σ1 σ2 ρ

/-- **`y₁`**: the standard BS `d₁` of asset 1 against strike `K` at cost-of-carry `b₁`. -/
noncomputable def stulzY1 (S1 K b1 σ1 T : ℝ) : ℝ :=
  (Real.log (S1 / K) + (b1 + σ1 ^ 2 / 2) * T) / (σ1 * Real.sqrt T)

/-- **`y₂`**: the standard BS `d₁` of asset 2 against strike `K` at cost-of-carry `b₂`. -/
noncomputable def stulzY2 (S2 K b2 σ2 T : ℝ) : ℝ :=
  (Real.log (S2 / K) + (b2 + σ2 ^ 2 / 2) * T) / (σ2 * Real.sqrt T)

/-- **`d`**: the Margrabe-style `d₁` of the ratio `S¹/S²` at the effective spread vol `v`. -/
noncomputable def stulzD (S1 S2 b1 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  (Real.log (S1 / S2) + (b1 - b2 + stulzEffVol σ1 σ2 ρ ^ 2 / 2) * T) /
    (stulzEffVol σ1 σ2 ρ * Real.sqrt T)

/-- **Stulz's closed form for a call on the maximum of two assets**, struck at `K` — the
textbook interpretation is `𝔼[e^{−rT}max(max(S¹_T,S²_T)−K,0)]`, but that expectation identity is
not proved here (see the module docstring's "Scope" note); this `def` is only the closed-form
formula itself. -/
noncomputable def stulzCallMax (S1 S2 K r b1 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  let v := stulzEffVol σ1 σ2 ρ
  let ρ1 := stulzRho1 σ1 σ2 ρ
  let ρ2 := stulzRho2 σ1 σ2 ρ
  let y1 := stulzY1 S1 K b1 σ1 T
  let y2 := stulzY2 S2 K b2 σ2 T
  let d := stulzD S1 S2 b1 b2 σ1 σ2 ρ T
  S1 * Real.exp ((b1 - r) * T) * bivariateNormalCDF y1 d ρ1 +
    S2 * Real.exp ((b2 - r) * T) * bivariateNormalCDF y2 (-d + v * Real.sqrt T) ρ2 -
    K * Real.exp (-(r * T)) *
      (1 - bivariateNormalCDF (-y1 + σ1 * Real.sqrt T) (-y2 + σ2 * Real.sqrt T) ρ)

/-- **Stulz's closed form for a call on the minimum of two assets**, struck at `K` — the
textbook interpretation is `𝔼[e^{−rT}max(min(S¹_T,S²_T)−K,0)]`, but that expectation identity is
not proved here (see the module docstring's "Scope" note); this `def` is only the closed-form
formula itself. -/
noncomputable def stulzCallMin (S1 S2 K r b1 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  let v := stulzEffVol σ1 σ2 ρ
  let ρ1 := stulzRho1 σ1 σ2 ρ
  let ρ2 := stulzRho2 σ1 σ2 ρ
  let y1 := stulzY1 S1 K b1 σ1 T
  let y2 := stulzY2 S2 K b2 σ2 T
  let d := stulzD S1 S2 b1 b2 σ1 σ2 ρ T
  S1 * Real.exp ((b1 - r) * T) * bivariateNormalCDF y1 (-d) (-ρ1) +
    S2 * Real.exp ((b2 - r) * T) * bivariateNormalCDF y2 (d - v * Real.sqrt T) (-ρ2) -
    K * Real.exp (-(r * T)) *
      bivariateNormalCDF (y1 - σ1 * Real.sqrt T) (y2 - σ2 * Real.sqrt T) ρ

/-! ## `ρ₁`, `ρ₂` are genuine correlations -/

/-- **`ρ₁` is a genuine correlation**: `ρ₁² ≤ 1` whenever `ρ² ≤ 1`. Unconditional on
`v = stulzEffVol σ1 σ2 ρ ≠ 0`: at `v = 0`, `ρ1 = (σ1 - ρσ2) / 0 = 0` by Lean's division
convention, and `0 ≤ 1` trivially. -/
theorem stulzRho1_sq_le_one (σ1 σ2 ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) : stulzRho1 σ1 σ2 ρ ^ 2 ≤ 1 := by
  unfold stulzRho1 stulzEffVol
  have hnonneg : 0 ≤ σ1 ^ 2 + σ2 ^ 2 - 2 * ρ * σ1 * σ2 := by
    nlinarith [sq_nonneg (σ1 - ρ * σ2), mul_nonneg (sq_nonneg σ2) (sub_nonneg.2 hρ)]
  rcases hnonneg.lt_or_eq with hpos | heq
  · rw [div_pow, Real.sq_sqrt hpos.le, div_le_one hpos]
    nlinarith [mul_nonneg (sq_nonneg σ2) (sub_nonneg.2 hρ)]
  · rw [← heq, Real.sqrt_zero, div_zero]
    norm_num

/-- **`ρ₂` is a genuine correlation**: `ρ₂² ≤ 1` whenever `ρ² ≤ 1`, by the same argument as
`stulzRho1_sq_le_one` with `σ1, σ2` exchanged. -/
theorem stulzRho2_sq_le_one (σ1 σ2 ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) : stulzRho2 σ1 σ2 ρ ^ 2 ≤ 1 := by
  have h := stulzRho1_sq_le_one σ2 σ1 ρ hρ
  unfold stulzRho1 stulzEffVol at h
  unfold stulzRho2 stulzEffVol
  rwa [show σ2 ^ 2 + σ1 ^ 2 - 2 * ρ * σ2 * σ1 = σ1 ^ 2 + σ2 ^ 2 - 2 * ρ * σ1 * σ2 from by ring]
    at h

/-! ## The payoff-level parity -/

/-- **The payoff identity behind Stulz's construction**: a call on the max plus a call on the
min, both struck at `K`, pays exactly what a plain call on `a` plus a plain call on `b` pays.
Pure algebra — `rcases le_total a b` collapses `max`/`min` on each side identically. -/
theorem stulz_max_min_payoff_parity (a b K : ℝ) :
    max (max a b - K) 0 + max (min a b - K) 0 = max (a - K) 0 + max (b - K) 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h]; ring
  · rw [max_eq_left h, min_eq_right h]

/-! ## The price-level parity -/

/-- **Log-algebra bridge**: `stulzY1` matches `GarmanNormalForm`'s `gbsd1` at the cost-of-carry
parameters `A = S¹e^{(b₁−r)T}`, `DF = e^{−rT}`. Reuses `log_SexpNegQ_div_KexpNegR` (with
`q = r − b₁`, since `e^{(b₁-r)T} = e^{-((r-b₁)T)}`) rather than re-deriving the log algebra. -/
private lemma stulzY1_eq_gbsd1 (S1 K b1 σ1 T r : ℝ) (hS1 : 0 < S1) (hK : 0 < K) :
    stulzY1 S1 K b1 σ1 T =
      gbsd1 (S1 * Real.exp ((b1 - r) * T)) K (Real.exp (-(r * T))) σ1 T := by
  unfold stulzY1 gbsd1
  congr 1
  rw [show S1 * Real.exp ((b1 - r) * T) = S1 * Real.exp (-((r - b1) * T)) from by ring_nf,
    log_SexpNegQ_div_KexpNegR S1 K r (r - b1) T hS1 hK]
  ring

/-- **Log-algebra bridge** for `stulzY2`, symmetric to `stulzY1_eq_gbsd1`. -/
private lemma stulzY2_eq_gbsd1 (S2 K b2 σ2 T r : ℝ) (hS2 : 0 < S2) (hK : 0 < K) :
    stulzY2 S2 K b2 σ2 T =
      gbsd1 (S2 * Real.exp ((b2 - r) * T)) K (Real.exp (-(r * T))) σ2 T := by
  unfold stulzY2 gbsd1
  congr 1
  rw [show S2 * Real.exp ((b2 - r) * T) = S2 * Real.exp (-((r - b2) * T)) from by ring_nf,
    log_SexpNegQ_div_KexpNegR S2 K r (r - b2) T hS2 hK]
  ring

/-- **The price-level parity**: for `S¹, S², K > 0` and `ρ² ≤ 1`, `C_max + C_min` equals the
sum of two one-asset `bsVGarman` calls on `S¹` and `S²` at strike `K`, discount factor
`e^{−rT}`. The proof pairs each `N₂` term of `C_max` with its counterpart in `C_min` via
`bivariateNormalCDF_flip_snd` (asset terms) and `bivariateNormalCDF_neg_neg` (the strike term).
It is the price-level counterpart of `stulz_max_min_payoff_parity`, proved from the N₂
identities, not from the payoff lemma. It uses only `ρ₁², ρ₂² ≤ 1` of `d`, `v`, `ρ₁`, `ρ₂`, so
it does not check `stulzD`, `stulzEffVol`, `stulzRho1` or `stulzRho2`. -/
theorem stulzCallMax_add_stulzCallMin (S1 S2 K r b1 b2 σ1 σ2 T : ℝ) {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1)
    (hS1 : 0 < S1) (hS2 : 0 < S2) (hK : 0 < K) :
    stulzCallMax S1 S2 K r b1 b2 σ1 σ2 ρ T + stulzCallMin S1 S2 K r b1 b2 σ1 σ2 ρ T =
      bsVGarman (S1 * Real.exp ((b1 - r) * T)) K (Real.exp (-(r * T))) σ1 T +
        bsVGarman (S2 * Real.exp ((b2 - r) * T)) K (Real.exp (-(r * T))) σ2 T := by
  have hρ1sq := stulzRho1_sq_le_one σ1 σ2 ρ hρ
  have hρ2sq := stulzRho2_sq_le_one σ1 σ2 ρ hρ
  -- Abbreviations matching the `let`-bindings inside `stulzCallMax`/`stulzCallMin`.
  set v := stulzEffVol σ1 σ2 ρ
  set ρ1 := stulzRho1 σ1 σ2 ρ
  set ρ2 := stulzRho2 σ1 σ2 ρ
  set y1 := stulzY1 S1 K b1 σ1 T
  set y2 := stulzY2 S2 K b2 σ2 T
  set d := stulzD S1 S2 b1 b2 σ1 σ2 ρ T
  -- The three bivariate-CDF identities that collapse `C_max + C_min` term by term.
  have hasset1 : bivariateNormalCDF y1 d ρ1 + bivariateNormalCDF y1 (-d) (-ρ1) = Phi y1 :=
    bivariateNormalCDF_flip_snd y1 d hρ1sq
  have hasset2 : bivariateNormalCDF y2 (-d + v * Real.sqrt T) ρ2 +
      bivariateNormalCDF y2 (d - v * Real.sqrt T) (-ρ2) = Phi y2 := by
    have h2 := bivariateNormalCDF_flip_snd y2 (-d + v * Real.sqrt T) hρ2sq
    rwa [show -(-d + v * Real.sqrt T) = d - v * Real.sqrt T from by ring] at h2
  have hstrike : (1 - bivariateNormalCDF (-y1 + σ1 * Real.sqrt T) (-y2 + σ2 * Real.sqrt T) ρ) +
      bivariateNormalCDF (y1 - σ1 * Real.sqrt T) (y2 - σ2 * Real.sqrt T) ρ =
      Phi (y1 - σ1 * Real.sqrt T) + Phi (y2 - σ2 * Real.sqrt T) := by
    have hnn := bivariateNormalCDF_neg_neg (y1 - σ1 * Real.sqrt T) (y2 - σ2 * Real.sqrt T) hρ
    rw [show -(y1 - σ1 * Real.sqrt T) = -y1 + σ1 * Real.sqrt T from by ring,
      show -(y2 - σ2 * Real.sqrt T) = -y2 + σ2 * Real.sqrt T from by ring] at hnn
    linarith
  -- The `gbsd1` bridge, so `bsVGarman`'s own `d₁` matches `y1`/`y2` exactly.
  have hgbsd1 : gbsd1 (S1 * Real.exp ((b1 - r) * T)) K (Real.exp (-(r * T))) σ1 T = y1 :=
    (stulzY1_eq_gbsd1 S1 K b1 σ1 T r hS1 hK).symm
  have hgbsd2 : gbsd1 (S2 * Real.exp ((b2 - r) * T)) K (Real.exp (-(r * T))) σ2 T = y2 :=
    (stulzY2_eq_gbsd1 S2 K b2 σ2 T r hS2 hK).symm
  simp only [stulzCallMax, stulzCallMin, bsVGarman, gbsd2, hgbsd1, hgbsd2]
  linear_combination (S1 * Real.exp ((b1 - r) * T)) * hasset1 +
    (S2 * Real.exp ((b2 - r) * T)) * hasset2 - (K * Real.exp (-(r * T))) * hstrike

/-! ## Zero strike: the better-of-two option through Margrabe -/

/-- **Stulz's `d` is Margrabe's `d₁`** at equal costs of carry `b₁ = b₂`, with the spread
volatility `v = stulzEffVol σ₁ σ₂ ρ`. -/
lemma stulzD_eq_margrabeD1 (S1 S2 b σ1 σ2 ρ T : ℝ) :
    stulzD S1 S2 b b σ1 σ2 ρ T = margrabeD1 S1 S2 (stulzEffVol σ1 σ2 ρ) T := by
  unfold stulzD margrabeD1
  congr 1
  ring

open Filter Topology in
/-- As the strike falls to `0`, `y₁ → +∞`: `log(S₁/K) → +∞`. -/
lemma tendsto_stulzY1_zero_strike {S1 b1 σ1 T : ℝ} (hS1 : 0 < S1) (hσ1 : 0 < σ1) (hT : 0 < T) :
    Tendsto (fun K ↦ stulzY1 S1 K b1 σ1 T) (𝓝[>] 0) atTop := by
  have hlog : Tendsto (fun K ↦ Real.log (S1 / K)) (𝓝[>] 0) atTop := by
    refine (tendsto_atTop_add_const_left _ (Real.log S1)
      (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with K hK
    rw [Function.comp_apply, Real.log_div hS1.ne' (Set.mem_Ioi.mp hK).ne', sub_eq_add_neg]
  change Tendsto (fun K ↦ (Real.log (S1 / K) + (b1 + σ1 ^ 2 / 2) * T) / (σ1 * Real.sqrt T)) _ _
  exact (tendsto_atTop_add_const_right _ _ hlog).atTop_div_const
    (mul_pos hσ1 (Real.sqrt_pos.mpr hT))

open Filter Topology in
/-- As the strike falls to `0`, `y₂ → +∞` (`y₂` has the shape of `y₁`). -/
lemma tendsto_stulzY2_zero_strike {S2 b2 σ2 T : ℝ} (hS2 : 0 < S2) (hσ2 : 0 < σ2) (hT : 0 < T) :
    Tendsto (fun K ↦ stulzY2 S2 K b2 σ2 T) (𝓝[>] 0) atTop :=
  tendsto_stulzY1_zero_strike (b1 := b2) hS2 hσ2 hT

open Filter Topology in
/-- **Stulz's call on the maximum at zero strike is the better-of-two price.** With equal
costs of carry `b₁ = b₂ = r`, as `K ↓ 0` the closed form `stulzCallMax` tends to
`S² + margrabePrice S¹ S² v T`, `v = stulzEffVol σ₁ σ₂ ρ`: the closed-form price of
`max(S¹_T, S²_T) = S²_T + max(S¹_T − S²_T, 0)` (Margrabe's exchange option plus one unit of
`S²`). This is a statement about the closed forms; neither is derived here as an expected
payoff. -/
theorem tendsto_stulzCallMax_zero_strike {S1 S2 r σ1 σ2 ρ T : ℝ} (hS1 : 0 < S1) (hS2 : 0 < S2)
    (hσ1 : 0 < σ1) (hσ2 : 0 < σ2) (hT : 0 < T) :
    Tendsto (fun K ↦ stulzCallMax S1 S2 K r r r σ1 σ2 ρ T) (𝓝[>] 0)
      (𝓝 (S2 + margrabePrice S1 S2 (stulzEffVol σ1 σ2 ρ) T)) := by
  -- the two asset terms: `N₂(yᵢ, ·; ρᵢ)` tends to its second margin as `yᵢ → ∞`
  have h1 : Tendsto (fun K ↦ S1 * bivariateNormalCDF (stulzY1 S1 K r σ1 T)
      (margrabeD1 S1 S2 (stulzEffVol σ1 σ2 ρ) T) (stulzRho1 σ1 σ2 ρ)) (𝓝[>] 0)
      (𝓝 (S1 * Phi (margrabeD1 S1 S2 (stulzEffVol σ1 σ2 ρ) T))) :=
    ((tendsto_bivariateNormalCDF_atTop_fst _ _).comp
      (tendsto_stulzY1_zero_strike hS1 hσ1 hT)).const_mul S1
  have h2 : Tendsto (fun K ↦ S2 * bivariateNormalCDF (stulzY2 S2 K r σ2 T)
      (-margrabeD1 S1 S2 (stulzEffVol σ1 σ2 ρ) T + stulzEffVol σ1 σ2 ρ * Real.sqrt T)
      (stulzRho2 σ1 σ2 ρ)) (𝓝[>] 0)
      (𝓝 (S2 * Phi (-margrabeD1 S1 S2 (stulzEffVol σ1 σ2 ρ) T +
        stulzEffVol σ1 σ2 ρ * Real.sqrt T))) :=
    ((tendsto_bivariateNormalCDF_atTop_fst _ _).comp
      (tendsto_stulzY2_zero_strike hS2 hσ2 hT)).const_mul S2
  -- the strike term vanishes: `K e^{−rT}` times a number in `[0, 1]`
  have hKe : Tendsto (fun K : ℝ ↦ K * Real.exp (-(r * T))) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi 0)
      (tendsto_id : Tendsto id (𝓝 (0 : ℝ)) (𝓝 0))).mul_const (Real.exp (-(r * T)))
  have h3 : Tendsto (fun K ↦ K * Real.exp (-(r * T)) *
      (1 - bivariateNormalCDF (-stulzY1 S1 K r σ1 T + σ1 * Real.sqrt T)
        (-stulzY2 S2 K r σ2 T + σ2 * Real.sqrt T) ρ)) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hKe
    filter_upwards [self_mem_nhdsWithin] with K hK
    have hK0 : 0 < K * Real.exp (-(r * T)) := mul_pos (Set.mem_Ioi.mp hK) (Real.exp_pos _)
    have hN0 : 0 ≤ bivariateNormalCDF (-stulzY1 S1 K r σ1 T + σ1 * Real.sqrt T)
        (-stulzY2 S2 K r σ2 T + σ2 * Real.sqrt T) ρ := MeasureTheory.measureReal_nonneg
    have hN1 : bivariateNormalCDF (-stulzY1 S1 K r σ1 T + σ1 * Real.sqrt T)
        (-stulzY2 S2 K r σ2 T + σ2 * Real.sqrt T) ρ ≤ 1 := MeasureTheory.measureReal_le_one
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hK0, abs_of_nonneg (sub_nonneg.mpr hN1)]
    exact mul_le_of_le_one_right hK0.le (sub_le_self _ hN0)
  -- the limit `S¹Φ(d₁) + S²Φ(−d₁ + v√T)` is `S² + Margrabe`, since `−d₁ + v√T = −d₂`
  have hlim : S1 * Phi (margrabeD1 S1 S2 (stulzEffVol σ1 σ2 ρ) T) +
      S2 * Phi (-margrabeD1 S1 S2 (stulzEffVol σ1 σ2 ρ) T + stulzEffVol σ1 σ2 ρ * Real.sqrt T)
        - 0 = S2 + margrabePrice S1 S2 (stulzEffVol σ1 σ2 ρ) T := by
    rw [show -margrabeD1 S1 S2 (stulzEffVol σ1 σ2 ρ) T + stulzEffVol σ1 σ2 ρ * Real.sqrt T
        = -margrabeD2 S1 S2 (stulzEffVol σ1 σ2 ρ) T by rw [margrabeD2]; ring, Phi_neg]
    unfold margrabePrice
    ring
  rw [← hlim]
  refine ((h1.add h2).sub h3).congr fun K ↦ ?_
  simp only [stulzCallMax, stulzD_eq_margrabeD1, sub_self, zero_mul, Real.exp_zero, mul_one]

open Filter Topology MeasureTheory ProbabilityTheory in
/-- **Stulz's call on the maximum at zero strike is the expected better-of-two payoff.** For
two Black–Scholes terminals driven by a jointly Gaussian pair of standard normals with
covariance `ρ` and a non-degenerate spread variance, the closed form `stulzCallMax` with
`b₁ = b₂ = r` tends, as `K ↓ 0`, to `𝔼_P[e^{−rT}·max(S¹_T, S²_T)]`
(`tendsto_stulzCallMax_zero_strike` and `integral_betterOfTwo`). -/
theorem tendsto_stulzCallMax_zero_strike_betterOfTwo {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {W₁ W₂ : Ω → ℝ} {S1 S2 r σ1 σ2 ρ T : ℝ}
    (hjoint : HasGaussianLaw (fun ω ↦ (W₁ ω, W₂ ω)) P)
    (hW₁meas : Measurable W₁) (hW₂meas : Measurable W₂)
    (hW₁ : HasLaw W₁ (gaussianReal 0 1) P) (hW₂ : HasLaw W₂ (gaussianReal 0 1) P)
    (hcov : cov[W₁, W₂; P] = ρ) (hS1 : 0 < S1) (hS2 : 0 < S2) (hσ1 : 0 < σ1) (hσ2 : 0 < σ2)
    (hT : 0 < T) (hv : 0 < σ1 ^ 2 + σ2 ^ 2 - 2 * ρ * σ1 * σ2) :
    Tendsto (fun K ↦ stulzCallMax S1 S2 K r r r σ1 σ2 ρ T) (𝓝[>] 0)
      (𝓝 (∫ ω, Real.exp (-(r * T)) *
        max (bsTerminal S1 r σ1 T (W₁ ω)) (bsTerminal S2 r σ2 T (W₂ ω)) ∂P)) := by
  rw [integral_betterOfTwo hjoint hW₁meas hW₂meas hW₁ hW₂ hcov hS1 hS2 hσ2
    (Real.sqrt_pos.mpr hv) hT (Real.sq_sqrt hv.le)]
  exact tendsto_stulzCallMax_zero_strike hS1 hS2 hσ1 hσ2 hT

end MathFin
