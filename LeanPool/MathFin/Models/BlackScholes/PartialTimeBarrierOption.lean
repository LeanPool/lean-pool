/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.HeynenKatTwoAssetBarrier

/-!
# Partial-time barrier options (start window, call): Haug's closed form

A barrier that is monitored only on part of the option's life. This file covers the **start**
window, **call** side (QuantLib's `PartialBarrier::Start`, `Option::Call`): the barrier is live
on `[0, t₁]` and switched off for the remainder `(t₁, T]` of the option's life (Haug's
"Partial-Time Single-Asset Barrier Options", full citation below). Unlike the binary barrier
transcribed alongside this file, this genuinely needs the **bivariate** normal
CDF — the barrier-monitoring window `[0, t₁]` and the full life `[0, T]` are correlated
(correlation `ρ = √(t₁/T)`, the two Brownian increments share the `[0, t₁]` leg) — which is why
this file builds on the same `BivariateNormalCDF.lean` substrate (`bivariateNormalCDF`,
`bivariateNormalCDF_flip_snd`) as `HeynenKatTwoAssetBarrier.lean`. Sources for the closed
form: Heynen & Kat, "Partial barrier options", *Journal of Financial Engineering* 3 (1994);
Haug, *The Complete Guide to Option Pricing Formulas*, 2nd ed. (2007), ch. 4, "Partial-Time
Single-Asset Barrier Options" (the `A`-value table the engine's `CA` transcribes).

**Scope, disclosed honestly**: QuantLib's `AnalyticPartialTimeBarrierOptionEngine` also prices
the **end**-window case (`PartialBarrier::EndB1`/`EndB2`, barrier live only on `(t₁, T]`) via
`CoB1`/`CoB2`, which are substantially more involved (each has its own strike-vs-barrier case
split with extra vanilla-minus-partial decompositions) and genuinely harder; this file formalizes
the **start**-window case (`CA`, QuantLib's simplest of the three) and leaves `EndB1`/`EndB2` out
of scope. **`CA` is also call-only**: QuantLib's `CA` is commented
`//Partial-Time-Start- OUT  Call Option calculation`, and the engine prices a *put* in
`calculate()` via the put–call spot-reflection symmetry (strike `X ↦ S²/X`, barrier `H ↦ S²/H`,
barrier direction mirrored, the `CA`-call result on the transformed inputs scaled by `X/S`) rather
than a second closed form — that symmetry transform is not formalized here either. The knock-in
case (`CIA = vanilla − CA`) is in–out parity — the closed-form counterpart of
`BarrierParity.lean`'s `knockIn_add_knockOut_eq_vanilla` (the barrier-hit event and its
complement partition the payoff) — rather than an independent closed form, so it is not
separately formalized.

Transcribed from QuantLib's
`ql/pricingengines/barrier/analyticpartialtimebarrieroptionengine.cpp` (`CA`, upstream commit
`5f4811e`, 2026-10-16; contributed 2014 by Polytech'Nice Sophia Antipolis). We adopt a single
constant volatility `σ` (QuantLib's engine reads a possibly term-structured Black vol evaluated
at `t₁` for `μ` and the `e`-terms and at `T` for the `d`/`f`-terms; Haug's original textbook
closed form, which this transcribes, uses one constant `σ` throughout — the flat-vol case
QuantLib's more general engine specializes to).

With cost-of-carry `b = r − q`, `ρ = √(t₁/T)`, `μ = (b − σ²/2)/σ²`, and

  `d₁ = (log(S/X) + (b+σ²/2)T)/(σ√T)`,  `d₂ = d₁ − σ√T`,
  `e₁ = (log(S/H) + (b+σ²/2)t₁)/(σ√t₁)`,  `e₂ = e₁ − σ√t₁`,
  `e₃ = e₁ + 2log(H/S)/(σ√t₁)`,  `e₄ = e₃ − σ√t₁`,
  `f₁ = (log(S/X) + 2log(H/S) + (b+σ²/2)T)/(σ√T)`,  `f₂ = f₁ − σ√T`,

and `(H/S)^{2μ}`, `(H/S)^{2(μ+1)}` as `exp(·log·)` (as in `BinaryBarrierOption.lean` and
`HeynenKatTwoAssetBarrier.lean`), the
start-window out-barrier **call** value (`η = 1` down, `η = −1` up) is

  `CA(η) = S·e^{(b−r)T}·(N₂(d₁, ηe₁; ηρ) − (H/S)^{2(μ+1)}·N₂(f₁, ηe₃; ηρ))`
         `− X·e^{−rT}·(N₂(d₂, ηe₂; ηρ) − (H/S)^{2μ}·N₂(f₂, ηe₄; ηρ))`.

## Main definitions

* `ptRho`: `ρ = √(t₁/T)`, the correlation between the barrier-window and full-life log-returns.
* `ptMu`: `μ = (b − σ²/2)/σ²`, the drift parameter of the barrier formulas.
* `ptD1`, `ptD2`: the Black–Scholes `d₁`, `d₂` with cost of carry `b` against the strike `X` over
  the full life `T`.
* `ptE1`, `ptE2`, `ptE3`, `ptE4`: the corresponding quantities against the barrier `H` over the
  monitoring window `t₁`, with `ptE3`, `ptE4` carrying the barrier reflection term.
* `ptF1`, `ptF2`: `d₁` and `d₂` shifted by the barrier reflection term over the full life `T`.
* `ptCA`: the partial-time-start barrier call closed form `CA(η)` (`η = 1` down, `η = −1` up),
  Haug's expression with the barrier live on `[0, t₁]`; not proved to be a discounted expected
  payoff.
* `ptDownOutCall`: the full-life down-and-out call closed form (Rubinstein–Reiner), as transcribed
  in this file.

## Main results

* `ptCA_down_add_up`: **`CA(1) + CA(−1)` collapses to a closed form with no bivariate CDF left**
  — every `N₂(a, ηb; ηρ)` pair (`η = ±1`) telescopes via `bivariateNormalCDF_flip_snd` to a
  single `Φ(a)`, exactly the mechanism behind `HeynenKatTwoAssetBarrier.lean`'s
  `heynenKat_downOut_add_upOut`. As there, the down/up window-start prices are mutually exclusive
  regimes (down-monitored vs. up-monitored), so the sum itself is not a payoff decomposition;
  what the identity shows is that the sum is `t₁`-free — it equals `ptDownOutCall`, the
  transcribed full-life down-and-out call closed form (the `X ≥ H` branch), for every
  `0 ≤ t₁ ≤ T`, not only in some limit. It verifies the `(ηe_i, ηρ)` sign pattern is
  self-consistent across `η = ±1`, the same scope the Heynen–Kat file disclosed for its own
  analogous check.

* `ptCA_down_monitored_full_life`: **monitoring over the whole life gives the full-life
  closed form** — at `t₁ = T` (with `X ≥ H`), the correlation `ρ = 1` degenerates each
  `N₂(a, ηb; ηρ)` to
  `Φ(min(a, ηb))` via `bivariateNormalCDF_one`, and `X ≥ H` orders every such pair so the `d`/`f`
  term is the minimum, reducing `CA(1)` directly to `ptDownOutCall`, the closed form
  `ptCA_down_add_up` reaches.
  Both are identities between transcribed closed forms; neither is proved to be a price.

## References

* [Haug, *The Complete Guide to Option Pricing Formulas*][Haug2007], ch. 4
* [Heynen and Kat, *Partial barrier options*][HeynenKat1994b]

## Tags

partial barrier option, Heynen–Kat, Haug closed form, barrier monitoring window, bivariate normal,
knock-out call, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

/-- **`ρ = √(t₁/T)`**, the correlation between the barrier-window and full-life log-returns. -/
noncomputable def ptRho (t1 T : ℝ) : ℝ := Real.sqrt (t1 / T)

/-- **`μ = (b − σ²/2)/σ²`** — `hkMu`'s drift (`HeynenKatTwoAssetBarrier.lean`) divided by
`σ²`, the same `hkMu`-style parameter the binary barrier's `mu` takes. -/
noncomputable def ptMu (b σ : ℝ) : ℝ := hkMu b σ / σ ^ 2

/-- **`d₁`**: the standard BS `d₁` (`bsd1`, `Models/BlackScholes/Call.lean`) with the cost-of-carry
`b` in the rate slot, against strike `X` over the full life `T`. -/
noncomputable def ptD1 (S X b σ T : ℝ) : ℝ := bsd1 S X b σ T

/-- **`d₂`** = `bsd2 S X b σ T` — `d₁ − σ√T`. -/
noncomputable def ptD2 (S X b σ T : ℝ) : ℝ := bsd2 S X b σ T

/-- **`e₁`**: `bsd1` against the barrier `H` over the monitoring window `t₁`. -/
noncomputable def ptE1 (S H b σ t1 : ℝ) : ℝ := bsd1 S H b σ t1

/-- **`e₂` = `e₁ − σ√t₁`** = `bsd2 S H b σ t₁`. -/
noncomputable def ptE2 (S H b σ t1 : ℝ) : ℝ := bsd2 S H b σ t1

/-- **`e₃`**: `e₁` shifted by the barrier reflection term. -/
noncomputable def ptE3 (S H b σ t1 : ℝ) : ℝ :=
  ptE1 S H b σ t1 + 2 * Real.log (H / S) / (σ * Real.sqrt t1)

/-- **`e₄` = `e₃ − σ√t₁`**. -/
noncomputable def ptE4 (S H b σ t1 : ℝ) : ℝ := ptE3 S H b σ t1 - σ * Real.sqrt t1

/-- **`f₁`**: `d₁` shifted by the barrier reflection term (over the full life `T`). -/
noncomputable def ptF1 (S X H b σ T : ℝ) : ℝ :=
  (Real.log (S / X) + 2 * Real.log (H / S) + (b + σ ^ 2 / 2) * T) / (σ * Real.sqrt T)

/-- **`f₂` = `f₁ − σ√T`**. -/
noncomputable def ptF2 (S X H b σ T : ℝ) : ℝ := ptF1 S X H b σ T - σ * Real.sqrt T

/-- **`(H/S)^{2μ}`**, written as `exp(·log·)`. -/
noncomputable def ptHSmu (S H b σ : ℝ) : ℝ := Real.exp (2 * ptMu b σ * Real.log (H / S))

/-- **`(H/S)^{2(μ+1)}`**. -/
noncomputable def ptHSmu1 (S H b σ : ℝ) : ℝ := Real.exp (2 * (ptMu b σ + 1) * Real.log (H / S))

/-- **Partial-time-start barrier call value** `CA(η)` (QuantLib's
`AnalyticPartialTimeBarrierOptionEngine::CA`; `η = 1` down, `η = −1` up; call-only — see the
module docstring's "Scope" paragraph for how QuantLib prices the put side instead). -/
noncomputable def ptCA (eta S X H b r σ t1 T : ℝ) : ℝ :=
  S * Real.exp ((b - r) * T) *
      (bivariateNormalCDF (ptD1 S X b σ T) (eta * ptE1 S H b σ t1) (eta * ptRho t1 T)
        - ptHSmu1 S H b σ *
            bivariateNormalCDF (ptF1 S X H b σ T) (eta * ptE3 S H b σ t1) (eta * ptRho t1 T))
    - X * Real.exp (-r * T) *
        (bivariateNormalCDF (ptD2 S X b σ T) (eta * ptE2 S H b σ t1) (eta * ptRho t1 T)
          - ptHSmu S H b σ *
              bivariateNormalCDF (ptF2 S X H b σ T) (eta * ptE4 S H b σ t1) (eta * ptRho t1 T))

/-- **The full-life down-and-out call closed form** (Rubinstein & Reiner (1991); Haug (2007),
ch. 4, the `X ≥ H` branch), transcribed: the barrier monitored over all of `[0, T]`. It is a
closed-form expression here, not proved to be the expected discounted knock-out payoff. -/
noncomputable def ptDownOutCall (S X H b r σ T : ℝ) : ℝ :=
  S * Real.exp ((b - r) * T) *
      (Phi (ptD1 S X b σ T) - ptHSmu1 S H b σ * Phi (ptF1 S X H b σ T))
    - X * Real.exp (-r * T) *
        (Phi (ptD2 S X b σ T) - ptHSmu S H b σ * Phi (ptF2 S X H b σ T))

/-- `ρ² ≤ 1` whenever `0 ≤ t₁ ≤ T` — the hypothesis `bivariateNormalCDF_flip_snd` needs, since
a monitoring window can only be a sub-interval of the option's life. -/
theorem ptRho_sq_le_one {t1 T : ℝ} (ht1 : 0 ≤ t1) (hT : t1 ≤ T) : ptRho t1 T ^ 2 ≤ 1 := by
  have hT0 : 0 ≤ T := ht1.trans hT
  rw [ptRho, Real.sq_sqrt (div_nonneg ht1 hT0)]
  exact div_le_one_of_le₀ hT hT0

/-- **Down-window plus up-window, same strike/barrier**: `CA(1) + CA(−1)` collapses to a closed
form with every bivariate CDF replaced by a single `Φ`, via `bivariateNormalCDF_flip_snd` applied
to each of the four `N₂` pairs (see the module docstring for the scope this checks). -/
theorem ptCA_down_add_up (S X H b r σ t1 T : ℝ) (ht1 : 0 ≤ t1) (hT : t1 ≤ T) :
    ptCA 1 S X H b r σ t1 T + ptCA (-1) S X H b r σ t1 T = ptDownOutCall S X H b r σ T := by
  have hr : ptRho t1 T ^ 2 ≤ 1 := ptRho_sq_le_one ht1 hT
  have hd1 := bivariateNormalCDF_flip_snd (ptD1 S X b σ T) (ptE1 S H b σ t1) hr
  have hf1 := bivariateNormalCDF_flip_snd (ptF1 S X H b σ T) (ptE3 S H b σ t1) hr
  have hd2 := bivariateNormalCDF_flip_snd (ptD2 S X b σ T) (ptE2 S H b σ t1) hr
  have hf2 := bivariateNormalCDF_flip_snd (ptF2 S X H b σ T) (ptE4 S H b σ t1) hr
  simp only [ptCA, ptDownOutCall, one_mul, neg_one_mul]
  linear_combination S * Real.exp ((b - r) * T) * hd1
    - S * Real.exp ((b - r) * T) * ptHSmu1 S H b σ * hf1
    - X * Real.exp (-r * T) * hd2 + X * Real.exp (-r * T) * ptHSmu S H b σ * hf2

/-- **Monitoring over the whole life gives the full-life closed form.** With the barrier live on
`[0, T]` (i.e. `t₁ = T`) and the strike dominating the barrier (`X ≥ H`, the branch where the
down-and-out closed form holds without a min inside the payoff), the start-window value
`ptCA 1 … T T` reduces to `ptDownOutCall`, the transcribed full-life down-and-out call closed form —
the same `t₁`-free expression `ptCA_down_add_up` collapses to, here obtained directly: the
correlation `ptRho T T = 1`, so `bivariateNormalCDF_one` turns each `N₂(a, b; 1)` into
`Φ(min(a, b))`, and `X ≥ H` makes `d₁ ≤ e₁`, `f₁ ≤ e₃`, `d₂ ≤ e₂`, `f₂ ≤ e₄` (each pair differs
exactly by `log(S/X) ≤ log(S/H)` over the same positive denominator), so every min is the `d`/ `f`
term. -/
theorem ptCA_down_monitored_full_life (S X H b r σ T : ℝ) (hS : 0 < S) (hX : 0 < X)
    (hH : 0 < H) (hXH : H ≤ X) (hσ : 0 < σ) (hT : 0 < T) :
    ptCA 1 S X H b r σ T T = ptDownOutCall S X H b r σ T := by
  have hsqrt : 0 < σ * Real.sqrt T := mul_pos hσ (Real.sqrt_pos.mpr hT)
  have hSdX : 0 < S / X := div_pos hS hX
  have hSdH : 0 < S / H := div_pos hS hH
  have hlog : Real.log (S / X) ≤ Real.log (S / H) :=
    (Real.log_le_log_iff hSdX hSdH).mpr (by field_simp; linarith)
  -- every `(d/e, f/e)` pair differs exactly by `log(S/X) ≤ log(S/H)` over the same
  -- positive denominator `σ√T` (with `X ≥ H`), so `div_le_iff₀` reduces each to `hlog`
  have hd1e1 : ptD1 S X b σ T ≤ ptE1 S H b σ T := by
    unfold ptD1 ptE1 bsd1
    rw [div_le_iff₀ hsqrt, div_mul_eq_mul_div, mul_div_cancel_right₀ _ hsqrt.ne']
    linarith
  have hF1decomp : ptF1 S X H b σ T
      = ptD1 S X b σ T + 2 * Real.log (H / S) / (σ * Real.sqrt T) := by
    simp only [ptF1, ptD1, bsd1]
    rw [add_div, add_div]
    ring
  have hf1e3 : ptF1 S X H b σ T ≤ ptE3 S H b σ T := by
    rw [hF1decomp]
    simp only [ptE3]
    linarith [hd1e1]
  have hd2e2 : ptD2 S X b σ T ≤ ptE2 S H b σ T := by
    unfold ptD2 ptE2
    exact sub_le_sub_right hd1e1 _
  have hf2e4 : ptF2 S X H b σ T ≤ ptE4 S H b σ T := by
    unfold ptF2 ptE4
    exact sub_le_sub_right hf1e3 _
  have hrho : ptRho T T = 1 := by
    unfold ptRho
    rw [div_self hT.ne', Real.sqrt_one]
  have hD1 := bivariateNormalCDF_one (ptD1 S X b σ T) (ptE1 S H b σ T)
  have hF1 := bivariateNormalCDF_one (ptF1 S X H b σ T) (ptE3 S H b σ T)
  have hD2 := bivariateNormalCDF_one (ptD2 S X b σ T) (ptE2 S H b σ T)
  have hF2 := bivariateNormalCDF_one (ptF2 S X H b σ T) (ptE4 S H b σ T)
  simp only [ptCA, ptDownOutCall, one_mul, hrho, hD1, hF1, hD2, hF2,
    min_eq_left hd1e1, min_eq_left hf1e3, min_eq_left hd2e2, min_eq_left hf2e4]

end MathFin
