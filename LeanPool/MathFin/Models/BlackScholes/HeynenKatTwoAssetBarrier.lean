/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Gaussian.BivariateNormalCDF
public import LeanPool.MathFin.Models.BlackScholes.PutGreeks

/-!
# Heynen & Kat two-asset barrier option: the closed form

A barrier option on asset 1, struck at `X`, but **knocked out by asset 2** crossing a barrier
`H`: R. Heynen and H. Kat, "Crossing barriers", *Risk* 7(6) (1994), in the cost-of-carry form
of E. G. Haug, *The Complete Guide to Option Pricing Formulas*, 2nd ed., McGraw-Hill (2007).
Needs the bivariate normal CDF (same substrate as `StulzTwoAssetRainbow.lean`).

With `μ(b, σ) = b − σ²/2` (`hkMu`) and, for asset 1 against strike `X` and asset 2 against
barrier `H`,

  `d₁ = (log(S₁/X) + (μ(b₁,σ₁) + σ₁²)T) / (σ₁√T)`,  `d₂ = d₁ − σ₁√T`,
  `d₃ = d₁ + 2ρ·log(H/S₂)/(σ₂√T)`,  `d₄ = d₂ + 2ρ·log(H/S₂)/(σ₂√T)`,
  `e₁ = (log(H/S₂) − (μ(b₂,σ₂) + ρσ₁σ₂)T) / (σ₂√T)`,  `e₂ = e₁ + ρσ₁√T`,
  `e₃ = e₁ − 2·log(H/S₂)/(σ₂√T)`,  `e₄ = e₂ − 2·log(H/S₂)/(σ₂√T)`,

(so `d₁` carries the drift `b₁ + σ₁²/2`, the standard Black–Scholes `d₁`), the knock-out value
(`heynenKatA`, `A(η, φ)`; `η = 1` call / `η = -1` put, `φ = -1` down / `φ = 1` up) is

  `A(η,φ) = ηS₁e^{(b₁−r)T}(N₂(ηd₁,φe₁;−ηφρ) − e^{2(μ(b₂,σ₂)+ρσ₁σ₂)log(H/S₂)/σ₂²}N₂(ηd₃,φe₃;−ηφρ))`
          `− ηXe^{−rT}(N₂(ηd₂,φe₂;−ηφρ) − e^{2μ(b₂,σ₂)log(H/S₂)/σ₂²}N₂(ηd₄,φe₄;−ηφρ))`,

and the four knock-out prices are `A(1,-1)` (down-out call), `A(1,1)` (up-out call),
`A(-1,-1)` (down-out put), `A(-1,1)` (up-out put).

## Main definitions

* `hkMu`: the risk-neutral log-drift `μ(b, σ) = b − σ²/2`.
* `hkD1`, `hkD2`, `hkD3`, `hkD4`, `hkE1`, `hkE2`, `hkE3`, `hkE4`: the arguments `d₁, …, d₄`,
  `e₁, …, e₄` of the bivariate normal CDFs. `d₁, d₂` are the Black–Scholes arguments of asset 1
  against the strike `X`, and `d₃, d₄, e₃, e₄` carry the barrier-reflection shifts.
* `heynenKatA`: Heynen and Kat's knock-out value `A(η, φ)` of an option on asset 1 knocked out
  when asset 2 crosses the barrier `H`, as a closed-form definition. That it is a discounted
  expected payoff is not proved.

## Main results

* `heynenKatA_rho_zero`, the module's structural result: for independent assets (`ρ = 0`) every
  `N₂` factors (`bivariateNormalCDF_zero`), and the knock-out value is the one-asset
  Black–Scholes value of the option on `S¹` (cost-of-carry form) times the barrier factor
  `Φ(φe₁) − e^{2μ(b₂,σ₂)log(H/S₂)/σ₂²} Φ(φe₃)` of `S²`. That factor is the single-asset
  reflection-principle formula for the probability that `S²` does not cross `H`; the
  probabilistic reading is not proved here, and the comparison with the one-asset formula
  (which checks `e₁`, `e₃` and the reflection exponent) is by inspection — that formula is not
  in the library.
* `heynenKatA_call_rho_zero_eq_bsV`, `heynenKatA_put_rho_zero_eq_bsP`: at `ρ = 0` and
  `b₁ = r` (asset 1 pays no dividend), that one-asset factor is the library's Black–Scholes
  call `bsV` (put `bsP`), since `hkD1`, `hkD2` are then `bsd1`, `bsd2`. So the independent
  knock-out value is `bsV · (barrier factor)`; the barrier factor is still a transcription.
* `heynenKat_downOut_add_upOut`: for a fixed option type `η` (`η² = 1`) and `ρ² ≤ 1`, the
  down-out and up-out values sum to a closed form with no `N₂` left: each pair
  `N₂(ηdᵢ, φeᵢ; −ηφρ)`, `φ = ±1`, collapses via `bivariateNormalCDF_flip_snd` to `Φ(ηdᵢ)`.
  It holds for any arguments `dᵢ, eᵢ`, so it
  checks only that `φ` enters as `(φeᵢ, −ηφρ)`; and the sum has no payoff meaning, since the two
  formulas apply to the disjoint regimes `S₂ > H` and `S₂ < H`.

**Scope.** This module transcribes the closed form and proves the two identities above; it does
not derive the formula as a discounted expected payoff. That needs the joint law of one GBM and
the running extremum of a correlated second one, which the library does not have (the discrete
reflection principle is `Models/Binomial/BarrierReflection.lean`). Knock-in values are not stated:
they
follow from in–out parity (`knockIn_add_knockOut_eq_vanilla`,
`Models/BlackScholes/BarrierParity.lean`)
once `heynenKatA` is identified with a discounted expected payoff, which this module does not do.

## References

* [R. Heynen and H. Kat, *Crossing barriers*][HeynenKat1994a]

## Tags

two-asset barrier option, Heynen–Kat, bivariate normal, knock-out barrier, exotic option,
cost of carry, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Real

/-- **Risk-neutral log-drift** `μ(b, σ) = b − σ²/2`. -/
noncomputable def hkMu (b σ : ℝ) : ℝ := b - σ ^ 2 / 2

/-- **`d₁`**: the standard BS `d₁` of asset 1 against strike `X` at cost-of-carry `b₁`. -/
noncomputable def hkD1 (S1 X b1 σ1 T : ℝ) : ℝ :=
  (Real.log (S1 / X) + (hkMu b1 σ1 + σ1 ^ 2) * T) / (σ1 * Real.sqrt T)

/-- **`d₂` = `d₁ − σ₁√T`**. -/
noncomputable def hkD2 (S1 X b1 σ1 T : ℝ) : ℝ :=
  hkD1 S1 X b1 σ1 T - σ1 * Real.sqrt T

/-- **`d₃`**: `d₁` shifted by the asset-2/barrier correlation term. -/
noncomputable def hkD3 (S1 X H S2 b1 σ1 σ2 ρ T : ℝ) : ℝ :=
  hkD1 S1 X b1 σ1 T + 2 * ρ * Real.log (H / S2) / (σ2 * Real.sqrt T)

/-- **`d₄`**: `d₂` shifted by the same correlation term as `d₃`. -/
noncomputable def hkD4 (S1 X H S2 b1 σ1 σ2 ρ T : ℝ) : ℝ :=
  hkD2 S1 X b1 σ1 T + 2 * ρ * Real.log (H / S2) / (σ2 * Real.sqrt T)

/-- **`e₁`**: the "distance" of the barrier `H` from asset 2, at cost-of-carry `b₂`, correlation
`ρ` to asset 1. -/
noncomputable def hkE1 (H S2 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  (Real.log (H / S2) - (hkMu b2 σ2 + ρ * σ1 * σ2) * T) / (σ2 * Real.sqrt T)

/-- **`e₂` = `e₁ + ρσ₁√T`**. -/
noncomputable def hkE2 (H S2 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  hkE1 H S2 b2 σ1 σ2 ρ T + ρ * σ1 * Real.sqrt T

/-- **`e₃`**: `e₁` shifted by the barrier reflection term. -/
noncomputable def hkE3 (H S2 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  hkE1 H S2 b2 σ1 σ2 ρ T - 2 * Real.log (H / S2) / (σ2 * Real.sqrt T)

/-- **`e₄`**: `e₂` shifted by the same barrier reflection term as `e₃`. -/
noncomputable def hkE4 (H S2 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  hkE2 H S2 b2 σ1 σ2 ρ T - 2 * Real.log (H / S2) / (σ2 * Real.sqrt T)

/-- **Heynen & Kat's knock-out value `A(η, φ)`**, as a closed-form definition (that it is the
discounted expected payoff is not proved here). `η = 1` is a call on asset 1, `η = -1` a put;
`φ = -1` is a down-barrier (on asset 2), `φ = 1` an up-barrier. The four knock-out prices are
`A(1,-1)`, `A(1,1)`, `A(-1,-1)`, `A(-1,1)`. -/
noncomputable def heynenKatA (eta phi S1 S2 X H T r b1 b2 σ1 σ2 ρ : ℝ) : ℝ :=
  let d1 := hkD1 S1 X b1 σ1 T
  let d2 := hkD2 S1 X b1 σ1 T
  let d3 := hkD3 S1 X H S2 b1 σ1 σ2 ρ T
  let d4 := hkD4 S1 X H S2 b1 σ1 σ2 ρ T
  let e1 := hkE1 H S2 b2 σ1 σ2 ρ T
  let e2 := hkE2 H S2 b2 σ1 σ2 ρ T
  let e3 := hkE3 H S2 b2 σ1 σ2 ρ T
  let e4 := hkE4 H S2 b2 σ1 σ2 ρ T
  let mu2 := hkMu b2 σ2
  eta * S1 * Real.exp ((b1 - r) * T) *
      (bivariateNormalCDF (eta * d1) (phi * e1) (-eta * phi * ρ) -
        Real.exp (2 * (mu2 + ρ * σ1 * σ2) * Real.log (H / S2) / σ2 ^ 2) *
          bivariateNormalCDF (eta * d3) (phi * e3) (-eta * phi * ρ)) -
    eta * X * Real.exp (-(r * T)) *
      (bivariateNormalCDF (eta * d2) (phi * e2) (-eta * phi * ρ) -
        Real.exp (2 * mu2 * Real.log (H / S2) / σ2 ^ 2) *
          bivariateNormalCDF (eta * d4) (phi * e4) (-eta * phi * ρ))

/-- **Independent assets factor.** At `ρ = 0` every `N₂` in `A(η, φ)` factors
(`bivariateNormalCDF_zero`), the correlation shifts in `d₃`, `d₄`, `e₂` and the first exponent
vanish, and the knock-out value is the one-asset Black–Scholes value of the option on `S¹`
(cost-of-carry form) times the barrier factor `Φ(φe₁) − e^{2μ₂ log(H/S₂)/σ₂²} Φ(φe₃)` of `S²`,
the single-asset reflection-principle formula for the probability that `S²` does not cross `H`
(that probabilistic reading is not proved here). -/
theorem heynenKatA_rho_zero (eta phi S1 S2 X H T r b1 b2 σ1 σ2 : ℝ) :
    heynenKatA eta phi S1 S2 X H T r b1 b2 σ1 σ2 0 =
      (eta * S1 * Real.exp ((b1 - r) * T) * Phi (eta * hkD1 S1 X b1 σ1 T) -
          eta * X * Real.exp (-(r * T)) * Phi (eta * hkD2 S1 X b1 σ1 T)) *
        (Phi (phi * hkE1 H S2 b2 σ1 σ2 0 T) -
          Real.exp (2 * hkMu b2 σ2 * Real.log (H / S2) / σ2 ^ 2) *
            Phi (phi * hkE3 H S2 b2 σ1 σ2 0 T)) := by
  simp only [heynenKatA, hkD3, hkD4, hkE2, hkE3, hkE4, mul_zero, zero_mul, zero_div, add_zero,
    bivariateNormalCDF_zero]
  ring

/-- **Down-out and up-out collapse to a bivariate-CDF-free form.** For a fixed option type
`η ∈ {-1,1}` and a correlation with `ρ² ≤ 1`, summing the down-barrier (`φ=-1`) and
up-barrier (`φ=1`) knock-out values pairs every `N₂(ηdᵢ,φeᵢ;−ηφρ)` with its `φ`-flipped
partner via `bivariateNormalCDF_flip_snd`
(`N₂(a,b;r)+N₂(a,-b;-r)=Φ(a)`, applied at `a = ηdᵢ`, `b = eᵢ`, `r = -ηρ`), collapsing all four
`N₂` pairs to `Φ(ηd₁), Φ(ηd₂), Φ(ηd₃), Φ(ηd₄)` simultaneously. It holds for any arguments
`dᵢ, eᵢ`: it checks only that `φ` enters as `(φeᵢ, −ηφρ)`, and the sum has no payoff meaning
(the two formulas apply to the disjoint regimes `S₂ > H` and `S₂ < H`). -/
theorem heynenKat_downOut_add_upOut (S1 S2 X H T r b1 b2 σ1 σ2 : ℝ) {eta ρ : ℝ}
    (heta : eta ^ 2 = 1) (hρ : ρ ^ 2 ≤ 1) :
    heynenKatA eta (-1) S1 S2 X H T r b1 b2 σ1 σ2 ρ +
        heynenKatA eta 1 S1 S2 X H T r b1 b2 σ1 σ2 ρ =
      eta * S1 * Real.exp ((b1 - r) * T) *
          (Phi (eta * hkD1 S1 X b1 σ1 T) -
            Real.exp (2 * (hkMu b2 σ2 + ρ * σ1 * σ2) * Real.log (H / S2) / σ2 ^ 2) *
              Phi (eta * hkD3 S1 X H S2 b1 σ1 σ2 ρ T)) -
        eta * X * Real.exp (-(r * T)) *
          (Phi (eta * hkD2 S1 X b1 σ1 T) -
            Real.exp (2 * hkMu b2 σ2 * Real.log (H / S2) / σ2 ^ 2) *
              Phi (eta * hkD4 S1 X H S2 b1 σ1 σ2 ρ T)) := by
  have heρ : (-(eta * ρ)) ^ 2 ≤ 1 := by
    rw [neg_sq, mul_pow, heta, one_mul]; exact hρ
  set d1 := hkD1 S1 X b1 σ1 T with hd1
  set d2 := hkD2 S1 X b1 σ1 T with hd2
  set d3 := hkD3 S1 X H S2 b1 σ1 σ2 ρ T with hd3
  set d4 := hkD4 S1 X H S2 b1 σ1 σ2 ρ T with hd4
  set e1 := hkE1 H S2 b2 σ1 σ2 ρ T with he1
  set e2 := hkE2 H S2 b2 σ1 σ2 ρ T with he2
  set e3 := hkE3 H S2 b2 σ1 σ2 ρ T with he3
  set e4 := hkE4 H S2 b2 σ1 σ2 ρ T with he4
  have h1 := bivariateNormalCDF_flip_snd (eta * d1) e1 heρ
  have h2 := bivariateNormalCDF_flip_snd (eta * d2) e2 heρ
  have h3 := bivariateNormalCDF_flip_snd (eta * d3) e3 heρ
  have h4 := bivariateNormalCDF_flip_snd (eta * d4) e4 heρ
  simp only [neg_neg] at h1 h2 h3 h4
  -- Unfolding `heynenKatA` at the literal `phi := 1 / -1` substitutes `1 * e_i`, `-1 * e_i`,
  -- `-eta * 1 * ρ`, `-eta * (-1) * ρ` for the bivariate-CDF arguments: these are only RING-equal
  -- (not defeq) to the clean `e_i` / `-e_i` / `-(eta * ρ)` / `eta * ρ` forms in `h1`-`h4`, so the
  -- explicit `← hd_i`/`← he_i` fold-back and sign-normalizing lemmas below are needed before
  -- `linear_combination`'s atom matching can see the two sides as the same bivariate-CDF calls.
  simp only [heynenKatA, ← hd1, ← he1, neg_mul, one_mul, mul_neg, mul_one, neg_neg, hkMu, ← hd3,
    ← he3, ← hd2, ← he2, ← hd4, ← he4]
  linear_combination (eta * S1 * Real.exp ((b1 - r) * T)) * h1 +
    (-(eta * X * Real.exp (-(r * T)))) * h2 +
    (-(eta * S1 * Real.exp ((b1 - r) * T) *
        Real.exp (2 * (b2 - σ2 ^ 2 / 2 + ρ * σ1 * σ2) * Real.log (H / S2) / σ2 ^ 2))) * h3 +
    (eta * X * Real.exp (-(r * T)) *
        Real.exp (2 * (b2 - σ2 ^ 2 / 2) * Real.log (H / S2) / σ2 ^ 2)) * h4

/-! ### The independent case through the library's Black–Scholes prices -/

/-- At cost of carry `b₁ = r`, Heynen–Kat's `d₁` is the Black–Scholes `bsd1`. -/
lemma hkD1_eq_bsd1 (S X r σ T : ℝ) : hkD1 S X r σ T = bsd1 S X r σ T := by
  unfold hkD1 hkMu bsd1
  ring

/-- At cost of carry `b₁ = r`, Heynen–Kat's `d₂` is the Black–Scholes `bsd2`. -/
lemma hkD2_eq_bsd2 (S X r σ T : ℝ) : hkD2 S X r σ T = bsd2 S X r σ T := by
  unfold hkD2 bsd2
  rw [hkD1_eq_bsd1]

/-- **Independent assets, call: Black–Scholes call times barrier factor.** At `ρ = 0` and
`b₁ = r`, the Heynen–Kat knock-out call value is the Black–Scholes call `bsV X r σ₁ S₁ T`
on asset 1 times the closed-form barrier factor `Φ(φe₁) − e^{2μ₂ log(H/S₂)/σ₂²}Φ(φe₃)` of
asset 2 (`heynenKatA_rho_zero` with `hkD1_eq_bsd1`, `hkD2_eq_bsd2`). Neither side is shown to
be a discounted expected payoff. -/
theorem heynenKatA_call_rho_zero_eq_bsV (phi S1 S2 X H T r b2 σ1 σ2 : ℝ) :
    heynenKatA 1 phi S1 S2 X H T r r b2 σ1 σ2 0 =
      bsV X r σ1 S1 T *
        (Phi (phi * hkE1 H S2 b2 σ1 σ2 0 T) -
          Real.exp (2 * hkMu b2 σ2 * Real.log (H / S2) / σ2 ^ 2) *
            Phi (phi * hkE3 H S2 b2 σ1 σ2 0 T)) := by
  rw [heynenKatA_rho_zero, hkD1_eq_bsd1, hkD2_eq_bsd2, bsV, sub_self, zero_mul, Real.exp_zero]
  simp only [one_mul, mul_one]

/-- **Independent assets, put: Black–Scholes put times barrier factor.** At `ρ = 0` and
`b₁ = r`, the Heynen–Kat knock-out put value is the Black–Scholes put `bsP X r σ₁ S₁ T` on
asset 1 times the same barrier factor of asset 2. Neither side is shown to be a discounted
expected payoff. -/
theorem heynenKatA_put_rho_zero_eq_bsP (phi S1 S2 X H T r b2 σ1 σ2 : ℝ) :
    heynenKatA (-1) phi S1 S2 X H T r r b2 σ1 σ2 0 =
      bsP X r σ1 S1 T *
        (Phi (phi * hkE1 H S2 b2 σ1 σ2 0 T) -
          Real.exp (2 * hkMu b2 σ2 * Real.log (H / S2) / σ2 ^ 2) *
            Phi (phi * hkE3 H S2 b2 σ1 σ2 0 T)) := by
  rw [heynenKatA_rho_zero, hkD1_eq_bsd1, hkD2_eq_bsd2, bsP, sub_self, zero_mul, Real.exp_zero]
  simp only [neg_mul, one_mul, mul_one]
  ring

end MathFin
