/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.PDE

/-!
# The Garman normal form: every BS-family closed form is one formula

Every European-call closed form in the library has the shape

  `V = A · Φ(d_1) − K · DF · Φ(d_2)`,
  `d_1 = log(A / (K · DF)) / (σ · √T) + σ · √T / 2`,
  `d_2 = d_1 − σ · √T`,

where `A` is the **present value of receiving one unit of the asset at
maturity** under the chosen numéraire and `DF` is the **discount factor for
cash received at maturity**.

Specialisations:

| Variant | `A` | `DF` | What changes |
|---|---|---|---|
| Standard BS (`bsV` in `PDE.lean`) | `S` | `e^{−rτ}` | (baseline) |
| Black-76 (`black_futures_formula`) | `F · e^{−rT}` | `e^{−rT}` | underlying is the *forward* |
| BS-Merton dividends | `S · e^{−qT}` | `e^{−rT}` | continuous dividend yield `q` |
| Garman-Kohlhagen FX | `S · e^{−r_f T}` | `e^{−r_d T}` | foreign-rate-discounted asset |
| KMV-Merton credit | `V` (firm) | `e^{−rT}` | strike = face debt; `d_2` = distance to default |
| Swaption (Black model) | `A_annuity · F` | `A_annuity` | annuity numéraire |
| Quanto-adjusted | drift-shifted | `e^{−r_dom T}` | correlation adjustment in drift |
| Margrabe exchange (`margrabe_eq_bsVGarman`) | `S¹₀` | `1` | 2nd asset is the strike (see below) |

In the Margrabe row `σ` is the effective volatility `√(σ₁²+σ₂²−2ρσ₁σ₂)`, and there is no
discounting: the second asset is the numéraire.

This is the **change-of-numéraire** principle in elementary form: BS pricing
is a single computation, parameterised by what the underlying and the
discount factor mean.

## Why this is structural, not cosmetic

This file is **load-bearing**: we prove the BS closed form `bsV` and the
Black-76 / BS-Merton closed-form right-hand sides are *equal* (as real
numbers) to `bsVGarman` at the appropriate `(A, DF)`. Each existing
specialisation file becomes a one-line corollary instead of a separate
chain-rule + integral derivation.

This is what was missing in the previously-shipped `KMVMerton.lean`,
`Quanto.lean`, `Swaption.lean`: those files redefined the same formula in
new variable names. The honest content is "the formula is parameterised
by `(A, DF)`", which is exactly what this file says.

## Main definitions

* `gbsd1`, `gbsd2`: `d₁ = (log(A/(K·DF)) + σ²T/2) / (σ√T)` and `d₂ = d₁ − σ√T`.
* `bsVGarman`: the Garman-normalised call price `A · Φ(d₁) − K · DF · Φ(d₂)`, where `A` is the
  present value of one unit of the asset at maturity and `DF` the discount factor for cash at
  maturity.

## Main results

* `bsd1_eq_gbsd1_standard`, `bsd2_eq_gbsd2_standard`: standard BS d_1/d_2
  match the Garman form at `DF = e^{−rτ}`.
* `bsV_eq_bsVGarman_standard`: **`bsV` is `bsVGarman`** at the standard BS
  parameters. This is the load-bearing instance.
* `black76_RHS_eq_bsVGarman`: the closed-form RHS of `black_futures_formula`
  equals `bsVGarman` at `A = F · e^{−rT}`, `DF = e^{−rT}`.
* `bs_dividends_RHS_eq_bsVGarman`: the closed-form RHS of
  `bs_dividends_call_formula` equals `bsVGarman` at `A = S · e^{−qT}`,
  `DF = e^{−rT}`.

## Tags

Garman normal form, generalized Black–Scholes, cost of carry, unified closed form, discount factor,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Real

/-! ### Garman-normalised definitions -/

/-- **Garman-normalised `d_1`**: `d_1 = (log(A/(K·DF)) + σ²T/2) / (σ √T)`. -/
noncomputable def gbsd1 (A K DF σ T : ℝ) : ℝ :=
  (Real.log (A / (K * DF)) + σ^2 * T / 2) / (σ * Real.sqrt T)

/-- **Garman-normalised `d_2`**: `d_2 = d_1 − σ √T`. -/
noncomputable def gbsd2 (A K DF σ T : ℝ) : ℝ :=
  gbsd1 A K DF σ T - σ * Real.sqrt T

/-- **Garman-normalised BS call price**: `V = A · Φ(d_1) − K · DF · Φ(d_2)`. -/
noncomputable def bsVGarman (A K DF σ T : ℝ) : ℝ :=
  A * Phi (gbsd1 A K DF σ T) - K * DF * Phi (gbsd2 A K DF σ T)

/-! ### Standard BS is a Garman instance -/

/-- **Log-algebra bridge**: `log(S / (K · e^{−rτ})) = log(S/K) + rτ`. -/
lemma log_div_mul_exp_neg (S K r τ : ℝ) (hS : 0 < S) (hK : 0 < K) :
    Real.log (S / (K * Real.exp (-(r * τ)))) = Real.log (S / K) + r * τ := by
  have hexp_ne : Real.exp (-(r * τ)) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.log_div hS.ne' (mul_ne_zero hK.ne' hexp_ne)]
  rw [Real.log_mul hK.ne' hexp_ne]
  rw [Real.log_exp]
  rw [Real.log_div hS.ne' hK.ne']
  ring

/-- **Standard BS `bsd1` matches the Garman normal form** at `DF = e^{−rτ}`. -/
lemma bsd1_eq_gbsd1_standard (S K r σ τ : ℝ) (hS : 0 < S) (hK : 0 < K) :
    bsd1 S K r σ τ = gbsd1 S K (Real.exp (-(r * τ))) σ τ := by
  unfold bsd1 gbsd1
  congr 1
  rw [log_div_mul_exp_neg S K r τ hS hK]
  ring

/-- **Standard BS `bsd2` matches the Garman normal form**. -/
lemma bsd2_eq_gbsd2_standard (S K r σ τ : ℝ) (hS : 0 < S) (hK : 0 < K) :
    bsd2 S K r σ τ = gbsd2 S K (Real.exp (-(r * τ))) σ τ := by
  unfold bsd2 gbsd2
  rw [bsd1_eq_gbsd1_standard S K r σ τ hS hK]

/-- **`bsV` is a Garman instance**: the standard BS call price equals
`bsVGarman S K (e^{−rτ}) σ τ`. This is the load-bearing fact that makes
the Garman form the actual structural object underlying BS pricing — not
just a cosmetic rename. -/
theorem bsV_eq_bsVGarman_standard (K r σ S τ : ℝ) (hS : 0 < S) (hK : 0 < K) :
    bsV K r σ S τ = bsVGarman S K (Real.exp (-(r * τ))) σ τ := by
  unfold bsV bsVGarman
  rw [bsd1_eq_gbsd1_standard S K r σ τ hS hK]
  rw [bsd2_eq_gbsd2_standard S K r σ τ hS hK]

/-! ### Black-76 is a Garman instance -/

/-- **Log-algebra bridge** for Black-76: `log((F·e^{−rT}) / (K·e^{−rT})) = log(F/K)`. -/
lemma log_FDF_div_KDF (F K r T : ℝ) (hF : 0 < F) (hK : 0 < K) :
    Real.log (F * Real.exp (-(r * T)) / (K * Real.exp (-(r * T)))) =
      Real.log (F / K) := by
  have hexp_ne : Real.exp (-(r * T)) ≠ 0 := (Real.exp_pos _).ne'
  rw [show F * Real.exp (-(r * T)) / (K * Real.exp (-(r * T))) = F / K from by
    field_simp]

/-- **`bsd1 F K 0 σ T` matches Garman's `gbsd1`** at Black-76 parameters
`A = F · e^{−rT}`, `DF = e^{−rT}`. -/
lemma bsd1_eq_gbsd1_black76 (F K r σ T : ℝ) (hF : 0 < F) (hK : 0 < K) :
    bsd1 F K 0 σ T =
      gbsd1 (F * Real.exp (-(r * T))) K (Real.exp (-(r * T))) σ T := by
  unfold bsd1 gbsd1
  congr 1
  rw [log_FDF_div_KDF F K r T hF hK]
  rw [Real.log_div hF.ne' hK.ne']
  ring

/-- **`bsd2` Black-76 / Garman match**. -/
lemma bsd2_eq_gbsd2_black76 (F K r σ T : ℝ) (hF : 0 < F) (hK : 0 < K) :
    bsd2 F K 0 σ T =
      gbsd2 (F * Real.exp (-(r * T))) K (Real.exp (-(r * T))) σ T := by
  unfold bsd2 gbsd2
  rw [bsd1_eq_gbsd1_black76 F K r σ T hF hK]

/-- **Black-76 closed form is a Garman instance**: the explicit RHS of
`black_futures_formula` equals `bsVGarman` at `A = F · e^{−rT}`, `DF = e^{−rT}`.

So the Black-76 closed form is *not* a separate pricing theorem — it is the
same formula as standard BS, viewed through a different (forward) numéraire. -/
theorem black76_RHS_eq_bsVGarman (F K r σ T : ℝ) (hF : 0 < F) (hK : 0 < K) :
    Real.exp (-(r * T)) *
        (F * Phi (bsd1 F K 0 σ T) - K * Phi (bsd2 F K 0 σ T)) =
      bsVGarman (F * Real.exp (-(r * T))) K (Real.exp (-(r * T))) σ T := by
  unfold bsVGarman
  rw [← bsd1_eq_gbsd1_black76 F K r σ T hF hK,
      ← bsd2_eq_gbsd2_black76 F K r σ T hF hK]
  ring

/-! ### BS-Merton (continuous dividends) is a Garman instance -/

/-- **Log-algebra bridge for BS-Merton**: `log((S·e^{−qT}) / (K·e^{−rT})) =
log(S/K) + (r − q)T`. -/
lemma log_SexpNegQ_div_KexpNegR (S K r q T : ℝ) (hS : 0 < S) (hK : 0 < K) :
    Real.log (S * Real.exp (-(q * T)) / (K * Real.exp (-(r * T)))) =
      Real.log (S / K) + (r - q) * T := by
  have hexpQ_ne : Real.exp (-(q * T)) ≠ 0 := (Real.exp_pos _).ne'
  have hexpR_ne : Real.exp (-(r * T)) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.log_div (mul_ne_zero hS.ne' hexpQ_ne) (mul_ne_zero hK.ne' hexpR_ne)]
  rw [Real.log_mul hS.ne' hexpQ_ne, Real.log_mul hK.ne' hexpR_ne]
  rw [Real.log_exp, Real.log_exp]
  rw [Real.log_div hS.ne' hK.ne']
  ring

/-- **`bsd1 S K (r-q) σ T` matches Garman's `gbsd1`** at BS-Merton dividend
parameters `A = S · e^{−qT}`, `DF = e^{−rT}`. -/
lemma bsd1_eq_gbsd1_dividends (S K r q σ T : ℝ) (hS : 0 < S) (hK : 0 < K) :
    bsd1 S K (r - q) σ T =
      gbsd1 (S * Real.exp (-(q * T))) K (Real.exp (-(r * T))) σ T := by
  unfold bsd1 gbsd1
  congr 1
  rw [log_SexpNegQ_div_KexpNegR S K r q T hS hK]
  rw [Real.log_div hS.ne' hK.ne']
  ring

/-- **`bsd2` BS-Merton / Garman match**. -/
lemma bsd2_eq_gbsd2_dividends (S K r q σ T : ℝ) (hS : 0 < S) (hK : 0 < K) :
    bsd2 S K (r - q) σ T =
      gbsd2 (S * Real.exp (-(q * T))) K (Real.exp (-(r * T))) σ T := by
  unfold bsd2 gbsd2
  rw [bsd1_eq_gbsd1_dividends S K r q σ T hS hK]

/-- **BS-Merton dividend formula is a Garman instance**: the explicit RHS
of `bs_dividends_call_formula` equals `bsVGarman` at `A = S · e^{−qT}`,
`DF = e^{−rT}`. -/
theorem bs_dividends_RHS_eq_bsVGarman (S K r q σ T : ℝ) (hS : 0 < S) (hK : 0 < K) :
    S * Real.exp (-(q * T)) * Phi (bsd1 S K (r - q) σ T) -
        K * Real.exp (-(r * T)) * Phi (bsd2 S K (r - q) σ T) =
      bsVGarman (S * Real.exp (-(q * T))) K (Real.exp (-(r * T))) σ T := by
  unfold bsVGarman
  rw [← bsd1_eq_gbsd1_dividends S K r q σ T hS hK,
      ← bsd2_eq_gbsd2_dividends S K r q σ T hS hK]

end MathFin
