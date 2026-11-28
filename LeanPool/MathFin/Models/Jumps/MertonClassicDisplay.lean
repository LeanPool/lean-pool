/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Jumps.MertonJumpDiffusion

/-!
# The classic Merton display: `Λ′ = Λ(1+k)`

`MertonJumpDiffusion.lean` states the price with jump-compensated
*conditional spots* `spot_n = S₀ e^{−kΛ}(1+k)^n` under plain Poisson
weights. The textbook display instead keeps the spot at `S₀` and absorbs
the jump factor `(1+k)^n` into an **adjusted intensity** `Λ′ = Λ(1+k)` and
a **shifted rate** `r_n = r − kΛ/T + n·log(1+k)/T`:

  `C_Merton = Σₙ e^{−Λ′} Λ′ⁿ/n! · C_BS(S₀, K, r_n, vol_n, T)`.

The two forms are the same series regrouped, and the regrouping is driven
by one structural identity of the BS formula:

* **Rate-shift identity** (`bsV_spot_exp_rate_shift`): spot growth `e^{cτ}`
  trades for a discount-rate shift,
  `bsV K r σ (S e^{cτ}) τ = e^{cτ} · bsV K (r+c) σ S τ` — the same
  invariance that underlies forward/futures re-parametrizations.

Applying it at `c_n = r_n − r` (so `e^{c_n T} = e^{−kΛ}(1+k)^n`, the
compensated jump growth) turns each conditional value into
`e^{−kΛ}(1+k)^n · C_BS(S₀, r_n, vol_n)`, and the weight algebra
`e^{−Λ}Λⁿ/n! · e^{−kΛ}(1+k)ⁿ = e^{−Λ′}Λ′ⁿ/n!` finishes the display.
No hypotheses beyond `S₀, K > 0`, `T > 0`, `k > −1` — in particular no
constraint on `σ`, `δ`, `r`.

## Main definitions

* `mertonRate`: the jump-adjusted rate `r_n = r − kΛ/T + n·log(1+k)/T` of the classic display.

## Main results

* `bsV_spot_exp_rate_shift` — the rate-shift identity.
* `mertonCallTerm_eq_classic` — per-term regrouping.
* `mertonCallPrice_eq_classic_tsum` — the classic Merton series.

## References

* [R. C. Merton, *Option pricing when underlying stock returns are discontinuous*][Merton1976], eq.
  (16)

## Tags

Merton jump-diffusion, adjusted intensity, Poisson series, textbook form, jump compensator,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal Nat

/-- The jump-adjusted rate of the classic display:
`r_n = r − kΛ/T + n·log(1+k)/T` — the `n`-conditional drift correction that
trades the jump-compensated spot for a rate shift. -/
noncomputable def mertonRate (r k T : ℝ) (Λ : ℝ≥0) (n : ℕ) : ℝ :=
  r - k * (Λ : ℝ) / T + n * Real.log (1 + k) / T

/-- `d₁` trades spot growth `e^{cτ}` for a rate shift `r ↦ r + c`. -/
lemma bsd1_spot_exp_shift {S K : ℝ} (hS : 0 < S) (hK : 0 < K)
    (r c σ τ : ℝ) :
    bsd1 (S * rexp (c * τ)) K r σ τ = bsd1 S K (r + c) σ τ := by
  unfold bsd1
  rw [show S * rexp (c * τ) / K = S / K * rexp (c * τ) from by ring,
    Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- `d₂` inherits the same trade. -/
lemma bsd2_spot_exp_shift {S K : ℝ} (hS : 0 < S) (hK : 0 < K)
    (r c σ τ : ℝ) :
    bsd2 (S * rexp (c * τ)) K r σ τ = bsd2 S K (r + c) σ τ := by
  unfold bsd2
  rw [bsd1_spot_exp_shift hS hK]

/-- **Rate-shift identity**: spot growth `e^{cτ}` trades for a discount-rate
shift, `bsV K r σ (S e^{cτ}) τ = e^{cτ} · bsV K (r+c) σ S τ`. The algebraic
engine of the classic Merton display. -/
theorem bsV_spot_exp_rate_shift {S K : ℝ} (hS : 0 < S) (hK : 0 < K)
    (r c σ τ : ℝ) :
    bsV K r σ (S * rexp (c * τ)) τ = rexp (c * τ) * bsV K (r + c) σ S τ := by
  unfold bsV
  rw [bsd1_spot_exp_shift hS hK, bsd2_spot_exp_shift hS hK,
    show -(r * τ) = c * τ + -((r + c) * τ) from by ring, Real.exp_add]
  ring

/-- The compensated spot as exponential growth at the shifted rate:
`mertonSpot S₀ k Λ n = S₀ · e^{(r_n − r)T}`. -/
lemma mertonSpot_eq_spot_exp {k T : ℝ} (S_0 : ℝ) (hT : 0 < T) (hk : -1 < k)
    (Λ : ℝ≥0) (r : ℝ) (n : ℕ) :
    mertonSpot S_0 k Λ n = S_0 * rexp ((mertonRate r k T Λ n - r) * T) := by
  have h1k : (0 : ℝ) < 1 + k := by linarith
  unfold mertonSpot mertonRate
  rw [show (r - k * (Λ : ℝ) / T + ↑n * Real.log (1 + k) / T - r) * T
      = -(k * (Λ : ℝ)) + ↑n * Real.log (1 + k) from by
        field_simp [hT.ne']; ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log h1k]
  ring

/-- **Per-term classic form**: each Merton term regroups as the compensated
jump growth times a Black–Scholes value at spot `S₀` and the shifted rate:
`term_n = e^{−kΛ}(1+k)^n · bsV K r_n vol_n S₀ T`. -/
theorem mertonCallTerm_eq_classic {S_0 K k T : ℝ} (r σ δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hT : 0 < T) (hk : -1 < k) (n : ℕ) :
    mertonCallTerm S_0 K r σ T k δ Λ n
      = rexp (-(k * (Λ : ℝ))) * (1 + k) ^ n
          * bsV K (mertonRate r k T Λ n) (mertonVol σ δ T n) S_0 T := by
  have h1k : (0 : ℝ) < 1 + k := by linarith
  rw [mertonCallTerm_eq_bsV, mertonSpot_eq_spot_exp S_0 hT hk Λ r n,
    bsV_spot_exp_rate_shift hS_0 hK,
    show r + (mertonRate r k T Λ n - r) = mertonRate r k T Λ n from by ring,
    show (mertonRate r k T Λ n - r) * T
      = -(k * (Λ : ℝ)) + ↑n * Real.log (1 + k) from by
        unfold mertonRate; field_simp [hT.ne']; ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log h1k]

/-- **The classic Merton (1976) display**: regrouping the jump factor
`(1+k)^n` into the Poisson weight gives the textbook series — weights at
the adjusted intensity `Λ′ = Λ(1+k)`, Black–Scholes values at spot `S₀`,
shifted rates `r_n`, conditional vols `vol_n`:

  `C_Merton = Σₙ e^{−Λ′} Λ′ⁿ/n! · C_BS(S₀, K, r_n, vol_n, T)`. -/
theorem mertonCallPrice_eq_classic_tsum {S_0 K k T : ℝ} (r σ δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hT : 0 < T) (hk : -1 < k) :
    mertonCallPrice S_0 K r σ T k δ Λ
      = ∑' n : ℕ, rexp (-((Λ : ℝ) * (1 + k))) * ((Λ : ℝ) * (1 + k)) ^ n / n !
          * bsV K (mertonRate r k T Λ n) (mertonVol σ δ T n) S_0 T := by
  rw [mertonCallPrice_eq_tsum]
  refine tsum_congr fun n ↦ ?_
  rw [mertonCallTerm_eq_classic r σ δ Λ hS_0 hK hT hk n,
    show -((Λ : ℝ) * (1 + k)) = -(Λ : ℝ) + -(k * (Λ : ℝ)) from by ring,
    Real.exp_add, mul_pow]
  ring

end MathFin
