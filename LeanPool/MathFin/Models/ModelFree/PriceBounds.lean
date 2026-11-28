/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.Put
public import LeanPool.MathFin.Models.BlackScholes.PutGreeks
public import Mathlib.Algebra.Order.Star.Real

/-!
# The no-arbitrage rectangle for European call/put prices

Under the BS risk-neutral lognormal hypothesis, the call and put prices live
in a rectangle in the plane:

  `max(0, S₀ − K · e^{−rT}) ≤ bsV ≤ S₀`,
  `max(0, K · e^{−rT} − S₀) ≤ bsP ≤ K · e^{−rT}`,

and they are tied by put-call parity:

  `bsV − bsP = S₀ − K · e^{−rT}`.

This rectangle is the *single* structural fact. The library previously stated
six independent bound theorems, each with its own proof; here we collect them
around three elementary facts:

* **`bsV_nonneg`**: `0 ≤ bsV` (integrand `(S_T − K)⁺ ≥ 0`).
* **`bsP_nonneg`**: `0 ≤ bsP` (integrand `(K − S_T)⁺ ≥ 0`).
* **`bsP_eq_bsV`**: the parity identity (already proved in `PutGreeks.lean`).

Plus the trivial Phi-bounds `0 ≤ Φ ≤ 1`. Every other static price-bound
theorem reduces to a one-liner.

## Map of consequences

| Theorem                            | Proof via                              |
|------------------------------------|----------------------------------------|
| `bsV_le_S`                         | `Phi ≤ 1` + `Phi ≥ 0` (direct)         |
| `bsP_le_K_disc`                    | `Phi ≤ 1` + `Phi ≥ 0` (direct)         |
| `bsV_ge_forward_lower_bound`       | parity + `bsP_nonneg`                  |
| `bsP_ge_intrinsic_no_arb`          | parity + `bsV_nonneg`                  |
| `bsV_strict_gt_immediate_exercise` | forward lb + `exp(-rT) < 1` for `rT>0` |
| `box_spread_identity`              | subtract two parities                  |

The last is Merton (1973) — the strict bound that proves American = European
for a non-dividend call (early exercise is never optimal).

## Why this unification is the right one

Each of the six bounds in the table can be (and was) proved independently
from the BS formula by hand. But the *meaning* of each — bsV ≤ S says "a
call costs less than the stock", bsP ≥ K · e^{−rT} − S says "a put costs at
least the discounted strike minus spot", etc. — sits on the rectangle. Naming
the rectangle makes the meaning explicit and the proofs trivial.

## Main results

* `noArbBox`: under `BSCallHyp`, the call and put prices lie in the rectangle
  `max(0, S₀ − K·e^{−rT}) ≤ bsV ≤ S₀` and `max(0, K·e^{−rT} − S₀) ≤ bsP ≤ K·e^{−rT}`.
* `bsV_nonneg`, `bsP_nonneg`: the call and put prices are nonnegative under `BSCallHyp`.
* `bsV_le_S`, `bsP_le_K_disc`: for `S, K ≥ 0`, `bsV ≤ S` and `bsP ≤ K·e^{−rτ}`.
* `bsV_ge_forward_lower_bound`, `bsP_ge_intrinsic_no_arb`: `S − K·e^{−rτ} ≤ bsV` and
  `K·e^{−rτ} − S ≤ bsP`.
* `box_spread_identity`: `(bsV(K₁) − bsP(K₁)) − (bsV(K₂) − bsP(K₂)) = (K₂ − K₁)·e^{−rτ}`.
* `bsV_strict_gt_immediate_exercise`: for `r > 0`, `S₀ − K < bsV`.

## References

* [Cohen (1985)][Cohen1985]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 11.3; Ch 11.2; Ch 12.8
* [R. C. Merton, *Theory of rational option pricing*][Merton1973]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 4.5

## Tags

no-arbitrage bounds, put–call parity, option price bounds, Merton early exercise, box spread,
intrinsic value, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-! ### Bridging the closed-form `bsV`/`bsP` definitions to integral forms -/

/-- Bridge from the closed-form `bsV` to the discounted risk-neutral expectation
`∫ e^{−rT} · (S_T − K)⁺ dQ`. Pure normalisation of `bs_call_formula`
(reconciles `Real.exp (-r * T)` with `Real.exp (-(r * T))`). -/
private lemma bsV_eq_riskNeutralExpectation
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    bsV K r σ S_0 T =
      ∫ ω, Real.exp (-(r * T)) *
            max (bsTerminal S_0 r σ T (Z ω) - K) 0 ∂Q := by
  have h_form := bs_call_formula h
  have h_exp : Real.exp (-r * T) = Real.exp (-(r * T)) := by congr 1; ring
  rw [h_exp] at h_form
  -- Goal: bsV K r σ S_0 T = ∫ ... ∂Q
  -- bsV's def matches h_form's RHS exactly after the normalisation above.
  change S_0 * Phi (bsd1 S_0 K r σ T) -
        K * Real.exp (-(r * T)) * Phi (bsd2 S_0 K r σ T) = _
  exact h_form.symm

/-- Bridge from the closed-form `bsP` to `∫ e^{−rT} · (K − S_T)⁺ dQ`. -/
private lemma bsP_eq_riskNeutralExpectation
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    bsP K r σ S_0 T =
      ∫ ω, Real.exp (-(r * T)) *
            max (K - bsTerminal S_0 r σ T (Z ω)) 0 ∂Q := by
  have h_form := bs_put_formula h
  have h_exp : Real.exp (-r * T) = Real.exp (-(r * T)) := by congr 1; ring
  rw [h_exp] at h_form
  change K * Real.exp (-(r * T)) * Phi (-bsd2 S_0 K r σ T) -
        S_0 * Phi (-bsd1 S_0 K r σ T) = _
  exact h_form.symm

/-! ### The three foundational facts (the two non-negativities + Phi ≤ 1) -/

/-- **Call price non-negativity**: `0 ≤ bsV`. Integrand `e^{−rT} · (S_T − K)⁺`
is non-negative pointwise (positive discount factor times the non-negative
positive-part). -/
theorem bsV_nonneg
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    0 ≤ bsV K r σ S_0 T := by
  rw [bsV_eq_riskNeutralExpectation h]
  exact integral_nonneg fun _ ↦
    mul_nonneg (Real.exp_pos _).le (le_max_right _ _)

/-- **Put price non-negativity**: `0 ≤ bsP`. Same argument with `(K − S_T)⁺`. -/
theorem bsP_nonneg
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    0 ≤ bsP K r σ S_0 T := by
  rw [bsP_eq_riskNeutralExpectation h]
  exact integral_nonneg fun _ ↦
    mul_nonneg (Real.exp_pos _).le (le_max_right _ _)

/-! ### The two formula-direct upper bounds (Phi-bounds path, no parity)

`Phi_le_one` now lives in `Probability.Gaussian.StandardNormal` (pricing-free). -/

/-- **Call upper bound**: `bsV ≤ S` for non-negative spot/strike. By
`Phi ≤ 1`: the `S · Φ(d₁)` term is bounded by `S`, and the `−K · e^{−rτ} ·
Φ(d₂)` term is non-positive. -/
lemma bsV_le_S (K r σ : ℝ) (S τ : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) :
    bsV K r σ S τ ≤ S := by
  unfold bsV
  have h_Φd1 : Phi (bsd1 S K r σ τ) ≤ 1 := Phi_le_one _
  have h_Φd2 : 0 ≤ Phi (bsd2 S K r σ τ) := Phi_nonneg _
  have h_exp : 0 ≤ Real.exp (-(r * τ)) := (Real.exp_pos _).le
  have h_S_term : S * Phi (bsd1 S K r σ τ) ≤ S := by
    have := mul_le_mul_of_nonneg_left h_Φd1 hS
    simpa using this
  have h_K_term : 0 ≤ K * Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ) := by
    positivity
  linarith

/-- **Put upper bound**: `bsP ≤ K · e^{−rτ}`. Symmetric to `bsV_le_S` via
`Φ(−d₂) ≤ 1`. -/
lemma bsP_le_K_disc (K r σ : ℝ) (S τ : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) :
    bsP K r σ S τ ≤ K * Real.exp (-(r * τ)) := by
  unfold bsP
  have h_Φnegd2 : Phi (-bsd2 S K r σ τ) ≤ 1 := Phi_le_one _
  have h_Φnegd1 : 0 ≤ Phi (-bsd1 S K r σ τ) := Phi_nonneg _
  have h_exp : 0 ≤ Real.exp (-(r * τ)) := (Real.exp_pos _).le
  have h_first :
      K * Real.exp (-(r * τ)) * Phi (-bsd2 S K r σ τ) ≤
        K * Real.exp (-(r * τ)) := by
    have h_factor_nn : 0 ≤ K * Real.exp (-(r * τ)) := mul_nonneg hK h_exp
    have := mul_le_mul_of_nonneg_left h_Φnegd2 h_factor_nn
    simpa using this
  have h_second : 0 ≤ S * Phi (-bsd1 S K r σ τ) := mul_nonneg hS h_Φnegd1
  linarith

/-! ### The four parity-driven corollaries (one-line proofs each) -/

/-- **Forward lower bound**: `S − K · e^{−rτ} ≤ bsV`. By parity
`bsV = bsP + S − K · e^{−rτ}` and `bsP ≥ 0`. -/
theorem bsV_ge_forward_lower_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    S_0 - K * Real.exp (-(r * T)) ≤ bsV K r σ S_0 T := by
  have h_par := bsP_eq_bsV K r σ S_0 T
  have h_pos := bsP_nonneg h
  linarith

/-- **Intrinsic-style put lower bound**: `K · e^{−rτ} − S ≤ bsP`. By parity
`bsP = bsV + K · e^{−rτ} − S` and `bsV ≥ 0`. The "dual" of the call's forward
lower bound. -/
theorem bsP_ge_intrinsic_no_arb
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    K * Real.exp (-(r * T)) - S_0 ≤ bsP K r σ S_0 T := by
  have h_par := bsP_eq_bsV K r σ S_0 T
  have h_pos := bsV_nonneg h
  linarith

/-- **Box-spread identity**: `(bsV(K₁) − bsP(K₁)) − (bsV(K₂) − bsP(K₂)) =
(K₂ − K₁) · e^{−rτ}`. Two applications of put-call parity, subtracted. -/
theorem box_spread_identity (K₁ K₂ r σ S τ : ℝ) :
    (bsV K₁ r σ S τ - bsP K₁ r σ S τ) -
        (bsV K₂ r σ S τ - bsP K₂ r σ S τ) =
      (K₂ - K₁) * Real.exp (-(r * τ)) := by
  grind [pricing]

/-! ### Merton 1973: American non-dividend call equals European call -/

/-- **Merton 1973 strict dominance**: for `r > 0`, `S₀ − K < bsV`. Combined
with `bsV ≥ 0`, this strictly dominates the immediate-exercise payoff
`max(S₀ − K, 0)`, so early exercise is never optimal. American = European.

Proof: `bsV ≥ S₀ − K · e^{−rT}` (forward lb) and `K · e^{−rT} < K` (because
`e^{−rT} < 1` for `r > 0` and `T > 0`, multiplied by `K > 0`). -/
theorem bsV_strict_gt_immediate_exercise
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) (hr : 0 < r) :
    S_0 - K < bsV K r σ S_0 T := by
  have h_forward := bsV_ge_forward_lower_bound h
  have hT := h.T_pos
  have hK := h.K_pos
  have h_exp_lt_one : Real.exp (-(r * T)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith [mul_pos hr hT]
  have h_K_strict : K * Real.exp (-(r * T)) < K := by
    have := mul_lt_mul_of_pos_left h_exp_lt_one hK
    simpa using this
  linarith

/-! ### Packaging: the no-arbitrage rectangle, in one theorem -/

/-- **The no-arbitrage rectangle**: under `BSCallHyp`, the call and put
prices satisfy

  `max(0, S₀ − K · e^{−rT}) ≤ bsV K r σ S₀ T ≤ S₀`,
  `max(0, K · e^{−rT} − S₀) ≤ bsP K r σ S₀ T ≤ K · e^{−rT}`.

Each of the four sides of the call rectangle (and put rectangle) is a named
theorem above; this packages them. -/
theorem noArbBox
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    max 0 (S_0 - K * Real.exp (-(r * T))) ≤ bsV K r σ S_0 T ∧
    bsV K r σ S_0 T ≤ S_0 ∧
    max 0 (K * Real.exp (-(r * T)) - S_0) ≤ bsP K r σ S_0 T ∧
    bsP K r σ S_0 T ≤ K * Real.exp (-(r * T)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact max_le (bsV_nonneg h) (bsV_ge_forward_lower_bound h)
  · exact bsV_le_S K r σ S_0 T h.S_0_pos.le h.K_pos.le
  · exact max_le (bsP_nonneg h) (bsP_ge_intrinsic_no_arb h)
  · exact bsP_le_K_disc K r σ S_0 T h.S_0_pos.le h.K_pos.le

end MathFin
