/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.AsianGeometricN
public import LeanPool.MathFin.Models.BlackScholes.PDE

/-!
# Geometric vs arithmetic Asian options

The geometric Asian option's payoff is bounded above by the arithmetic Asian
option's payoff at every state, because the geometric mean of positive numbers
is at most their arithmetic mean (AM-GM).

For prices `S_{t_1}, …, S_{t_n} ≥ 0`:

  `(∏ S_{t_i})^{1/n} ≤ (1/n) ∑ S_{t_i}`.

Since `x ↦ max(x − K, 0)` is monotone non-decreasing:

  `max(geomMean − K, 0) ≤ max(arithMean − K, 0)`.

Integrating over the pricing measure preserves this pointwise inequality. In the
Black–Scholes model with a Brownian driver the geometric Asian price has a closed
form, the Black–Scholes call `bsV` at an effective spot and volatility
(`geomAsianN_call_price`, `Models/BlackScholes/AsianGeometricN.lean`), so the arithmetic Asian
call, which has no closed form, is bounded below by that `bsV` value.

## Main results

* `am_gm_two`: `√(a · b) ≤ (a + b) / 2` for `a, b ≥ 0` — Mathlib's
  `Real.geom_mean_le_arith_mean2_weighted` at weights `1/2`, bridged from
  `rpow` to `sqrt`.
* `geom_mean_le_arith_mean_n`: weighted AM-GM specialized to equal weights
  `1/n` (Mathlib's `Real.geom_mean_le_arith_mean_weighted`).
* `asian_payoff_geom_le_arith_two`, `asian_payoff_geom_le_arith_n`: the geometric
  Asian payoff is bounded above by the arithmetic Asian payoff (two and `n` dates).
* `geomAsianN_bsV_le_arith`: the price-level bound — the closed-form geometric-Asian
  price `bsV K r σ_G S_hat₀ T` is at most the discounted expected arithmetic-Asian payoff
  of the Black–Scholes GBM sampled at the same dates.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], Ch 26.13
* [A. G. Z. Kemna and A. C. F. Vorst, *A pricing method for options based on average asset
  values*][KemnaVorst1990]

## Tags

Asian option, arithmetic average, geometric average, AM–GM inequality, price bound,
average price option, MSC 91G20, MSC 60E15, JEL G13
-/

@[expose] public section

namespace MathFin

open Real

/-- **Two-element AM-GM**: `√(a · b) ≤ (a + b) / 2` for `a, b ≥ 0`. Mathlib's
weighted two-element AM-GM `Real.geom_mean_le_arith_mean2_weighted` at weights
`w₁ = w₂ = 1/2`, with `√x = x^(1/2)` bridging `sqrt` to `rpow`. -/
lemma am_gm_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have h := Real.geom_mean_le_arith_mean2_weighted
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) ha hb
    (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  calc Real.sqrt (a * b) = (a * b) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
    _ = a ^ ((1:ℝ)/2) * b ^ ((1:ℝ)/2) := Real.mul_rpow ha hb
    _ ≤ 1/2 * a + 1/2 * b := h
    _ = (a + b) / 2 := by ring

/-- **Two-time-point geometric vs arithmetic Asian payoff**: for positive
prices `S₁, S₂` and any strike `K`, the geometric-Asian-call payoff is
bounded above by the arithmetic-Asian-call payoff. -/
lemma asian_payoff_geom_le_arith_two (S₁ S₂ K : ℝ) (h₁ : 0 ≤ S₁) (h₂ : 0 ≤ S₂) :
    max (Real.sqrt (S₁ * S₂) - K) 0 ≤ max ((S₁ + S₂) / 2 - K) 0 := by
  have h_mean := am_gm_two S₁ S₂ h₁ h₂
  -- max is monotone in the first argument: x ≤ y ⟹ max(x - K, 0) ≤ max(y - K, 0)
  have h_sub : Real.sqrt (S₁ * S₂) - K ≤ (S₁ + S₂) / 2 - K := by linarith
  exact max_le_max h_sub le_rfl

/-- **Weighted AM-GM, n-element equal-weight form**:
`n · ∏ f_i^{1/n} ≤ ∑ f_i` for non-negative `f : Fin n → ℝ` and `n > 0`. -/
lemma geom_mean_le_arith_mean_n {n : ℕ} (f : Fin n → ℝ)
    (h_nn : ∀ i, 0 ≤ f i) (hn : 0 < n) :
    (n : ℝ) * (∏ i : Fin n, f i ^ ((n : ℝ)⁻¹)) ≤ ∑ i : Fin n, f i := by
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hn_inv_nn : 0 ≤ ((n : ℝ))⁻¹ := inv_nonneg.mpr hn_pos.le
  set w : Fin n → ℝ := fun _ ↦ ((n : ℝ))⁻¹
  have h_w_nn : ∀ i ∈ Finset.univ, 0 ≤ w i := fun _ _ ↦ hn_inv_nn
  have h_f_nn : ∀ i ∈ Finset.univ, 0 ≤ f i := fun i _ ↦ h_nn i
  have h_sum_w : ∑ i ∈ Finset.univ, w i = 1 := by
    change ∑ _ : Fin n, ((n : ℝ))⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- Apply Mathlib weighted AM-GM with `w` and `z := f`.
  have h := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
              w f h_w_nn h_sum_w h_f_nn
  -- `h : ∏ i, f i ^ (1/n) ≤ ∑ i, (1/n) * f i`
  -- Multiply both sides by `n ≥ 0`.
  have h_mul := mul_le_mul_of_nonneg_left h hn_pos.le
  -- Now LHS: n * ∏, RHS: n * ∑ (1/n) * f = ∑ f.
  have h_rhs_simp : (n : ℝ) * ∑ i : Fin n, w i * f i = ∑ i : Fin n, f i := by
    change (n : ℝ) * ∑ i : Fin n, ((n : ℝ))⁻¹ * f i = ∑ i : Fin n, f i
    rw [← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hn_ne, one_mul]
  rw [h_rhs_simp] at h_mul
  exact h_mul

/-- **n-date geometric vs arithmetic Asian payoff**: the geometric-mean Asian
call payoff is bounded above by the arithmetic-mean one, for any number `n` of
averaging dates — the `n`-date extension of `asian_payoff_geom_le_arith_two`,
a one-line `max_le_max` over the already-proved AM-GM `geom_mean_le_arith_mean_n`. -/
lemma asian_payoff_geom_le_arith_n {n : ℕ} (S : Fin n → ℝ)
    (h_nn : ∀ i, 0 ≤ S i) (hn : 0 < n) (K : ℝ) :
    max ((∏ i, S i ^ ((n : ℝ)⁻¹)) - K) 0 ≤ max ((∑ i, S i) / n - K) 0 := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := geom_mean_le_arith_mean_n S h_nn hn
  have h_div : (∏ i, S i ^ ((n : ℝ)⁻¹)) ≤ (∑ i, S i) / n := by
    rw [le_div_iff₀ hn_pos, mul_comm]; exact h
  exact max_le_max (by linarith) le_rfl

/-! ### The price-level bound in the Black–Scholes model -/

section PriceBound

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- The arithmetic-average Asian call payoff of a Black–Scholes GBM sampled at dates `τ` is
integrable: it is the positive part of a finite sum of lognormals minus a constant. -/
lemma integrable_arithAsian_payoff (hB : IsPreBrownianReal B μ) {n : ℕ} (τ : Fin n → ℝ≥0)
    (S₀ K r σ : ℝ) :
    Integrable (fun ω ↦ max ((∑ i, S₀ * Real.exp ((r - σ ^ 2 / 2) * (τ i : ℝ) + σ * B (τ i) ω))
      / n - K) 0) μ := by
  have hS (i : Fin n) : Integrable
      (fun ω ↦ S₀ * Real.exp ((r - σ ^ 2 / 2) * (τ i : ℝ) + σ * B (τ i) ω)) μ := by
    have h : Integrable (fun ω ↦ Real.exp (σ * B (τ i) ω)) μ := by
      rw [show (fun ω ↦ Real.exp (σ * B (τ i) ω)) = (fun x ↦ Real.exp (σ * x)) ∘ B (τ i)
        from rfl]
      refine Integrable.comp_aemeasurable ?_ (hB.aemeasurable _)
      rw [(hB.hasLaw_eval (τ i)).map_eq]
      exact integrable_exp_mul_gaussianReal σ
    refine (h.const_mul (S₀ * Real.exp ((r - σ ^ 2 / 2) * (τ i : ℝ)))).congr
      (ae_of_all _ fun ω ↦ ?_)
    simp only [Real.exp_add]
    ring
  exact (((integrable_finsetSum _ fun i _ ↦ hS i).div_const _).sub'
    (integrable_const K)).pos_part

/-- **The geometric-Asian closed form bounds the arithmetic Asian call from below.** For a
Black–Scholes GBM `S_u = S₀·exp((r − σ²/2)u + σB_u)` sampled at dates `τ : Fin n → ℝ≥0`
(all `≤ T`, non-degenerate log-driver variance), the Black–Scholes call at the geometric
average's effective spot `S_hat₀` and volatility `σ_G` — which is the geometric-Asian price,
`geomAsianN_call_price` — is at most the discounted expected arithmetic-Asian call payoff
`e^{−rT}·𝔼[max((1/n)∑ᵢ S_{τᵢ} − K, 0)]`. The proof integrates the pointwise AM–GM payoff
bound `asian_payoff_geom_le_arith_n`. -/
theorem geomAsianN_bsV_le_arith (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    {n : ℕ} (hn : 0 < n) (τ : Fin n → ℝ≥0) (hτT : ∀ i, τ i ≤ T)
    (S₀ K r σ Tmat : ℝ) (hS₀ : 0 < S₀) (hK : 0 < K) (hσ : 0 < σ) (hTmat : 0 < Tmat)
    (hV : 0 < geomAsianVar τ) :
    bsV K r (geomAsianEffVol σ Tmat τ) (geomAsianEffSpot S₀ r σ Tmat τ) Tmat ≤
      ∫ ω, Real.exp (-r * Tmat) *
        max ((∑ i, S₀ * Real.exp ((r - σ ^ 2 / 2) * (τ i : ℝ) + σ * B (τ i) ω)) / n - K) 0
        ∂μ := by
  calc bsV K r (geomAsianEffVol σ Tmat τ) (geomAsianEffSpot S₀ r σ Tmat τ) Tmat
      = ∫ ω, Real.exp (-r * Tmat) *
          max ((∏ i, (S₀ * Real.exp ((r - σ ^ 2 / 2) * (τ i : ℝ) + σ * B (τ i) ω))
            ^ ((n : ℝ)⁻¹)) - K) 0 ∂μ := by
        rw [geomAsianN_call_price hB T hn τ hτT S₀ K r σ Tmat hS₀ hK hσ hTmat hV, bsV,
          neg_mul]
    _ ≤ _ := integral_mono_of_nonneg
        (ae_of_all _ fun ω ↦ mul_nonneg (Real.exp_pos _).le (le_max_right _ _))
        ((integrable_arithAsian_payoff hB τ S₀ K r σ).const_mul _)
        (ae_of_all _ fun ω ↦ mul_le_mul_of_nonneg_left
          (asian_payoff_geom_le_arith_n _ (fun i ↦ by positivity) hn K) (Real.exp_pos _).le)

end PriceBound

end MathFin
