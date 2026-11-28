/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.CRRCharFun
public import LeanPool.MathFin.Models.BlackScholes.Put

/-!
# CRR → Black–Scholes call price, in closed form

`binomialPrice_call_tendsto_bs` lands the binomial call-price limit in the
put-call-parity *integral* form `e^{−rT}·E[(K − S_T)₊] + (S₀ − K e^{−rT})`.
This file chains it to the literal Black–Scholes closed form
`S₀·Φ(d₁) − K·e^{−rT}·Φ(d₂)`, via the BS put formula (`bs_put_formula`,
instantiated on the terminal law `N((r−σ²/2)T, σ²T)` through the standardisation
`Z = (· − (r−σ²/2)T)/(σ√T)`) and the CDF symmetry `Φ(−x) = 1 − Φ(x)`.

## Main results

* `exp_neg_mul_integral_put_gaussian_eq`: for `σ, T, S₀, K > 0`, the discounted put expectation
  under `N((r − σ²/2)T, σ²T)` equals the Black–Scholes put value.
* `binomialPrice_call_tendsto_bs_closed`: for `σ, T, S₀, K > 0`, if the CRR tree is
  arbitrage-free for every size `n > 0`, its `n`-step call price tends to
  `S₀ · Φ(d₁) − K · e^{−rT} · Φ(d₂)`.

## References

* [J. C. Cox, S. A. Ross and M. Rubinstein, *Option pricing: a simplified
  approach*][CoxRossRubinstein1979]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 21.1
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  3.2

## Tags

Cox–Ross–Rubinstein, Black–Scholes formula, put–call parity, binomial convergence, call price limit,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology

/-- The discounted put expectation over the BS terminal law `N((r−σ²/2)T, σ²T)`
equals the Black–Scholes put price `K e^{−rT} Φ(−d₂) − S₀ Φ(−d₁)`. Proved by
instantiating `bs_put_formula` on that gaussian with the standardisation
`Z = (· − (r−σ²/2)T)/(σ√T)` (which has `N(0,1)` law), under which the BS
terminal `bsTerminal S₀ r σ T (Z x)` collapses to `S₀·eˣ`. -/
lemma exp_neg_mul_integral_put_gaussian_eq {r σ T S₀ K : ℝ}
    (hσ : 0 < σ) (hT : 0 < T) (hS₀ : 0 < S₀) (hK : 0 < K) :
    Real.exp (-(r * T)) * ∫ x, max (K - S₀ * Real.exp x) 0
        ∂(gaussianReal ((r - σ ^ 2 / 2) * T) (σ ^ 2 * T).toNNReal)
      = K * Real.exp (-(r * T)) * Phi (-(bsd2 S₀ K r σ T))
        - S₀ * Phi (-(bsd1 S₀ K r σ T)) := by
  set μ_bs : ℝ := (r - σ ^ 2 / 2) * T with hμ
  set ν : ℝ := σ * Real.sqrt T with hν
  have hν_pos : 0 < ν := mul_pos hσ (Real.sqrt_pos.mpr hT)
  have hσ2T_pos : 0 < σ ^ 2 * T := by positivity
  -- Standardisation `Z = (· − μ_bs)/ν` has `N(0,1)` law under the BS gaussian.
  have hlaw : HasLaw (fun x ↦ (x - μ_bs) / ν) (gaussianReal 0 1)
      (gaussianReal μ_bs (σ ^ 2 * T).toNNReal) := by
    have h1 := gaussianReal_sub_const
      (HasLaw.id (μ := gaussianReal μ_bs (σ ^ 2 * T).toNNReal)) μ_bs
    have h2 := gaussianReal_div_const h1 ν
    have hmk : NNReal.mk (ν ^ 2) (sq_nonneg _) = (σ ^ 2 * T).toNNReal := by
      apply NNReal.eq
      simp only [NNReal.coe_mk]
      rw [hν, mul_pow, Real.sq_sqrt hT.le]
      exact (Real.coe_toNNReal _ hσ2T_pos.le).symm
    have hvar : ((σ ^ 2 * T).toNNReal / NNReal.mk (ν ^ 2) (sq_nonneg _)) = 1 := by
      rw [hmk]; exact div_self (Real.toNNReal_pos.mpr hσ2T_pos).ne'
    simp only [id_eq] at h2
    convert h2 using 2
    · rw [sub_self, zero_div]
    · rw [hvar]
  have hbs : BSCallHyp (gaussianReal μ_bs (σ ^ 2 * T).toNNReal) S₀ K r σ T
      (fun x ↦ (x - μ_bs) / ν) := ⟨hS₀, hK, hσ, hT, hlaw⟩
  have hpf := bs_put_formula hbs
  -- `bsTerminal S₀ r σ T ((x − μ_bs)/ν) = S₀ · eˣ`.
  have hterm : (fun x : ℝ ↦ Real.exp (-r * T) *
        max (K - bsTerminal S₀ r σ T ((x - μ_bs) / ν)) 0)
      = (fun x : ℝ ↦ Real.exp (-r * T) * max (K - S₀ * Real.exp x) 0) := by
    funext x
    have hb : bsTerminal S₀ r σ T ((x - μ_bs) / ν) = S₀ * Real.exp x := by
      rw [bsTerminal]
      congr 2
      rw [hμ, hν]
      field_simp
      ring
    rw [hb]
  rw [hterm] at hpf
  rw [← integral_const_mul, show Real.exp (-(r * T)) = Real.exp (-r * T) from by
    rw [neg_mul]]
  exact hpf

/-- **Cox–Ross–Rubinstein → Black–Scholes, closed form.** Under no-arbitrage at
every step with `n ≥ 1`, the `n`-step CRR binomial call price converges to the *literal*
Black–Scholes call price `S₀·Φ(d₁) − K·e^{−rT}·Φ(d₂)`.

This is `binomialPrice_call_tendsto_bs` with its put-call-parity integral limit
chained, via `exp_neg_mul_integral_put_gaussian_eq` + `Phi_neg`, onto the closed
`Φ`-form. -/
theorem binomialPrice_call_tendsto_bs_closed {r σ T S₀ K : ℝ}
    (hσ : 0 < σ) (hT : 0 < T) (hS₀ : 0 < S₀) (hK : 0 < K)
    (hna : ∀ n, 0 < n → BinomialNoArb (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n)) :
    Tendsto (fun n : ℕ ↦ binomialPrice (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n)
        (fun x ↦ max (x - K) 0) n S₀) atTop
      (𝓝 (S₀ * Phi (bsd1 S₀ K r σ T)
          - K * Real.exp (-(r * T)) * Phi (bsd2 S₀ K r σ T))) := by
  have h := binomialPrice_call_tendsto_bs (K := K) hσ hT hS₀ hna
  have hkey : Real.exp (-(r * T)) * ∫ x, max (K - S₀ * Real.exp x) 0
        ∂(gaussianReal ((r - σ ^ 2 / 2) * T) (σ ^ 2 * T).toNNReal)
      + (S₀ - K * Real.exp (-(r * T)))
      = S₀ * Phi (bsd1 S₀ K r σ T)
        - K * Real.exp (-(r * T)) * Phi (bsd2 S₀ K r σ T) := by
    rw [exp_neg_mul_integral_put_gaussian_eq hσ hT hS₀ hK,
        Phi_neg (bsd2 S₀ K r σ T), Phi_neg (bsd1 S₀ K r σ T)]
    ring
  rwa [hkey] at h

end MathFin
