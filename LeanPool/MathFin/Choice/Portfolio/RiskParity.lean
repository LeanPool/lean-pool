/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Portfolio.RiskParityFOC

/-!
# Risk parity portfolio (two-asset closed form)

A risk-parity portfolio sets each asset's *contribution to variance*
`wᵢ (Σw)ᵢ` equal across assets. For two assets with positive volatilities `σ₁, σ₂`
and correlation `ρ`, the risk-parity weights under the budget constraint
`w₁ + w₂ = 1` with `w₁, w₂ > 0` are independent of `ρ`:

  `w₁^RP = σ₂ / (σ₁ + σ₂)`,
  `w₂^RP = σ₁ / (σ₁ + σ₂)`.

The independence from correlation is the surprising feature: only the
relative volatilities matter for equal-risk allocation.

## Main definitions

* `riskParityWeightTwo`: the two-asset risk-parity weight `σ₂ / (σ₁ + σ₂)` on asset 1.

## Main results

* `risk_parity_equal_contribution`: at the RP weights, the two assets'
  contributions to portfolio variance are equal.
* `isRiskParity_two_iff`: with the covariance matrix `covTwo` (`Choice/Portfolio/Markowitz.lean`)
  and the risk-parity predicate `IsRiskParity` (`Choice/Portfolio/RiskParityFOC.lean`), a long-only
  budget portfolio has equal risk contributions iff `w₁ = σ₂ / (σ₁ + σ₂)`, for every `ρ`:
  the closed form is the only long-only two-asset risk-parity portfolio (not formalised: when
  `σ₁ ≠ σ₂`, a budget portfolio with a short leg, `w₁σ₁ = −w₂σ₂`, also equalises contributions).

## References

* [Maillard, Roncalli and Te"iletche, *The properties of equally weighted risk contribution
  portfolios*][MaillardRoncalliTeiletche2010], §2

## Tags

risk parity, equal risk contribution, inverse volatility weights, two-asset portfolio,
variance contribution, MSC 91G10, JEL G11
-/

@[expose] public section

namespace MathFin

/-- Risk-parity weight on asset 1 in the two-asset case. The other asset gets
the complementary weight `σ₁ / (σ₁ + σ₂)`. -/
noncomputable def riskParityWeightTwo (σ₁ σ₂ : ℝ) : ℝ :=
  σ₂ / (σ₁ + σ₂)

/-- **Risk-parity equal-contribution identity** for two assets: at
`w₁ = σ₂/(σ₁+σ₂)`, `w₂ = σ₁/(σ₁+σ₂)`, asset 1 and asset 2 contribute
identically to portfolio variance regardless of correlation `ρ`. The
contribution of asset `i` is `w_i · (Σ·w)_i = w_i · (w_i σ_i² + w_j ρ σ_i σ_j)`. -/
theorem risk_parity_equal_contribution (σ₁ σ₂ ρ : ℝ)
    (hσ : σ₁ + σ₂ ≠ 0) :
    let w₁ := riskParityWeightTwo σ₁ σ₂
    let w₂ := riskParityWeightTwo σ₂ σ₁
    w₁ * (w₁ * σ₁^2 + w₂ * ρ * σ₁ * σ₂) =
      w₂ * (w₁ * ρ * σ₁ * σ₂ + w₂ * σ₂^2) := by
  unfold riskParityWeightTwo
  rw [show σ₂ + σ₁ = σ₁ + σ₂ from by ring]
  field_simp
  ring

/-- **Risk-parity weights sum to one**: `w₁ + w₂ = 1`. -/
lemma riskParity_weights_sum_one (σ₁ σ₂ : ℝ) (hσ : σ₁ + σ₂ ≠ 0) :
    riskParityWeightTwo σ₁ σ₂ + riskParityWeightTwo σ₂ σ₁ = 1 := by
  unfold riskParityWeightTwo
  rw [show σ₂ + σ₁ = σ₁ + σ₂ from by ring]
  field_simp
  ring

/-- **The two-asset risk-parity portfolio is unique.** For two assets with positive
volatilities and any correlation `ρ`, a long-only budget portfolio `(w₁, w₂)`
(`w₁, w₂ > 0`, `w₁ + w₂ = 1`) has equal risk contributions under `covTwo σ₁ σ₂ ρ`
(`IsRiskParity`) iff `w₁ = σ₂ / (σ₁ + σ₂)`. The reason is the factorisation
`RC₁ − RC₂ = (w₁σ₁ − w₂σ₂)(w₁σ₁ + w₂σ₂)`, in which the correlation terms cancel and the
second factor is positive. -/
theorem isRiskParity_two_iff {σ₁ σ₂ w₁ w₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (hw₁ : 0 < w₁)
    (hw₂ : 0 < w₂) (hsum : w₁ + w₂ = 1) (ρ : ℝ) :
    IsRiskParity Finset.univ (covTwo σ₁ σ₂ ρ) ![w₁, w₂] ↔ w₁ = riskParityWeightTwo σ₁ σ₂ := by
  have hRC : riskContribution Finset.univ (covTwo σ₁ σ₂ ρ) ![w₁, w₂] 0 -
      riskContribution Finset.univ (covTwo σ₁ σ₂ ρ) ![w₁, w₂] 1 =
      (w₁ * σ₁ - w₂ * σ₂) * (w₁ * σ₁ + w₂ * σ₂) := by
    simp [riskContribution, marginalVariance, covTwo, Fin.sum_univ_two]
    ring
  have hpos : w₁ * σ₁ + w₂ * σ₂ ≠ 0 := (add_pos (mul_pos hw₁ hσ₁) (mul_pos hw₂ hσ₂)).ne'
  rw [riskParityWeightTwo, eq_div_iff (add_pos hσ₁ hσ₂).ne']
  constructor
  · intro h
    have h0 := (mul_eq_zero.1 (hRC.symm.trans (sub_eq_zero.2
      (h 0 (Finset.mem_univ _) 1 (Finset.mem_univ _))))).resolve_right hpos
    linear_combination h0 + σ₂ * hsum
  · intro h i _ j _
    have h01 := sub_eq_zero.1 (hRC.trans (by
      rw [show w₁ * σ₁ - w₂ * σ₂ = 0 by linear_combination h - σ₂ * hsum, zero_mul]))
    fin_cases i <;> fin_cases j
    exacts [rfl, h01, h01.symm, rfl]

end MathFin
