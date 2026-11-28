/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.Concentration
public import LeanPool.MathFin.Choice.Portfolio.MarkowitzNAsset
public import LeanPool.MathFin.Risk.GaussianRiskMarkowitz

/-!
# Concentration is diversifiable variance

For uncorrelated assets of common variance `σ²`, the N-asset Markowitz portfolio
variance equals `σ²` times the Herfindahl–Hirschman concentration index
(`portfolioVarN_diag_eq_herfindahl`). This ties `Risk/Concentration.lean` to
`Choice/Portfolio/MarkowitzNAsset.lean`: the diversifiable part of portfolio variance *is* the
concentration metric. It is the `ρ = 0` case of the equicorrelated decomposition
`portfolioVarN_equicorrelated_eq_herfindahl` (`Risk/EquicorrelationConcentration.lean`),
`Var(w) = v ((1 − ρ) HHI(w) + ρ (∑ wᵢ)²)`, where the systematic term vanishes.

For a Gaussian vector of pairwise uncorrelated risk factors with common variance `v`, the
portfolio loss `∑ wᵢXᵢ` is Gaussian with variance `v · HHI(w)`, so its value-at-risk is
`∑ wᵢ E Xᵢ + √(v · HHI(w)) · Φ⁻¹(α)` (`valueAtRisk_portfolio_gaussian_uncorrelated`, from
`valueAtRisk_portfolio_gaussian` of `Risk/GaussianRiskMarkowitz.lean`). The VaR in excess of
the mean scales with the square root of the concentration index. A certified unification of
known textbook facts, not new finance.

## Main results

* `portfolioVarN_diag_eq_herfindahl`: if the covariances `σ i j` vanish off the diagonal on `s`
  and `σ i i = σ_sq` on `s`, then `portfolioVarN s w σ = σ_sq * herfindahl s w`.
* `valueAtRisk_portfolio_gaussian_uncorrelated`: for a Gaussian vector `X` of pairwise
  uncorrelated factors with common variance `v` and `α ∈ (0, 1)`, `valueAtRisk` of `∑ wᵢXᵢ` at
  level `α` is `∑ wᵢ E Xᵢ + √(v * herfindahl univ w) * PhiInv α`.

## References

* [H. Markowitz, *Portfolio selection*][Markowitz1952]
* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Example 2.11

## Tags

Herfindahl index, portfolio concentration, Markowitz variance, diversification,
Gaussian value-at-risk, MSC 91G10, MSC 91G70, JEL G11
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

/-- **Concentration × variance bridge.** Diagonal covariance with common
variance `σ_sq` ⇒ `Var(w) = σ_sq · HHI(w)`. This is the `ρ = 0` case of
`portfolioVarN_equicorrelated_eq_herfindahl`. -/
theorem portfolioVarN_diag_eq_herfindahl {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (σ : ι → ι → ℝ) (σ_sq : ℝ)
    (h_diag : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → σ i j = 0)
    (h_var : ∀ i ∈ s, σ i i = σ_sq) :
    portfolioVarN s w σ = σ_sq * herfindahl s w := by
  rw [portfolioVarN_diag s w σ h_diag]
  unfold herfindahl
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [h_var i hi]; ring

/-- **Uncorrelated Gaussian VaR is concentration**: for a Gaussian vector `X` of pairwise
uncorrelated risk factors with common variance `v` and `α ∈ (0, 1)`,
`VaR_α(∑ wᵢXᵢ) = ∑ wᵢ E Xᵢ + √(v · HHI(w)) · Φ⁻¹(α)`. -/
theorem valueAtRisk_portfolio_gaussian_uncorrelated {ι : Type*} [Fintype ι]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ} {α v : ℝ}
    (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (hvar : ∀ i, Var[X i; P] = v)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; P] = 0) (w : ι → ℝ) (hα : α ∈ Ioo 0 1) :
    valueAtRisk (fun ω ↦ ∑ i, w i * X i ω) P α =
      ∑ i, w i * P[X i] + √(v * herfindahl Finset.univ w) * PhiInv α := by
  rw [valueAtRisk_portfolio_gaussian hX w hα,
    portfolioVarN_diag_eq_herfindahl Finset.univ w _ v (fun i _ j _ hij ↦ hcov i j hij)
      fun i _ ↦ (covariance_self (hX.eval i).aemeasurable).trans (hvar i)]

end MathFin
