/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.Gaussian
public import LeanPool.MathFin.Probability.Gaussian.NormalQuantile

/-!
# Gaussian VaR/CVaR additivity at perfect positive correlation

At `ρ = 1`, the joint-gaussian standard deviation becomes
`√(σ₁² + 2 σ₁ σ₂ + σ₂²) = σ₁ + σ₂` and the subadditivity inequality from
`Risk.CoherentAxioms` is sharpened to equality. This is the extremal
case where diversification provides no benefit.

## Main results

* `gaussianVaR_additive_at_rho_one`: at `ρ = 1`, VaR is additive.
* `gaussianCVaR_additive_at_rho_one`: at `ρ = 1`, CVaR is additive.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Ch 8

## Tags

VaR additivity, CVaR additivity, perfect correlation, Gaussian risk, diversification benefit,
MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin

open Real

/-- **Gaussian VaR additivity at perfect positive correlation** (`ρ = 1`):
the joint stdev becomes `σ₁ + σ₂` and the subadditivity inequality is an
equality. -/
lemma gaussianVaR_additive_at_rho_one {μ₁ μ₂ σ₁ σ₂ z : ℝ}
    (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) :
    gaussianVaR (μ₁ + μ₂)
        (Real.sqrt (σ₁^2 + 2 * 1 * σ₁ * σ₂ + σ₂^2)) z =
      gaussianVaR μ₁ σ₁ z + gaussianVaR μ₂ σ₂ z := by
  unfold gaussianVaR
  have h_sum_sq : σ₁^2 + 2 * 1 * σ₁ * σ₂ + σ₂^2 = (σ₁ + σ₂)^2 := by ring
  rw [h_sum_sq]
  have h_sum_nn : 0 ≤ σ₁ + σ₂ := add_nonneg h₁ h₂
  rw [Real.sqrt_sq h_sum_nn]
  ring

/-- **Gaussian CVaR additivity at perfect positive correlation** (`ρ = 1`). -/
lemma gaussianCVaR_additive_at_rho_one {μ₁ μ₂ σ₁ σ₂ z α : ℝ}
    (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) :
    gaussianCVaR (μ₁ + μ₂)
        (Real.sqrt (σ₁^2 + 2 * 1 * σ₁ * σ₂ + σ₂^2)) z α =
      gaussianCVaR μ₁ σ₁ z α + gaussianCVaR μ₂ σ₂ z α := by
  unfold gaussianCVaR
  have h_sum_sq : σ₁^2 + 2 * 1 * σ₁ * σ₂ + σ₂^2 = (σ₁ + σ₂)^2 := by ring
  rw [h_sum_sq]
  have h_sum_nn : 0 ≤ σ₁ + σ₂ := add_nonneg h₁ h₂
  rw [Real.sqrt_sq h_sum_nn]
  ring

end MathFin
