/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.ValueAtRisk
public import LeanPool.MathFin.Risk.Gaussian
public import LeanPool.MathFin.Probability.Gaussian.NormalQuantile
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Value-at-risk of a Gaussian loss

`Risk/Gaussian.lean` records the closed form `gaussianVaR μ σ z = μ + σ z` in a quantile
parameter `z` with `Φ(z) = α`, because the library had no `Φ⁻¹`. This file proves that the closed
form is the value-at-risk of the law: for a loss `X ~ N(m, σ²)`,

  `VaR_α(X) = m + σ Φ⁻¹(α) = gaussianVaR m σ (Φ⁻¹ α)`

(`valueAtRisk_of_hasLaw_gaussianReal`). The parameter `z` of the closed-form lemmas is forced:
`Φ z = α` holds exactly when `z = Φ⁻¹(α)` (`Phi_eq_iff`).

## Main results

* `Phi_eq_iff`: `Φ z = α ↔ z = Φ⁻¹ α` for `α ∈ (0, 1)`.
* `valueAtRisk_of_hasLaw_gaussianReal`: `VaR_α(X) = gaussianVaR m σ (Φ⁻¹ α)` for `X ~ N(m, σ²)`.
* `valueAtRisk_of_hasGaussianLaw`: the same for any Gaussian `X`, in terms of `E X` and `Var X`.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Example 2.11

## Tags

Gaussian VaR, normal quantile, inverse normal CDF, value at risk closed form, normal loss,
MSC 91G70, MSC 60E05, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ} {α : ℝ}

/-- The quantile parameter of the Gaussian closed forms is determined by the level:
`Φ z = α ↔ z = Φ⁻¹ α`. -/
theorem Phi_eq_iff (hα : α ∈ Ioo 0 1) {z : ℝ} : Phi z = α ↔ z = PhiInv α :=
  ⟨fun h ↦ h ▸ (PhiInv_Phi z).symm, fun h ↦ h ▸ Phi_PhiInv hα⟩

/-- **The value-at-risk of a Gaussian loss** is the closed form of `Risk/Gaussian.lean`
at the normal quantile: `VaR_α(X) = m + σ Φ⁻¹(α)` for `X ~ N(m, σ²)`. -/
theorem valueAtRisk_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal m v) P) (hα : α ∈ Ioo 0 1) :
    valueAtRisk X P α = gaussianVaR m √(v : ℝ) (PhiInv α) := by
  rw [valueAtRisk_eq_quantile hX, quantile_gaussianReal m v hα, gaussianVaR]

/-- **The value-at-risk of a Gaussian random variable** in terms of its mean and variance:
`VaR_α(X) = E X + sd(X) Φ⁻¹(α)`. -/
theorem valueAtRisk_of_hasGaussianLaw (hX : HasGaussianLaw X P) (hα : α ∈ Ioo 0 1) :
    valueAtRisk X P α = P[X] + √Var[X; P] * PhiInv α := by
  have := hX.isProbabilityMeasure
  rw [valueAtRisk_of_hasLaw_gaussianReal ⟨hX.aemeasurable, hX.map_eq_gaussianReal⟩ hα, gaussianVaR,
    Real.coe_toNNReal _ (variance_nonneg X P)]

end MathFin
