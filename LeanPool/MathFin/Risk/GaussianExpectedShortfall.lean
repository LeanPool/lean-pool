/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.ExpectedShortfall
public import LeanPool.MathFin.Risk.RockafellarUryasev
public import LeanPool.MathFin.Probability.Gaussian.NormalQuantile
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Expected shortfall of a Gaussian loss

`Risk/RockafellarUryasev.lean` minimizes the Rockafellar–Uryasev objective of the Gaussian
loss `L = m + σ Z`, written against the standard normal density. It finds the closed form
`gaussianCVaR m σ z α = m + σ ϕ(z)/(1 − α)` at `Φ(z) = α`. The general Rockafellar–Uryasev theorem
(`Risk/ExpectedShortfall.lean`) shows that the minimum of the same objective, written
against the law, is the expected shortfall.

The two objectives are the same function of the threshold
(`rockafellarUryasev_of_hasLaw_gaussianReal`), so the two minima agree. The Gaussian closed form is
therefore the expected shortfall of the normal law (`expectedShortfall_of_hasLaw_gaussianReal`). No
new integral is computed here. The Gaussian file supplies the value and the general theorem
supplies its meaning.

## Main results

* `rockafellarUryasev_of_hasLaw_gaussianReal`: the law-side objective equals `ruObjective`.
* `expectedShortfall_of_hasLaw_gaussianReal`: `ES_α(X) = m + σ ϕ(Φ⁻¹(α))/(1 − α)` for
  `X ~ N(m, σ²)` with `σ > 0`.
* `expectedShortfall_of_hasGaussianLaw`: the same for any Gaussian `X` (degenerate included), in
  terms of `E X` and `Var X`.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Example 2.14
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 2.17

## Tags

Gaussian expected shortfall, normal loss, Rockafellar-Uryasev, CVaR closed form, normal law,
MSC 91G70, MSC 60E05, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {α : ℝ}

omit [IsProbabilityMeasure P] in
/-- The Rockafellar–Uryasev objective of a Gaussian loss, written against its law, is the objective
`ruObjective` of `Risk/RockafellarUryasev.lean`, written against the standard normal
density. -/
theorem rockafellarUryasev_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal m v) P) (c : ℝ) :
    rockafellarUryasev X P α c = ruObjective m √(v : ℝ) α c := by
  have hlaw : ∫ ω, max (X ω - c) 0 ∂P =
      ∫ x, max (m + √(v : ℝ) * x - c) 0 * gaussianPDFReal 0 1 x := by
    calc ∫ ω, max (X ω - c) 0 ∂P = ∫ y, max (y - c) 0 ∂gaussianReal m v :=
          hX.integral_comp (f := fun y ↦ max (y - c) 0) (by fun_prop)
      _ = ∫ x, max (√(v : ℝ) * x + m - c) 0 ∂gaussianReal 0 1 := by
          rw [gaussianReal_eq_map_standard, integral_map (by fun_prop) (by fun_prop)]
      _ = ∫ x, max (m + √(v : ℝ) * x - c) 0 * gaussianPDFReal 0 1 x := by
          rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
          congr with x
          rw [smul_eq_mul, mul_comm, add_comm (√(v : ℝ) * x)]
  rw [rockafellarUryasev, ruObjective, hlaw, div_eq_inv_mul]

/-- **The expected shortfall of a Gaussian loss**: for `X ~ N(m, σ²)` with `σ > 0`,
`ES_α(X) = m + σ ϕ(Φ⁻¹(α))/(1 − α)`, the closed form `gaussianCVaR` of
`Risk/Gaussian.lean` at the normal quantile. -/
theorem expectedShortfall_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX : HasLaw X (gaussianReal m v) P) (hα : α ∈ Ioo 0 1) :
    expectedShortfall X P α = gaussianCVaR m √(v : ℝ) (PhiInv α) α := by
  have hσ : 0 < √(v : ℝ) := Real.sqrt_pos.2 (by positivity)
  have h := isLeast_rockafellarUryasev hX.hasGaussianLaw.integrable hα
  rw [show rockafellarUryasev X P α = ruObjective m √(v : ℝ) α from
    funext (rockafellarUryasev_of_hasLaw_gaussianReal hX)] at h
  exact h.unique (gaussianCVaR_isLeast_ruObjective m _ _ α hσ (Phi_PhiInv hα) hα.2)

omit [IsProbabilityMeasure P] in
/-- **The expected shortfall of a Gaussian random variable** in terms of its mean and variance:
`ES_α(X) = E X + sd(X) ϕ(Φ⁻¹(α))/(1 − α)`. A degenerate (`Var X = 0`) Gaussian is almost surely
constant, its own expected shortfall (`expectedShortfall_const`). -/
theorem expectedShortfall_of_hasGaussianLaw (hX : HasGaussianLaw X P) (hα : α ∈ Ioo 0 1) :
    expectedShortfall X P α = gaussianCVaR P[X] √Var[X; P] (PhiInv α) α := by
  have := hX.isProbabilityMeasure
  rcases (variance_nonneg X P).eq_or_lt with hv | hv
  · have h0 : X =ᵐ[P] fun _ ↦ P[X] := (evariance_eq_zero_iff hX.aemeasurable).1
      (by rw [← hX.memLp_two.ofReal_variance_eq, ← hv, ENNReal.ofReal_zero])
    have hc := expectedShortfall_const (P := P) P[X] hα
    rw [← hv, Real.sqrt_zero, gaussianCVaR, zero_mul, add_zero, ← hc]
    exact le_antisymm (expectedShortfall_mono hX.integrable (integrable_const _) h0.le hα)
      (expectedShortfall_mono (integrable_const _) hX.integrable h0.symm.le hα)
  · rw [expectedShortfall_of_hasLaw_gaussianReal (Real.toNNReal_pos.2 hv).ne'
      ⟨hX.aemeasurable, hX.map_eq_gaussianReal⟩ hα, Real.coe_toNNReal _ (variance_nonneg X P)]

end MathFin
