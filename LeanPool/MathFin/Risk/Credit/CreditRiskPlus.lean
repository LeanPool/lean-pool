/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Laws.GammaPoissonMixturePgf
public import LeanPool.MathFin.Probability.Jumps.CompoundPoissonMGF

/-!
# The CreditRisk+ sector loss MGF

In CreditRisk+ (Credit Suisse First Boston, *CreditRisk+: A Credit Risk Management Framework*,
1997) the number of defaults in a sector is Poisson with a random intensity `Λ ∼ Gamma(a, r)`,
and each default causes a loss drawn independently from a common severity law. The sector loss
`L = ∑_{i < N} Xᵢ` is then a compound Poisson sum whose Poisson intensity is mixed against the
Gamma law.

This file joins the two layers the library already has. The MGF of the `n`-loss sum is
`M_X(t)ⁿ` (`mgf_range_sum_of_iid`, `Probability/Jumps/CompoundPoissonMGF.lean`), so the mixture is
the Poisson–Gamma sector pgf (`integral_integral_pow_poissonMeasure_gammaMeasure`,
`Probability/Laws/GammaPoissonMixturePgf.lean`) evaluated at `z = M_X(t)`. For `M_X(t) < r + 1`,

  `∫ λ, (∫ n, M_{∑_{i<n} Xᵢ}(t) dPoisson(λ)) dGamma(a, r) = (r / (r − (M_X(t) − 1)))^a`

(`integral_compoundPoisson_mgf_gammaMeasure`). Equivalently, given `Λ = λ` the inner integral is
the compound-Poisson MGF `exp(λ (M_X(t) − 1))` (`compoundPoisson_mgf`), and the outer integral is
the Gamma moment-generating function at `M_X(t) − 1`.

Scope: the statement is the iterated (mixture) integral. A random sector count `N` with this
conditional law, the sector loss `L` as a random variable, the portfolio across independent sectors
and CreditRisk+'s loss-banding recursion are not constructed.

## Main results

* `integral_compoundPoisson_mgf_gammaMeasure`: for i.i.d. losses `Xᵢ`, `a, r > 0` and
  `M_X(t) < r + 1`, the compound-Poisson MGF `∫ n, M_{∑_{i<n} Xᵢ}(t) dPoisson(λ)` integrated
  against `Gamma(a, r)` in `λ` is `(r / (r − (M_X(t) − 1)))^a`.

## References

* [Credit Suisse First Boston, *CreditRisk+: A Credit Risk Management Framework*][CSFB1997]

## Tags

CreditRisk+, Poisson-Gamma mixture, compound Poisson, sector loss, moment generating function,
actuarial credit risk model, MSC 91G40, MSC 60E10, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

/-- **The CreditRisk+ sector loss MGF** (mixture form). For i.i.d. losses `Xᵢ` with common MGF
`M_X(t)`, a Poisson count with intensity `λ`, and the intensity mixed against `Gamma(a, r)`
(`a, r > 0`): if `M_X(t) < r + 1`, the compound-Poisson MGF `∫ n, M_{∑_{i<n} Xᵢ}(t) dPoisson(λ)`
integrated against `Gamma(a, r)` is `(r / (r − (M_X(t) − 1)))^a`. -/
theorem integral_compoundPoisson_mgf_gammaMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (X : ℕ → Ω → ℝ)
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hM : mgf (X 0) μ t < r + 1) :
    ∫ lam, (∫ n, mgf (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) μ t ∂poissonMeasure lam.toNNReal)
        ∂gammaMeasure a r =
      (r / (r - (mgf (X 0) μ t - 1))) ^ a := by
  simp_rw [mgf_range_sum_of_iid t X hindep hident]
  exact GammaPoissonMixturePgf.integral_integral_pow_poissonMeasure_gammaMeasure ha hr hM

end MathFin
