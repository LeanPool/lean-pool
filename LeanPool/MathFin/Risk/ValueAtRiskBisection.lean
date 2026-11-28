/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.ValueAtRisk
public import LeanPool.MathFin.Probability.Analysis.Bisection

/-!
# Value-at-risk by bisection

`Probability/Analysis/Bisection.lean` proves that bisection for `f x = C` converges to the
*threshold* of
`f` against `C`: the point `σ` with `f x < C ↔ x < σ` on the bracket. It needs no continuity or
strict monotonicity of `f`. The Galois connection of the quantile function (`lt_valueAtRisk_iff`)
says that `VaR_α(X)` is exactly the threshold of the distribution function `x ↦ P(X ≤ x)` against
`α`. So bisection on the distribution function computes value-at-risk for every law, including
atoms and flat stretches, and after `n` steps the midpoint is within `(hi − lo)/2^{n+1}`.

This is the consumer the bisection file was generalized for: a right-continuous CDF at its
quantile, where neither continuity nor strictness holds in general.

## Main results

* `valueAtRisk_mem_Icc_of_bracket`: a CDF bracket `P(X ≤ lo) < α ≤ P(X ≤ hi)` brackets VaR.
* `abs_bisectMid_sub_valueAtRisk_le`: the `n`-th estimate is within `(hi − lo)/2^{n+1}` of VaR.
* `tendsto_bisectMid_valueAtRisk`: bisection on the distribution function converges to VaR.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Chapter 9

## Tags

VaR computation, bisection method, quantile numerical, distribution function threshold,
root finding, MSC 91G60, MSC 91G70, JEL C63
-/

@[expose] public section

namespace MathFin

open MeasureTheory Set Filter Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {α lo hi : ℝ}

/-- A bracket of the distribution function brackets VaR: if `P(X ≤ lo) < α ≤ P(X ≤ hi)` then
`VaR_α(X) ∈ [lo, hi]`. Both conditions can be checked by evaluating the CDF. -/
lemma valueAtRisk_mem_Icc_of_bracket (hX : AEMeasurable X P) (hα : α ∈ Ioo 0 1)
    (hlo : P.real {ω | X ω ≤ lo} < α) (hhi : α ≤ P.real {ω | X ω ≤ hi}) :
    valueAtRisk X P α ∈ Icc lo hi :=
  ⟨((lt_valueAtRisk_iff hX hα).2 hlo).le, (valueAtRisk_le_iff hX hα).2 hhi⟩

/-- **The a-priori error of VaR by bisection**: the `n`-th midpoint of bisection on the
distribution function is within `(hi − lo)/2^{n+1}` of `VaR_α(X)`. -/
theorem abs_bisectMid_sub_valueAtRisk_le (hX : AEMeasurable X P) (hα : α ∈ Ioo 0 1)
    (hlo : P.real {ω | X ω ≤ lo} < α) (hhi : α ≤ P.real {ω | X ω ≤ hi}) (n : ℕ) :
    |bisectMid (fun x ↦ P.real {ω | X ω ≤ x}) α lo hi n - valueAtRisk X P α| ≤
      (hi - lo) / 2 ^ (n + 1) :=
  abs_bisectMid_sub_le (fun _ _ ↦ (lt_valueAtRisk_iff hX hα).symm)
    (valueAtRisk_mem_Icc_of_bracket hX hα hlo hhi) n

/-- **VaR by bisection**: bisection on the distribution function `x ↦ P(X ≤ x)` against the level
`α` converges to `VaR_α(X)`, for every law. -/
theorem tendsto_bisectMid_valueAtRisk (hX : AEMeasurable X P) (hα : α ∈ Ioo 0 1)
    (hlo : P.real {ω | X ω ≤ lo} < α) (hhi : α ≤ P.real {ω | X ω ≤ hi}) :
    Tendsto (bisectMid (fun x ↦ P.real {ω | X ω ≤ x}) α lo hi) atTop
      (𝓝 (valueAtRisk X P α)) :=
  tendsto_bisectMid (fun _ _ ↦ (lt_valueAtRisk_iff hX hα).symm)
    (valueAtRisk_mem_Icc_of_bracket hX hα hlo hhi)

end MathFin
