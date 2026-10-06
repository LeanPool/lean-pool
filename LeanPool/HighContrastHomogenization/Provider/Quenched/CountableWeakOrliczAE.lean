/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.Triangle

/-!
# High-contrast homogenization: Provider.Quenched.CountableWeakOrliczAE

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Almost-everywhere countable weak-Orlicz summation

This file gives the a.e.-safe counterpart of the pointwise countable summation
theorem.  A pointwise limit outside one null set inherits a uniform weak-Orlicz
bound.  For an a.e. summable series, `AEMeasurable.mk` then supplies a measurable
representative of the raw `tsum` without imposing summability on null outcomes.
-/

namespace HCPolySupport
namespace IndependentSums

open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `tsum` of measurable real summands is a.e.-measurable when the series is
summable almost everywhere. -/
theorem aemeasurable_tsum_of_ae_summable {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hXSummable : ∀ᵐ ω ∂μ, Summable fun i => X i ω) :
    AEMeasurable (fun ω => ∑' i, X i ω) μ := by
  apply aemeasurable_of_tendsto_metrizable_ae'
      (f := fun n ω => ∑ i ∈ Finset.range n, X i ω)
  · intro n
    exact (Finset.measurable_sum (s := Finset.range n) fun i _ => hXm i).aemeasurable
  · filter_upwards [hXSummable] with ω hω
    exact hω.hasSum.tendsto_sum_nat

end

end IndependentSums
end HCPolySupport
