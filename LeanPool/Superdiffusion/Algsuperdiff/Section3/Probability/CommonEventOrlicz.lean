/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.TwoTermOrlicz

/-!
# CommonEventOrlicz

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Common-event two-term weak-Orlicz bounds

This module records the common-event interpretation needed by the supremum in
ABK26 Section 3.5.  A single pair of measurable envelopes dominates every
member of an indexed family on one event of full measure.  The index type may
be uncountable, so this assertion cannot be reconstructed from separate
almost-sure bounds for individual indices.

## Main definitions

* `Algsuperdiff.Section3.Probability.IsCommonEventTwoTermBigOWith`: a
  two-term one-sided weak-Orlicz bound with one full-measure domination event
  common to the entire indexed family.

## References

* ABK26, Appendix.
* ABK26, Proposition `p.homogenization.step`.
-/

namespace Algsuperdiff.Section3.Probability

open MeasureTheory

/-- A two-term one-sided weak-Orlicz bound for an indexed family on one common
event of full measure.

The witnesses are chosen before the index.  In particular, when the index
contains both a cutoff scale and a unit direction, the `Eventually` field is
one event on which the same two witnesses dominate every cutoff and every
direction. -/
def IsCommonEventTwoTermBigOWith {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ψ₁ Ψ₂ : ℝ → ℝ)
    (X : I → Ω → ℝ) (A₁ A₂ : ℝ) : Prop :=
  ∃ Y Z : Ω → ℝ,
    IsAdmissibleTail Ψ₁ ∧
      IsAdmissibleTail Ψ₂ ∧
        0 < A₁ ∧
          0 < A₂ ∧
            (∀ i : I, Measurable (X i)) ∧
              Measurable Y ∧
                Measurable Z ∧
                  (∀ᵐ ω ∂μ, ∀ i : I, X i ω ≤ Y ω + Z ω) ∧
                    HCPolySupport.IndependentSums.IsBigOWith μ Ψ₁ Y A₁ ∧
                      HCPolySupport.IndependentSums.IsBigOWith μ Ψ₂ Z A₂

end Algsuperdiff.Section3.Probability
