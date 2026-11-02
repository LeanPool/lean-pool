/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz

/-!
# LowerFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# One-sided lower-index-family weak-Orlicz bounds

This is the literal witness scope of the lower coarse-ellipticity estimate:
one measurable random witness controls every integer cutoff at or above a
specified lower index. It is not a collection of separately chosen tails.

## References

* ABK26.
* ABK26.
-/

namespace Algsuperdiff.Section3.Probability

open MeasureTheory

/-- A single measurable witness for a lower-indexed family of one-sided bounds.

The deterministic shift appears before the witness, and the witness is chosen
before every integer index. Thus the relation is the source supremum bound,
not a family of unrelated estimates. Every member of the controlled index range
is required to be a measurable random variable. -/
structure IsLowerIntegerFamilyOrliczWithWitness {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : ℤ → Ω → ℝ) (L0 : ℤ)
    (b : ℝ) (Y : Ω → ℝ) (A : ℝ) : Prop where
  admissible : IsAdmissibleTail Ψ
  scale_pos : 0 < A
  measurable_observable : ∀ L : ℤ, L0 ≤ L → Measurable (X L)
  measurable_witness : Measurable Y
  dominates : ∀ ω, ∀ L : ℤ, L0 ≤ L → X L ω ≤ b + Y ω
  tail : HCPolySupport.IndependentSums.IsBigOWith μ Ψ Y A

/-- A lower-indexed source supremum bound with one common measurable witness. -/
def IsLowerIntegerFamilyOrlicz {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : ℤ → Ω → ℝ) (L0 : ℤ) (b A : ℝ) : Prop :=
  ∃ Y : Ω → ℝ,
    IsLowerIntegerFamilyOrliczWithWitness μ Ψ X L0 b Y A

end Algsuperdiff.Section3.Probability
