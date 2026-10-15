/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.TwoTermOrlicz

/-!
# OneSidedOrlicz

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# One-sided weak-Orlicz relations

The ABK26 Appendix uses one-sided weak-Orlicz bounds for random variables, with
measurable witnesses in its additive notation.  This file records the literal
one-term relation and its deterministic-shift A.  The canonical two-term
relation is `IsTwoTermBigOWith` from `TwoTermOrlicz`; it is reused here rather
than duplicated.  CoarseGraining's tail-event predicate does not itself carry
measurability, so the source's random-variable requirement is stated explicitly
here.

## References

* ABK26.
* ABK26, the main-text uses of the one-sided bound.
-/

namespace Algsuperdiff.Section3.Probability

open MeasureTheory

/-- The Appendix-literal source notation `X ≤ O_Ψ(A)`: `X` is a measurable
random variable with the stated one-sided upper tail at the positive scale
`A`. -/
def IsOneSidedOrlicz {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : Ω → ℝ) (A : ℝ) : Prop :=
  IsAdmissibleTail Ψ ∧
    0 < A ∧
      Measurable X ∧
        HCPolySupport.IndependentSums.IsBigOWith μ Ψ X A

/-- The source notation `X ≤ b + O_Ψ(A)` for a deterministic shift `b`. -/
def IsDeterministicShiftOneSidedOrlicz {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : Ω → ℝ) (b A : ℝ) : Prop :=
  IsAdmissibleTail Ψ ∧
    0 < A ∧
      Measurable X ∧
        HCPolySupport.IndependentSums.IsBigOWith μ Ψ (fun ω ↦ X ω - b) A

/-- The source notation `X ≤ b + O_{Ψ₁}(A₁) + O_{Ψ₂}(A₂)` for a deterministic
shift `b`. -/
def IsDeterministicShiftTwoTermOneSidedOrlicz {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ψ₁ Ψ₂ : ℝ → ℝ) (X : Ω → ℝ) (b A₁ A₂ : ℝ) : Prop :=
  Measurable X ∧ IsTwoTermBigOWith μ Ψ₁ Ψ₂ (fun ω ↦ X ω - b) A₁ A₂

theorem deterministicShiftTwoTermOneSidedOrlicz_iff_exists
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Ψ₁ Ψ₂ : ℝ → ℝ}
    {X : Ω → ℝ} {b A₁ A₂ : ℝ} :
    IsDeterministicShiftTwoTermOneSidedOrlicz μ Ψ₁ Ψ₂ X b A₁ A₂ ↔
      ∃ Y Z : Ω → ℝ,
        IsAdmissibleTail Ψ₁ ∧
          IsAdmissibleTail Ψ₂ ∧
            0 < A₁ ∧
              0 < A₂ ∧
                Measurable X ∧
                  Measurable Y ∧
                    Measurable Z ∧
                      (∀ ω, X ω ≤ b + Y ω + Z ω) ∧
                        HCPolySupport.IndependentSums.IsBigOWith μ Ψ₁ Y A₁ ∧
                          HCPolySupport.IndependentSums.IsBigOWith μ Ψ₂ Z A₂ := by
  constructor
  · rintro ⟨hXmeas, Y, Z, hLeft, hRight, hA₁, hA₂, _hShiftMeas,
      hYmeas, hZmeas, hDom, hYtail, hZtail⟩
    refine ⟨Y, Z, hLeft, hRight, hA₁, hA₂, hXmeas, hYmeas, hZmeas, ?_,
      hYtail, hZtail⟩
    intro ω
    linarith [hDom ω]
  · rintro ⟨Y, Z, hLeft, hRight, hA₁, hA₂, hXmeas, hYmeas, hZmeas, hDom, hYtail, hZtail⟩
    refine ⟨hXmeas, Y, Z, hLeft, hRight, hA₁, hA₂, ?_, hYmeas, hZmeas, ?_, hYtail, hZtail⟩
    · exact hXmeas.sub measurable_const
    intro ω
    linarith [hDom ω]

open HCPolySupport.IndependentSums in
/-- Clamping a witness below at zero preserves its one-sided tail at every
positive scale, without requiring measurability or a finite measure. -/
theorem isBigOWith_max_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Ψ : ℝ → ℝ} {Y : Ω → ℝ} {A : ℝ} (hA : 0 < A)
    (hY : IsBigOWith μ Ψ Y A) :
    IsBigOWith μ Ψ (fun ω => max 0 (Y ω)) A := by
  intro t ht
  have hAt : 0 < A * t := mul_pos hA (lt_of_lt_of_le zero_lt_one ht)
  have hsets :
      upperTailEvent (fun ω => max 0 (Y ω)) (A * t) = upperTailEvent Y (A * t) := by
    ext ω
    simp only [mem_upperTailEvent, lt_max_iff]
    constructor
    · rintro (hω | hω)
      · exact absurd hω (not_lt.2 hAt.le)
      · exact hω
    · exact Or.inr
  rw [hsets]
  exact hY ht

open HCPolySupport in
/-- A pointwise zero observable has every nonnegative Gamma scale. The tail
event is empty, so measurability and measure finiteness are unnecessary. -/
theorem isBigOWith_gammaSigma_of_eq_zero {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} {X : Omega → ℝ} {sigma A : ℝ}
    (hA : 0 ≤ A) (hX : ∀ omega, X omega = 0) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) X A := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hAt : (0 : ℝ) ≤ A * t := mul_nonneg hA ht0
  have hset : IndependentSums.upperTailEvent X (A * t) = (∅ : Set Omega) := by
    ext omega
    simp only [IndependentSums.mem_upperTailEvent, hX omega,
      Set.mem_empty_iff_false, iff_false, not_lt]
    exact hAt
  rw [hset, measureReal_empty]
  have h1 : (1 : ℝ) ≤ IndependentSums.gammaSigma sigma t :=
    IndependentSums.one_le_gammaSigma ht0
  exact inv_nonneg.2 (by linarith)

end Algsuperdiff.Section3.Probability
