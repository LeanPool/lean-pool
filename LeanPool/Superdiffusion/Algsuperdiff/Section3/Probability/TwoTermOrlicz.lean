/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Basic

/-!
# TwoTermOrlicz

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Two-term weak-Orlicz bounds

This module formalizes the one-sided two-term weak-Orlicz notation of the
ABK26 Appendix. It records the source admissibility conditions on tail
functions, measurable witness random variables, and a pointwise
decomposition, without replacing the paper's one-sided tails by symmetric
ones.

## Main definitions

* `Algsuperdiff.Section3.Probability.IsTwoTermBigOWithWitnesses`: a fixed
  measurable witness pair for a two-term weak-Orlicz bound.
* `Algsuperdiff.Section3.Probability.IsTwoTermBigOWith`: the assertion
  `X ≤ O_{Ψ₁}(A₁) + O_{Ψ₂}(A₂)`.
* `Algsuperdiff.Section3.Probability.IsAdmissibleTail`: the Appendix
  conditions on a tail function.

## References

* ABK26, Appendix.
-/

namespace Algsuperdiff.Section3.Probability

open MeasureTheory

/-- The admissibility conditions imposed on a tail function in the ABK26
Appendix: it is increasing on the nonnegative reals, takes values at least
one there, and its reciprocal has the stated weighted integrability. -/
def IsAdmissibleTail (Ψ : ℝ → ℝ) : Prop :=
  HCPolySupport.IndependentSums.AdmissiblePsi Ψ ∧
    IntegrableOn (fun t : ℝ ↦ t / Ψ t) (Set.Ici 1) volume

/-- The stretched-exponential tail function satisfies the Appendix
admissibility conditions whenever its exponent is positive. -/
theorem isAdmissibleTail_gammaSigma {σ : ℝ} (hσ : 0 < σ) :
    IsAdmissibleTail (HCPolySupport.IndependentSums.gammaSigma σ) := by
  refine ⟨HCPolySupport.IndependentSums.admissiblePsi_gammaSigma hσ.le, ?_⟩
  have hKernel :
      IntegrableOn (fun t : ℝ ↦ t * Real.exp (-(t ^ σ))) (Set.Ioi 0) := by
    simpa [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using
      (HCPolySupport.IndependentSums.integrableOn_rpow_mul_exp_neg_rpow_of_pos
        (σ := σ) (p := 2) hσ (by norm_num : 0 < (2 : ℝ)))
  have hIoi :
      IntegrableOn (fun t : ℝ ↦ t / HCPolySupport.IndependentSums.gammaSigma σ t)
        (Set.Ioi 1) := by
    refine (integrableOn_congr_fun ?_ measurableSet_Ioi).2
      (hKernel.mono_set (by
        intro t ht
        change 1 < t at ht
        change 0 < t
        exact lt_trans zero_lt_one ht))
    intro t ht
    simp [HCPolySupport.IndependentSums.gammaSigma, div_eq_mul_inv, Real.exp_neg]
  exact (integrableOn_Ici_iff_integrableOn_Ioi).2 hIoi

/-- A fixed witness pair for the one-sided two-term weak-Orlicz relation.

The tail functions are Appendix-admissible, the scales are positive, all three
random variables are measurable, `X` is pointwise bounded above by `Y + Z`,
and the two witnesses satisfy their respective one-sided weak-Orlicz tails. -/
def IsTwoTermBigOWithWitnesses {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ψ₁ Ψ₂ : ℝ → ℝ) (X Y Z : Ω → ℝ) (A₁ A₂ : ℝ) : Prop :=
  IsAdmissibleTail Ψ₁ ∧
    IsAdmissibleTail Ψ₂ ∧
      0 < A₁ ∧
        0 < A₂ ∧
          Measurable X ∧
            Measurable Y ∧
              Measurable Z ∧
                (∀ ω, X ω ≤ Y ω + Z ω) ∧
                  HCPolySupport.IndependentSums.IsBigOWith μ Ψ₁ Y A₁ ∧
                    HCPolySupport.IndependentSums.IsBigOWith μ Ψ₂ Z A₂

/-- The one-sided two-term weak-Orlicz relation of the ABK26 Appendix.

`IsTwoTermBigOWith μ Ψ₁ Ψ₂ X A₁ A₂` means that the positive scales `A₁` and
`A₂` control measurable witnesses `Y` and `Z`, respectively, and that `X` is
pointwise bounded above by their sum. Each witness has the source's one-sided
weak-Orlicz tail, implemented by `IndependentSums.IsBigOWith`. -/
def IsTwoTermBigOWith {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ψ₁ Ψ₂ : ℝ → ℝ) (X : Ω → ℝ) (A₁ A₂ : ℝ) : Prop :=
  ∃ Y Z : Ω → ℝ,
    IsTwoTermBigOWithWitnesses μ Ψ₁ Ψ₂ X Y Z A₁ A₂

end Algsuperdiff.Section3.Probability
