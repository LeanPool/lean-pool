/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.WeakOrlicz
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# CenteredIndicator

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weak-Orlicz pricing of indicators and of centered indicators

ABK26's estimate `e.indc.O.sigma` prices the indicator of a rare event, `1_E ≤
O_{Γ_σ}(|log ℙ[E]|^{-1/σ})`.  CoarseGraining proves that estimate at the exact
scale `gammaIndicatorScale σ ℙ[E] = (-log ℙ[E])^{-1/σ}`, under the standing
assumption `0 < ℙ[E] < 1`.

Two adjustments are needed before the estimate can feed the ABK26 concentration
inequality, and both are supplied here.

* Call sites carry a *majorant* of the scale, in the form `ℙ[E] ≤ exp(-A^{-σ})`,
  and must tolerate a null event. `isBigOWith_gammaSigma_indicator_of_le` proves
  the indicator bound directly at such an `A`, with no positivity assumption on
  `ℙ[E]`.
* The concentration inequality consumes *centered*, *two-sided* summands.

## Main results

* `Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_indicator_of_le`
* `Algsuperdiff.Section3.Provider.Orlicz.isBigO_gammaSigma_indicator_sub_measureReal`
* `Algsuperdiff.Section3.Provider.Orlicz.exp_neg_rpow_neg_two_le`
* `Algsuperdiff.Section3.Provider.Orlicz.isBigO_gammaSigma_two_indicator_sub_measureReal`

## References

* ABK26, `e.indc.O.sigma`.
* ABK26, Step 1 of `l.percolation.bound.general`.
-/

namespace Algsuperdiff.Section3.Provider.Orlicz

open MeasureTheory
open HCPolySupport.IndependentSums

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Indicator pricing at a majorant scale.**

If `ℙ[E] ≤ exp(-A^{-σ})` with `A > 0` then `1_E ≤ O_{Γ_σ}(A)`. -/
theorem isBigOWith_gammaSigma_indicator_of_le [IsFiniteMeasure μ]
    {E : Set Ω} {σ A : ℝ} (hσ : 0 ≤ σ) (hA : 0 < A)
    (hE : μ.real E ≤ Real.exp (-(A ^ (-σ)))) :
    IsBigOWith μ (gammaSigma σ) (E.indicator fun _ => (1 : ℝ)) A := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hAt : 0 < A * t := mul_pos hA (lt_of_lt_of_le zero_lt_one ht)
  rcases le_or_gt 1 (A * t) with hge | hlt
  · have hset : upperTailEvent (E.indicator fun _ => (1 : ℝ)) (A * t) = (∅ : Set Ω) := by
      ext ω
      simp only [mem_upperTailEvent, Set.mem_empty_iff_false, iff_false, not_lt]
      by_cases hω : ω ∈ E
      · simpa only [Set.indicator_of_mem hω] using hge
      · simpa only [Set.indicator_of_notMem hω] using hAt.le
    rw [hset, measureReal_empty]
    positivity
  · have hsub : upperTailEvent (E.indicator fun _ => (1 : ℝ)) (A * t) ⊆ E := by
      intro ω hω
      by_contra hcon
      rw [mem_upperTailEvent] at hω
      simp only [Set.indicator_of_notMem hcon] at hω
      exact absurd hω (not_lt.mpr hAt.le)
    have hpow : t ^ σ ≤ A ^ (-σ) := by
      have hApos : 0 < A ^ σ := Real.rpow_pos_of_pos hA σ
      have hmul : A ^ σ * t ^ σ ≤ 1 := by
        rw [← Real.mul_rpow hA.le ht0]
        exact Real.rpow_le_one hAt.le hlt.le hσ
      rw [Real.rpow_neg hA.le]
      refine le_of_mul_le_mul_right ?_ hApos
      rw [inv_mul_cancel₀ hApos.ne']
      linarith
    calc μ.real (upperTailEvent (E.indicator fun _ => (1 : ℝ)) (A * t))
        ≤ μ.real E := measureReal_mono hsub (measure_ne_top μ E)
      _ ≤ Real.exp (-(A ^ (-σ))) := hE
      _ ≤ Real.exp (-(t ^ σ)) := Real.exp_le_exp.mpr (by linarith)

/-- **Centered indicator pricing.**

For a rare event `E` with `ℙ[E] ≤ exp(-A^{-σ})` and `ℙ[E] ≤ A`, the centered
indicator satisfies the two-sided relation `1_E - ℙ[E] = O_{Γ_σ}(2A)`. This is
the form required by the ABK26 concentration inequality, which consumes centered
summands with two-sided tails. -/
theorem isBigO_gammaSigma_indicator_sub_measureReal [IsProbabilityMeasure μ]
    {E : Set Ω} {σ A : ℝ} (hσ : 0 ≤ σ) (hA : 0 < A)
    (hE : μ.real E ≤ Real.exp (-(A ^ (-σ)))) (hpA : μ.real E ≤ A) :
    IsBigO μ (gammaSigma σ)
      (fun ω => E.indicator (fun _ => (1 : ℝ)) ω - μ.real E) (2 * A) := by
  have hraw := isBigOWith_gammaSigma_indicator_of_le (μ := μ) hσ hA hE
  rw [isBigOWith_gammaSigma_iff] at hraw
  rw [isBigO_gammaSigma_iff]
  intro t ht
  have hp0 : (0 : ℝ) ≤ μ.real E := measureReal_nonneg
  have hp1 : μ.real E ≤ 1 := measureReal_le_one
  have hAt : A ≤ A * t := le_mul_of_one_le_right hA.le ht
  have hsub :
      absTailEvent (fun ω => E.indicator (fun _ => (1 : ℝ)) ω - μ.real E) (2 * A * t) ⊆
        upperTailEvent (E.indicator fun _ => (1 : ℝ)) (A * t) := by
    intro ω hω
    rw [mem_absTailEvent] at hω
    rw [mem_upperTailEvent]
    have hbound : |E.indicator (fun _ => (1 : ℝ)) ω - μ.real E| ≤
        E.indicator (fun _ => (1 : ℝ)) ω + A := by
      by_cases hmem : ω ∈ E
      · simp only [Set.indicator_of_mem hmem]
        rw [abs_of_nonneg (by linarith)]
        linarith [hA.le]
      · simp only [Set.indicator_of_notMem hmem]
        rw [zero_sub, abs_neg, abs_of_nonneg hp0]
        linarith
    linarith
  calc μ.real
        (absTailEvent (fun ω => E.indicator (fun _ => (1 : ℝ)) ω - μ.real E) (2 * A * t))
      ≤ μ.real (upperTailEvent (E.indicator fun _ => (1 : ℝ)) (A * t)) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ Real.exp (-(t ^ σ)) := hraw ht

/-- For `0 < A ≤ 1` the tail bound `exp(-A^{-2})` is itself at most `A`. This is
the elementary inequality that makes the hypothesis `ℙ[E] ≤ A` of
`isBigO_gammaSigma_indicator_sub_measureReal` automatic at `σ = 2`. -/
theorem exp_neg_rpow_neg_two_le {A : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) :
    Real.exp (-(A ^ (-(2 : ℝ)))) ≤ A := by
  have hpow : A ^ (-(2 : ℝ)) = (A ^ 2)⁻¹ := by
    rw [Real.rpow_neg hA.le, ← Real.rpow_natCast A 2]
    norm_num
  have hsq_pos : (0 : ℝ) < A ^ 2 := by positivity
  have hv_pos : (0 : ℝ) < (A ^ 2)⁻¹ := inv_pos.mpr hsq_pos
  have hexp : (A ^ 2)⁻¹ ≤ Real.exp ((A ^ 2)⁻¹) := by
    have := Real.add_one_le_exp ((A ^ 2)⁻¹)
    linarith
  calc Real.exp (-(A ^ (-(2 : ℝ)))) = (Real.exp ((A ^ 2)⁻¹))⁻¹ := by
        rw [hpow, Real.exp_neg]
    _ ≤ ((A ^ 2)⁻¹)⁻¹ := by
        exact inv_anti₀ hv_pos hexp
    _ = A ^ 2 := inv_inv _
    _ ≤ A := by nlinarith

/-- **Centered indicator pricing at `σ = 2`, in call-site form.**

For `0 < A ≤ 1` and `ℙ[E] ≤ exp(-A^{-2})`, the centered indicator satisfies
`1_E - ℙ[E] = O_{Γ₂}(2A)`. This is the exact form consumed by Step 1 of ABK26's
`l.percolation.bound.general`, where `A = T^{-1} 3^{-aL/2}` and the tail
hypothesis is `ℙ[B_L(z)] ≤ exp(-T² 3^{aL})`. -/
theorem isBigO_gammaSigma_two_indicator_sub_measureReal [IsProbabilityMeasure μ]
    {E : Set Ω} {A : ℝ} (hA : 0 < A) (hA1 : A ≤ 1)
    (hE : μ.real E ≤ Real.exp (-(A ^ (-(2 : ℝ))))) :
    IsBigO μ (gammaSigma 2)
      (fun ω => E.indicator (fun _ => (1 : ℝ)) ω - μ.real E) (2 * A) :=
  isBigO_gammaSigma_indicator_sub_measureReal (by norm_num) hA hE
    (hE.trans (exp_neg_rpow_neg_two_le hA hA1))

end Algsuperdiff.Section3.Provider.Orlicz
