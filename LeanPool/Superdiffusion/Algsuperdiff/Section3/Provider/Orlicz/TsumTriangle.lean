/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Operations
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.ConcentrationAEMeasurable
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# TsumTriangle

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Countable generalized triangle inequality for stretched-exponential tails

This module upgrades the finite-family weak-Orlicz triangle inequality of
CoarseGraining to a countable family, which is the form used by the ABK26
Appendix.

CoarseGraining proves the finite-family estimate
`Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma` with
the explicit constant `gammaTriangleConst σ`.  The countable statement is
obtained by continuity from below: for a nonnegative family the partial-sum
upper-tail events increase to the upper-tail event of the series, and each of
them is controlled at the common scale `gammaTriangleConst σ * ∑' k, a k`.

## Main results

* `Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg`: for a
  pointwise nonnegative random variable the one-sided and symmetric weak-Orlicz
  relations coincide.
* `Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_tsum_of_isBigOWith_sum_range_succ`:
  continuity from below for a general tail function `Ψ`.
* `Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_tsum`: the
  countable triangle inequality for `Γ_σ`.
* `Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le`:
  the same estimate stated against an arbitrary majorant of `∑' k, a k`.

## References

* ABK26, Lemma `l.Gamma.sigma.triangle`.
* ABK26, Appendix.
-/

namespace Algsuperdiff.Section3.Provider.Orlicz

open MeasureTheory
open HCPolySupport.IndependentSums

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- For a pointwise nonnegative random variable the one-sided weak-Orlicz
relation `X ≤ O_Ψ(A)` and the symmetric relation `X = O_Ψ(A)` agree, because
`|X| = X`. -/
theorem isBigOWith_iff_isBigO_of_nonneg {Ψ : ℝ → ℝ} {Y : Ω → ℝ} {A : ℝ}
    (hY : ∀ ω, 0 ≤ Y ω) :
    IsBigOWith μ Ψ Y A ↔ IsBigO μ Ψ Y A := by
  have habs : (fun ω => |Y ω|) = Y := funext fun ω => abs_of_nonneg (hY ω)
  rw [IsBigO, habs]

/-- Continuity from below for weak-Orlicz upper tails of a nonnegative series.

If every partial sum `∑_{k < N+1} X k` obeys the same one-sided bound at scale
`A`, then so does the series `∑' k, X k`. Only the partial sums over the
nonempty ranges are required, which is what the finite triangle inequality
supplies. -/
theorem isBigOWith_tsum_of_isBigOWith_sum_range_succ [IsFiniteMeasure μ]
    {Ψ : ℝ → ℝ} {X : ℕ → Ω → ℝ} {A : ℝ}
    (hX_nonneg : ∀ k ω, 0 ≤ X k ω)
    (hsum : ∀ N : ℕ,
      IsBigOWith μ Ψ (fun ω => ∑ k ∈ Finset.range (N + 1), X k ω) A) :
    IsBigOWith μ Ψ (fun ω => ∑' k, X k ω) A := by
  intro t ht
  have hΨ_nonneg : (0 : ℝ) ≤ (Ψ t)⁻¹ := le_trans measureReal_nonneg (hsum 0 ht)
  have hmono : Monotone fun N : ℕ =>
      upperTailEvent (fun ω => ∑ k ∈ Finset.range (N + 1), X k ω) (A * t) := by
    intro M N hMN ω hω
    simp only [mem_upperTailEvent] at hω ⊢
    refine lt_of_lt_of_le hω ?_
    have hsub : Finset.range (M + 1) ⊆ Finset.range (N + 1) :=
      Finset.range_subset_range.2 (by omega)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hX_nonneg i ω
  have hsubset : upperTailEvent (fun ω => ∑' k, X k ω) (A * t) ⊆
      ⋃ N : ℕ, upperTailEvent
        (fun ω => ∑ k ∈ Finset.range (N + 1), X k ω) (A * t) := by
    intro ω hω
    simp only [mem_upperTailEvent] at hω
    obtain ⟨N, hN⟩ : ∃ N : ℕ, A * t < ∑ k ∈ Finset.range N, X k ω := by
      by_contra hcon
      push Not at hcon
      exact absurd hω
        (not_lt.2 (Real.tsum_le_of_sum_range_le (fun k => hX_nonneg k ω) hcon))
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    simp only [mem_upperTailEvent]
    refine lt_of_lt_of_le hN ?_
    rw [Finset.sum_range_succ]
    linarith [hX_nonneg N ω]
  have hbound : ∀ N : ℕ,
      μ (upperTailEvent (fun ω => ∑ k ∈ Finset.range (N + 1), X k ω) (A * t))
        ≤ ENNReal.ofReal ((Ψ t)⁻¹) :=
    fun N =>
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hΨ_nonneg).2 (hsum N ht)
  have hmeasure :
      μ (upperTailEvent (fun ω => ∑' k, X k ω) (A * t))
        ≤ ENNReal.ofReal ((Ψ t)⁻¹) := by
    refine (measure_mono hsubset).trans ?_
    rw [hmono.measure_iUnion]
    exact iSup_le hbound
  have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rwa [ENNReal.toReal_ofReal hΨ_nonneg] at htoReal

/-- Generalized triangle inequality for a countable family of nonnegative
random variables with stretched-exponential upper tails.

This is the ABK26 statement `l.Gamma.sigma.triangle` with CoarseGraining's
explicit constant `gammaTriangleConst σ` in place of the source's `1 + C
σ^{-1/σ} 1_{σ < 1}`. -/
theorem isBigOWith_gammaSigma_tsum [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {a : ℕ → ℝ} {σ : ℝ}
    (hσ : 0 < σ)
    (hX_nonneg : ∀ k ω, 0 ≤ X k ω)
    (hX_meas : ∀ k, Measurable (X k))
    (ha : ∀ k, 0 < a k)
    (ha_summable : Summable a)
    (hX : ∀ k, IsBigOWith μ (gammaSigma σ) (X k) (a k)) :
    IsBigOWith μ (gammaSigma σ) (fun ω => ∑' k, X k ω)
      (gammaTriangleConst σ * ∑' k, a k) := by
  have hC_pos : (0 : ℝ) < gammaTriangleConst σ := gammaTriangleConst_pos
  have hX_bigO : ∀ k, IsBigO μ (gammaSigma σ) (X k) (a k) := fun k =>
    (isBigOWith_iff_isBigO_of_nonneg fun ω => hX_nonneg k ω).1 (hX k)
  refine isBigOWith_tsum_of_isBigOWith_sum_range_succ hX_nonneg fun N => ?_
  have hs : (Finset.range (N + 1)).Nonempty :=
    Finset.nonempty_range_iff.2 (Nat.succ_ne_zero N)
  have hfinite :=
    isBigO_finset_sum_of_isBigO_gammaSigma (μ := μ) (Finset.range (N + 1))
      (X := X) (a := a) (σ := σ) hσ hs (fun i _ => ha i)
      (fun i _ => hX_bigO i) fun i _ => hX_meas i
  have hfinite' :
      IsBigOWith μ (gammaSigma σ)
        (fun ω => ∑ k ∈ Finset.range (N + 1), X k ω)
        (gammaTriangleConst σ * ∑ k ∈ Finset.range (N + 1), a k) :=
    (isBigOWith_iff_isBigO_of_nonneg
      fun ω => Finset.sum_nonneg fun k _ => hX_nonneg k ω).2 hfinite
  refine hfinite'.mono_scale ?_
  exact mul_le_mul_of_nonneg_left
    (ha_summable.sum_le_tsum _ fun i _ => (ha i).le) hC_pos.le

/-- The countable triangle inequality stated against an arbitrary majorant `B`
of the scale series, which is the form used at ABK26 call sites. -/
theorem isBigOWith_gammaSigma_tsum_of_tsum_le [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {a : ℕ → ℝ} {σ B : ℝ}
    (hσ : 0 < σ)
    (hX_nonneg : ∀ k ω, 0 ≤ X k ω)
    (hX_meas : ∀ k, Measurable (X k))
    (ha : ∀ k, 0 < a k)
    (ha_summable : Summable a)
    (hX : ∀ k, IsBigOWith μ (gammaSigma σ) (X k) (a k))
    (hB : ∑' k, a k ≤ B) :
    IsBigOWith μ (gammaSigma σ) (fun ω => ∑' k, X k ω)
      (gammaTriangleConst σ * B) :=
  (isBigOWith_gammaSigma_tsum hσ hX_nonneg hX_meas ha ha_summable hX).mono_scale
    (mul_le_mul_of_nonneg_left hB gammaTriangleConst_pos.le)

/-! ## A.e.-measurable summands -/

/-- Countable `Gamma_sigma` triangle inequality for nonnegative summands that are
only a.e.-measurable.  This is the countable extension of CoarseGraining's
finite `isBigO_finset_sum_of_isBigO_gammaSigma_aemeasurable`; it introduces no
measurable-representative premise at the call site. -/
theorem isBigOWith_gammaSigma_tsum_aemeasurable [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {a : ℕ → ℝ} {σ : ℝ}
    (hσ : 0 < σ)
    (hX_nonneg : ∀ k ω, 0 ≤ X k ω)
    (hX_meas : ∀ k, AEMeasurable (X k) μ)
    (ha : ∀ k, 0 < a k)
    (ha_summable : Summable a)
    (hX : ∀ k, IsBigOWith μ (gammaSigma σ) (X k) (a k)) :
    IsBigOWith μ (gammaSigma σ) (fun ω => ∑' k, X k ω)
      (gammaTriangleConst σ * ∑' k, a k) := by
  have hC_pos : (0 : ℝ) < gammaTriangleConst σ := gammaTriangleConst_pos
  have hX_bigO : ∀ k, IsBigO μ (gammaSigma σ) (X k) (a k) := fun k =>
    (isBigOWith_iff_isBigO_of_nonneg fun ω => hX_nonneg k ω).1 (hX k)
  refine isBigOWith_tsum_of_isBigOWith_sum_range_succ hX_nonneg fun N => ?_
  have hs : (Finset.range (N + 1)).Nonempty :=
    Finset.nonempty_range_iff.2 (Nat.succ_ne_zero N)
  have hfinite :=
    HCPolySupport.Book.Ch04.isBigO_finset_sum_of_isBigO_gammaSigma_aemeasurable
      (μ := μ) (Finset.range (N + 1))
      (X := X) (a := a) (σ := σ) hσ hs (fun i _ => ha i)
      (fun i _ => hX_bigO i) hX_meas
  have hfinite' :
      IsBigOWith μ (gammaSigma σ)
        (fun ω => ∑ k ∈ Finset.range (N + 1), X k ω)
        (gammaTriangleConst σ * ∑ k ∈ Finset.range (N + 1), a k) :=
    (isBigOWith_iff_isBigO_of_nonneg
      fun ω => Finset.sum_nonneg fun k _ => hX_nonneg k ω).2 hfinite
  refine hfinite'.mono_scale ?_
  exact mul_le_mul_of_nonneg_left
    (ha_summable.sum_le_tsum _ fun i _ => (ha i).le) hC_pos.le

end

end Algsuperdiff.Section3.Provider.Orlicz
