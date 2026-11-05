/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Operations

/-!
# Maximum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Maxima of stretched-exponential random variables over any nonempty family

CoarseGraining's finite-maximum estimate
`Homogenization.IndependentSums.isBigOWith_gammaSigma_finset_sup'` carries the
hypothesis `2 ≤ s.card`, matching the source proof, which uses `2 log N ≥ 1`.
The ABK26 call sites also instantiate the estimate at singletons, where `log 1
= 0` degenerates the amplitude.

This module removes the cardinality restriction by replacing `log N` with
`max 1 (log N)`. For `2 ≤ N` this only enlarges the amplitude, and for `N = 1`
the supremum is a single member of the family and the amplitude factor is
`3^{1/σ} ≥ 1`. Both cases then follow by amplitude monotonicity,
`Homogenization.IndependentSums.IsBigOWith.mono_scale`.

## Main results

* `Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty`
* `Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_finset_sup'_of_scales_of_nonempty`

## References

* ABK26, Lemma `l.maximums.Gamma.s`.
* ABK26, Appendix.
-/

namespace Algsuperdiff.Section3.Provider.Orlicz

open MeasureTheory
open HCPolySupport.IndependentSums

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Maximum of a nonempty finite family of `Γ_σ` random variables at a common
scale `A`, with no restriction on the cardinality.

The amplitude uses `max 1 (log card)` rather than the source's `log card`;
the two agree up to an enlargement for `2 ≤ card`, and the `max` is what makes
the singleton case nondegenerate. -/
theorem isBigOWith_gammaSigma_finset_sup'_of_nonempty [IsFiniteMeasure μ]
    (s : Finset ι) (hs : s.Nonempty) {X : ι → Ω → ℝ} {A σ : ℝ}
    (hσ : 0 < σ) (hA : 0 ≤ A)
    (hX : ∀ i ∈ s, IsBigOWith μ (gammaSigma σ) (X i) A) :
    IsBigOWith μ (gammaSigma σ) (fun ω => s.sup' hs fun i => X i ω)
      ((3 * max 1 (Real.log (s.card : ℝ))) ^ σ⁻¹ * A) := by
  have hinv : (0 : ℝ) ≤ σ⁻¹ := inv_nonneg.2 hσ.le
  by_cases hcard : 2 ≤ s.card
  · have hcard_real : (2 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hcard
    have hlog_pos : 0 < Real.log (s.card : ℝ) := Real.log_pos (by linarith)
    have hbase_nonneg : (0 : ℝ) ≤ 3 * Real.log (s.card : ℝ) := by linarith
    have hbase_le : 3 * Real.log (s.card : ℝ)
        ≤ 3 * max 1 (Real.log (s.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
    refine (isBigOWith_gammaSigma_finset_sup' (μ := μ) s hs (X := X) (A := A)
      (σ := σ) hσ hcard hX).mono_scale ?_
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hbase_nonneg hbase_le hinv) hA
  · have hcard_eq : s.card = 1 := by
      have hpos := hs.card_pos
      omega
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard_eq
    have hfun : (fun ω => ({i} : Finset ι).sup' hs fun j => X j ω) = X i := by
      funext ω
      simp
    have hcard_one : ((({i} : Finset ι).card : ℝ)) = 1 := by simp
    have hmax : max (1 : ℝ) 0 = 1 := max_eq_left (by norm_num)
    rw [hfun, hcard_one, Real.log_one, hmax, mul_one]
    refine (hX i (Finset.mem_singleton_self i)).mono_scale ?_
    exact le_mul_of_one_le_left hA (Real.one_le_rpow (by norm_num) hinv)

/-- Maximum of a nonempty finite family of `Γ_σ` random variables with
individual scales, controlled by the largest scale. -/
theorem isBigOWith_gammaSigma_finset_sup'_of_scales_of_nonempty [IsFiniteMeasure μ]
    (s : Finset ι) (hs : s.Nonempty) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    (hσ : 0 < σ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hX : ∀ i ∈ s, IsBigOWith μ (gammaSigma σ) (X i) (a i)) :
    IsBigOWith μ (gammaSigma σ) (fun ω => s.sup' hs fun i => X i ω)
      ((3 * max 1 (Real.log (s.card : ℝ))) ^ σ⁻¹ * s.sup' hs a) := by
  have hmem : ∃ j, j ∈ s := hs
  obtain ⟨j, hj⟩ := hmem
  refine isBigOWith_gammaSigma_finset_sup'_of_nonempty (μ := μ) s hs
    (X := X) (A := s.sup' hs a) (σ := σ) hσ
    (le_trans (ha j hj) (Finset.le_sup' a hj)) ?_
  exact fun i hi => (hX i hi).mono_scale (Finset.le_sup' a hi)

end

end Algsuperdiff.Section3.Provider.Orlicz
