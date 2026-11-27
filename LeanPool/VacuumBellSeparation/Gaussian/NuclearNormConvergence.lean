/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.NuclearSelfAdjointSeries

/-!
# A finite nuclear sum constructs the actual operator-norm sum

The genuine extended trace dominates operator norm. Consequently a family
whose nuclear traces have finite sum is norm summable, and a compact
self-adjoint family has an actual compact self-adjoint sum with the
claimed nuclear bound. No abstract Schatten-space completeness is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

theorem norm_le_positiveTrace_toReal {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) :
    ‖A‖ ≤ (positiveTrace A).toReal := by
  obtain ⟨κ, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  have ht : (∑' i, ENNReal.ofReal (‖CFC.sqrt A (b i)‖ ^ 2)) < ∞ := by
    simpa only [positiveTrace_eq_basisSquareTrace b, basisSquareTrace] using hA.2
  have hs : Summable fun i => ‖CFC.sqrt A (b i)‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal ht.ne
  have heq : (positiveTrace A).toReal = ∑' i, ‖CFC.sqrt A (b i)‖ ^ 2 := by
    rw [positiveTrace_eq_basisSquareTrace b, basisSquareTrace,
      ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (sq_nonneg _)]
  have hn := norm_le_sqrt_basis_image_sum b (CFC.sqrt A) hs
  have hsq : ‖CFC.sqrt A‖ ^ 2 ≤ ∑' i, ‖CFC.sqrt A (b i)‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hn 2
    rwa [Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)] at h
  calc
    ‖A‖ = ‖CFC.sqrt A * CFC.sqrt A‖ := congrArg norm (CFC.sqrt_mul_sqrt_self A hA.1).symm
    _ = ‖CFC.sqrt A‖ ^ 2 := by rw [(CFC.sqrt_nonneg A).isSelfAdjoint.norm_mul_self, pow_two]
    _ ≤ ∑' i, ‖CFC.sqrt A (b i)‖ ^ 2 := hsq
    _ = (positiveTrace A).toReal := heq.symm

theorem ofReal_norm_le_positiveTrace {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    ENNReal.ofReal ‖A‖ ≤ positiveTrace A := by
  by_cases ht : positiveTrace A = ∞
  · rw [ht]
    exact le_top
  · have hn := ENNReal.ofReal_le_ofReal (norm_le_positiveTrace_toReal ⟨hA,
      lt_top_iff_ne_top.mpr ht⟩)
    simpa only [ENNReal.ofReal_toReal ht] using hn

theorem ofReal_norm_le_operatorTraceNorm (A : E →L[ℂ] E) :
    ENNReal.ofReal ‖A‖ ≤ operatorTraceNorm A := by
  simpa only [CFC.norm_abs, operatorTraceNorm] using ofReal_norm_le_positiveTrace (CFC.abs_nonneg A)

theorem summable_norm_of_nuclear_sum_lt_top {A : ι → E →L[ℂ] E}
    (ht : (∑' i, operatorTraceNorm (A i)) < ∞) : Summable fun i => ‖A i‖ := by
  have hn : (∑' i, ENNReal.ofReal ‖A i‖) < ∞ :=
    (tsum_le_tsum fun i => ofReal_norm_le_operatorTraceNorm (A i)).trans_lt ht
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using ENNReal.summable_toReal hn.ne

theorem nuclear_sum_constructs_compact_selfAdjoint {A : ι → E →L[ℂ] E}
    (hc : ∀ i, IsCompactOperator (A i)) (hA : ∀ i, IsSelfAdjoint (A i))
    (ht : (∑' i, operatorTraceNorm (A i)) < ∞) :
    Summable A ∧ IsCompactOperator (∑' i, A i) ∧ IsSelfAdjoint (∑' i, A i) ∧
      operatorTraceNorm (∑' i, A i) ≤ ∑' i, operatorTraceNorm (A i) := by
  have hs := summable_norm_of_nuclear_sum_lt_top ht
  have hfun : HasSum (fun i => (A i : E → E))
      (fun x => ((∑' i, A i) : E →L[ℂ] E) x) := by
    apply Pi.hasSum.mpr
    intro x
    exact (ContinuousLinearMap.apply ℂ E x).hasSum hs.of_norm.hasSum
  have hcompact : IsCompactOperator (∑' i, (A i : E → E)) := by
    rw [hfun.tsum_eq]
    exact isCompactOperator_tsum_of_summable hc hs.of_norm
  exact ⟨hs.of_norm, hcompact, isSelfAdjoint_tsum hA,
    operatorTraceNorm_tsum_le hc hA hs⟩

end VacuumBellSeparation.Gaussian
