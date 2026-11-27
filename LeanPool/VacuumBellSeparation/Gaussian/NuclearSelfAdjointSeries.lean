/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CompactTraceNorm
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceSeries

/-!
# Nuclear bounds for actual self-adjoint operator series

Absolute summability is in the operator norm. It produces a genuine
compact self-adjoint sum; the trace of its absolute value is bounded by
the sum of the individual nuclear traces, even when that bound is infinite.
The argument compares the sum with the positive sum of absolute values,
using quadratic-form order rather than an operator absolute-value triangle
inequality.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Filter
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

theorem isCompactOperator_tsum_of_summable {A : ι → E →L[ℂ] E}
    (hA : ∀ i, IsCompactOperator (A i)) (hs : Summable A) :
    IsCompactOperator ((∑' i, A i) : E →L[ℂ] E) := by
  classical
  apply isCompactOperator_of_tendsto hs.hasSum
  exact Eventually.of_forall fun s =>
    (compactOperator (RingHom.id ℂ) E E).sum_mem fun i _ => hA i

theorem isSelfAdjoint_tsum {A : ι → E →L[ℂ] E}
    (hA : ∀ i, IsSelfAdjoint (A i)) : IsSelfAdjoint (∑' i, A i) := by
  change star (∑' i, A i) = ∑' i, A i
  rw [tsum_star]
  exact tsum_congr fun i => hA i

theorem summable_operator_abs_of_summable_norm {A : ι → E →L[ℂ] E}
    (hs : Summable fun i => ‖A i‖) : Summable fun i => CFC.abs (A i) := by
  apply Summable.of_norm
  simpa only [CFC.norm_abs] using hs

theorem operatorTraceNorm_tsum_le {A : ι → E →L[ℂ] E}
    (hc : ∀ i, IsCompactOperator (A i)) (hA : ∀ i, IsSelfAdjoint (A i))
    (hs : Summable fun i => ‖A i‖) :
    operatorTraceNorm (∑' i, A i) ≤ ∑' i, operatorTraceNorm (A i) := by
  have hsA : Summable A := hs.of_norm
  have hsabs := summable_operator_abs_of_summable_norm hs
  have hupper : (∑' i, A i) ≤ ∑' i, CFC.abs (A i) :=
    Summable.tsum_le_tsum (fun i => sub_nonneg.mp (operator_abs_sub_nonneg (hA i))) hsA hsabs
  have hlower : -(∑' i, CFC.abs (A i)) ≤ ∑' i, A i := by
    simpa only [tsum_neg] using
      Summable.tsum_le_tsum (fun i => neg_le_iff_add_nonneg'.mpr (operator_abs_add_nonneg (hA i)))
        hsabs.neg hsA
  have hb : 0 ≤ ∑' i, CFC.abs (A i) := tsum_nonneg fun i => CFC.abs_nonneg (A i)
  calc
    operatorTraceNorm (∑' i, A i) ≤ positiveTrace (∑' i, CFC.abs (A i)) :=
      operatorTraceNorm_le_positiveTrace_of_order_bounds
        (isCompactOperator_tsum_of_summable hc hsA) (isSelfAdjoint_tsum hA) hb hlower hupper
    _ = ∑' i, operatorTraceNorm (A i) := by
      simpa only [operatorTraceNorm] using positiveTrace_tsum (fun i => CFC.abs_nonneg (A i)) hsabs

theorem operatorTraceNorm_tsum_lt_top {A : ι → E →L[ℂ] E}
    (hc : ∀ i, IsCompactOperator (A i)) (hA : ∀ i, IsSelfAdjoint (A i))
    (hs : Summable fun i => ‖A i‖)
    (htrace : (∑' i, operatorTraceNorm (A i)) < ∞) :
    operatorTraceNorm (∑' i, A i) < ∞ :=
  (operatorTraceNorm_tsum_le hc hA hs).trans_lt htrace

end VacuumBellSeparation.Gaussian
