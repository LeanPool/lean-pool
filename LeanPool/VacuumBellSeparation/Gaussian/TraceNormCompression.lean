/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CompactTraceNorm
public import LeanPool.VacuumBellSeparation.Gaussian.HilbertSchmidtIdeal
public import LeanPool.VacuumBellSeparation.Gaussian.Compression

/-!
# Actual trace-norm bounds for rectangular compressions

The proof sandwiches the two genuine order bounds -|Y| <= Y <= |Y|
and uses the actual positive trace ideal estimate. It never asserts the
generally false operator inequality |A†YA| <= A†|Y|A.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem operatorTraceNorm_adjoint_sandwich_le
    {Y : F →L[ℂ] F} (hcY : IsCompactOperator Y) (hY : IsSelfAdjoint Y)
    (A : E →L[ℂ] F) :
    operatorTraceNorm (A.adjoint.comp (Y.comp A)) ≤
      ENNReal.ofReal (‖A‖ ^ 2) * operatorTraceNorm Y := by
  have hpos {B : F →L[ℂ] F} (hB : 0 ≤ B) :
      0 ≤ A.adjoint.comp (B.comp A) := by
    exact nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp hB).adjoint_conj A)
  have hlo : -(A.adjoint.comp ((CFC.abs Y).comp A)) ≤ A.adjoint.comp (Y.comp A) := by
    have h := hpos (operator_abs_add_nonneg hY)
    simp only [add_comp, comp_add] at h
    exact neg_le_iff_add_nonneg'.mpr h
  have hhi : A.adjoint.comp (Y.comp A) ≤ A.adjoint.comp ((CFC.abs Y).comp A) := by
    have h := hpos (operator_abs_sub_nonneg hY)
    simp only [sub_comp, comp_sub] at h
    exact sub_nonneg.mp h
  have hc : IsCompactOperator (A.adjoint.comp (Y.comp A)) :=
    (hcY.comp_clm A).clm_comp A.adjoint
  have hs : IsSelfAdjoint (A.adjoint.comp (Y.comp A)) := hY.adjoint_conj A
  exact (operatorTraceNorm_le_positiveTrace_of_order_bounds hc hs
    (hpos (CFC.abs_nonneg Y)) hlo hhi).trans
      (positiveTrace_adjoint_sandwich_le (CFC.abs_nonneg Y) A)

theorem operatorTraceNorm_adjoint_contraction_le
    {Y : F →L[ℂ] F} (hcY : IsCompactOperator Y) (hY : IsSelfAdjoint Y)
    (A : E →L[ℂ] F) (hA : ‖A‖ ≤ 1) :
    operatorTraceNorm (A.adjoint.comp (Y.comp A)) ≤ operatorTraceNorm Y := by
  have hs : ‖A‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg A]
  calc
    _ ≤ ENNReal.ofReal (‖A‖ ^ 2) * operatorTraceNorm Y :=
      operatorTraceNorm_adjoint_sandwich_le hcY hY A
    _ ≤ 1 * operatorTraceNorm Y := _root_.mul_le_mul_left (by
      simpa using ENNReal.ofReal_le_ofReal hs) _
    _ = _ := one_mul _

theorem operatorTraceNorm_compression_le
    (ι : E →ₗᵢ[ℂ] F) {Y : F →L[ℂ] F}
    (hcY : IsCompactOperator Y) (hY : IsSelfAdjoint Y) :
    operatorTraceNorm (compression ι Y) ≤ operatorTraceNorm Y := by
  exact operatorTraceNorm_adjoint_contraction_le hcY hY ι.toContinuousLinearMap
    (LinearIsometry.norm_toContinuousLinearMap_le ι)

end VacuumBellSeparation.Gaussian
