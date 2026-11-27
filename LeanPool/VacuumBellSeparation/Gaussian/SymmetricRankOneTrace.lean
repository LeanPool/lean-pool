/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.NuclearSelfAdjointSeries
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceScaling

/-!
# Genuine nuclear estimates for symmetric rank-one kernels

These operators act on the full Hilbert space. Their trace estimate gives
the factor two for a cross term and its adjoint; it uses actual positive
rank-one traces and order bounds. The final series theorem constructs the
bounded compact self-adjoint operator from the norm-summable coefficients.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap InnerProductSpace
open scoped ENNReal ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

omit [CompleteSpace E] in
theorem rankOne_self_nonneg (x : E) : 0 ≤ rankOne ℂ x x :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_rankOne_self x)

theorem positiveTrace_rankOne_self (x : E) :
    positiveTrace (rankOne ℂ x x) = ENNReal.ofReal (‖x‖ ^ 2) := by
  obtain ⟨κ, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  rw [positiveTrace_eq_tsum_diagonal b (rankOne_self_nonneg x)]
  have hterm (i : κ) : (inner ℂ (b i) (rankOne ℂ x x (b i))).re =
      ‖inner ℂ (b i) x‖ ^ 2 := by
    rw [inner_right_rankOne_apply, ← inner_conj_symm (b i) x, Complex.conj_mul']
    simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.norm_conj]
  simp_rw [hterm]
  exact tsum_basis_inner_norm_sq b x

theorem operatorTraceNorm_real_smul (c : ℝ) (A : E →L[ℂ] E) :
    operatorTraceNorm (c • A) = ENNReal.ofReal |c| * operatorTraceNorm A := by
  obtain ⟨κ, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  rw [operatorTraceNorm, CFC.abs_smul, positiveTrace_real_smul b
    (CFC.abs_nonneg A) (norm_nonneg c), Real.norm_eq_abs, operatorTraceNorm]

/-- Symmetric rank one given by `rankOne ℂ u v + rankOne ℂ v u`. -/
def symmetricRankOne (u v : E) : E →L[ℂ] E := rankOne ℂ u v + rankOne ℂ v u

theorem symmetricRankOne_isSelfAdjoint (u v : E) : IsSelfAdjoint (symmetricRankOne u v) := by
  change (symmetricRankOne u v).adjoint = symmetricRankOne u v
  simp only [symmetricRankOne, map_add, adjoint_rankOne, add_comm]

omit [CompleteSpace E] in
theorem symmetricRankOne_isCompactOperator (u v : E) :
    IsCompactOperator (symmetricRankOne u v) :=
  (isCompactOperator_rankOne u v).add (isCompactOperator_rankOne v u)

omit [CompleteSpace E] in
theorem norm_symmetricRankOne_le (u v : E) :
    ‖symmetricRankOne u v‖ ≤ 2 * (‖u‖ * ‖v‖) := by
  calc
    ‖symmetricRankOne u v‖ ≤ ‖rankOne ℂ u v‖ + ‖rankOne ℂ v u‖ := norm_add_le _ _
    _ = 2 * (‖u‖ * ‖v‖) := by rw [norm_rankOne, norm_rankOne]; ring

omit [CompleteSpace E] in
theorem symmetricRankOne_real_smul (a b : ℝ) (u v : E) :
    symmetricRankOne (a • u) (b • v) = (a * b) • symmetricRankOne u v := by
  have hterm (a b : ℝ) (u v x : E) :
      (inner ℂ (b • v) x) • (a • u) = (a * b) • ((inner ℂ v x) • u) := by
    rw [inner_smul_left_eq_smul, smul_assoc,
      smul_comm (inner ℂ v x) a, smul_smul, mul_comm b a]
  ext x
  change (inner ℂ (b • v) x) • (a • u) + (inner ℂ (a • u) x) • (b • v) =
    (a * b) • ((inner ℂ v x) • u + (inner ℂ u x) • v)
  rw [hterm a b u v x, hterm b a v u x, mul_comm b a, smul_add]

theorem operatorTraceNorm_symmetricRankOne_le_sq (u v : E) :
    operatorTraceNorm (symmetricRankOne u v) ≤ ENNReal.ofReal (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  let B := rankOne ℂ u u + rankOne ℂ v v
  have hB : 0 ≤ B := add_nonneg (rankOne_self_nonneg u) (rankOne_self_nonneg v)
  have hminus : B - symmetricRankOne u v = rankOne ℂ (u - v) (u - v) := by
    ext x
    simp only [B, symmetricRankOne, add_apply, sub_apply, rankOne_apply,
      inner_sub_left, sub_smul, smul_sub]
    abel
  have hplus : B + symmetricRankOne u v = rankOne ℂ (u + v) (u + v) := by
    ext x
    simp only [B, symmetricRankOne, add_apply, rankOne_apply,
      inner_add_left, add_smul, smul_add]
    abel
  have hupper : symmetricRankOne u v ≤ B := by
    apply sub_nonneg.mp
    rw [hminus]
    exact rankOne_self_nonneg _
  have hlower : -B ≤ symmetricRankOne u v := by
    apply neg_le_iff_add_nonneg'.mpr
    rw [hplus]
    exact rankOne_self_nonneg _
  calc
    operatorTraceNorm (symmetricRankOne u v) ≤ positiveTrace B :=
      operatorTraceNorm_le_positiveTrace_of_order_bounds (symmetricRankOne_isCompactOperator u v)
        (symmetricRankOne_isSelfAdjoint u v) hB hlower hupper
    _ = ENNReal.ofReal (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      dsimp only [B]
      rw [positiveTrace_add (rankOne_self_nonneg u) (rankOne_self_nonneg v),
        positiveTrace_rankOne_self, positiveTrace_rankOne_self,
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]

theorem operatorTraceNorm_symmetricRankOne_le (u v : E) :
    operatorTraceNorm (symmetricRankOne u v) ≤ ENNReal.ofReal (2 * (‖u‖ * ‖v‖)) := by
  by_cases hu : u = 0
  · subst u
    simp [symmetricRankOne, operatorTraceNorm, positiveTrace_zero]
  by_cases hv : v = 0
  · subst v
    simp [symmetricRankOne, operatorTraceNorm, positiveTrace_zero]
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u' := ‖u‖⁻¹ • u
  let v' := ‖v‖⁻¹ • v
  have hu' : ‖u'‖ = 1 := by simp [u', norm_smul, hnu.ne']
  have hv' : ‖v'‖ = 1 := by simp [v', norm_smul, hnv.ne']
  have heq : symmetricRankOne u v = (‖u‖ * ‖v‖) • symmetricRankOne u' v' := by
    dsimp only [u', v']
    rw [symmetricRankOne_real_smul, smul_smul]
    have hs : (‖u‖ * ‖v‖) * (‖u‖⁻¹ * ‖v‖⁻¹) = 1 := by
      field_simp [hnu.ne', hnv.ne']
    rw [hs, one_smul]
  rw [heq, operatorTraceNorm_real_smul, abs_of_nonneg (mul_nonneg hnu.le hnv.le)]
  calc
    ENNReal.ofReal (‖u‖ * ‖v‖) * operatorTraceNorm (symmetricRankOne u' v') ≤
        ENNReal.ofReal (‖u‖ * ‖v‖) * ENNReal.ofReal (‖u'‖ ^ 2 + ‖v'‖ ^ 2) :=
      _root_.mul_le_mul_right (operatorTraceNorm_symmetricRankOne_le_sq u' v') _
    _ = ENNReal.ofReal (2 * (‖u‖ * ‖v‖)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hnu.le hnv.le), hu', hv']
      congr 1
      ring

theorem summable_symmetricRankOne {u v : ι → E}
    (hs : Summable fun i => ‖u i‖ * ‖v i‖) :
    Summable fun i => symmetricRankOne (u i) (v i) :=
  (hs.mul_left 2).of_norm_bounded fun _i => norm_symmetricRankOne_le _ _

theorem operatorTraceNorm_symmetricRankOne_tsum_le {u v : ι → E}
    (hs : Summable fun i => ‖u i‖ * ‖v i‖) :
    operatorTraceNorm (∑' i, symmetricRankOne (u i) (v i)) ≤
      ENNReal.ofReal (2 * ∑' i, ‖u i‖ * ‖v i‖) := by
  have hsn : Summable fun i => ‖symmetricRankOne (u i) (v i)‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => norm_symmetricRankOne_le _ _)
      (hs.mul_left 2)
  calc
    operatorTraceNorm (∑' i, symmetricRankOne (u i) (v i)) ≤
        ∑' i, operatorTraceNorm (symmetricRankOne (u i) (v i)) :=
      operatorTraceNorm_tsum_le (fun i => symmetricRankOne_isCompactOperator _ _)
        (fun i => symmetricRankOne_isSelfAdjoint _ _) hsn
    _ ≤ ∑' i, ENNReal.ofReal (2 * (‖u i‖ * ‖v i‖)) :=
      tsum_le_tsum fun i => operatorTraceNorm_symmetricRankOne_le _ _
    _ = ENNReal.ofReal (2 * ∑' i, ‖u i‖ * ‖v i‖) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (hs.mul_left 2),
        tsum_mul_left]

end VacuumBellSeparation.Gaussian
