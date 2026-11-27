/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CompactTraceNorm
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The genuine nuclear norm is bounded by rank times operator norm

Only nonzero eigenvectors occur in the range. Their actual linear
independence bounds each finite spectral sum by the dimension of the
given finite-dimensional range space, including a possibly infinite
kernel and a nonseparable ambient Hilbert space.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem isCompactOperator_of_range_le_finiteDimensional
    (A : E →L[ℂ] E) (K : Submodule ℂ E) [FiniteDimensional ℂ K]
    (hK : A.toLinearMap.range ≤ K) : IsCompactOperator A := by
  let T := A.codRestrict K (fun x => hK ⟨x, rfl⟩)
  have hc : IsCompactOperator T := isCompactOperator_of_locallyCompactSpace_dom T
  convert hc.clm_comp K.subtypeL using 1
  funext x
  rfl

theorem compactSelfAdjoint_eigenvalue_abs_le_norm {A : E →L[ℂ] E}
    (hc : IsCompactOperator A) (hA : IsSelfAdjoint A) (i : operatorEigenIndex A) :
    |i.1.re| ≤ ‖A‖ := by
  have h := A.le_opNorm (compactSelfAdjointBasis hc hA i)
  rw [compactSelfAdjointBasis_apply_operator, norm_smul,
    (compactSelfAdjointBasis hc hA).orthonormal.norm_eq_one,
    Complex.norm_real, Real.norm_eq_abs, mul_one, mul_one] at h
  exact h

theorem compactSelfAdjoint_nonzero_eigenvector_mem_range {A : E →L[ℂ] E}
    (hc : IsCompactOperator A) (hA : IsSelfAdjoint A)
    (i : operatorEigenIndex A) (hi : i.1.re ≠ 0) :
    compactSelfAdjointBasis hc hA i ∈ A.toLinearMap.range := by
  refine ⟨(i.1.re : ℂ)⁻¹ • compactSelfAdjointBasis hc hA i, ?_⟩
  change A ((i.1.re : ℂ)⁻¹ • compactSelfAdjointBasis hc hA i) =
    compactSelfAdjointBasis hc hA i
  rw [A.map_smul, compactSelfAdjointBasis_apply_operator hc hA i, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hi), one_smul]

theorem operatorTraceNorm_le_finrank_mul_norm_of_range_le
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    (K : Submodule ℂ E) [FiniteDimensional ℂ K]
    (hK : A.toLinearMap.range ≤ K) :
    operatorTraceNorm A ≤ ENNReal.ofReal ((Module.finrank ℂ K : ℝ) * ‖A‖) := by
  classical
  have hc := isCompactOperator_of_range_le_finiteDimensional A K hK
  let b := compactSelfAdjointBasis hc hA
  rw [operatorTraceNorm_eq_eigenvalue_sum hc hA, tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  let t := s.filter (fun i : operatorEigenIndex A => i.1.re ≠ 0)
  have hm (i : t) : b i ∈ K :=
    hK (compactSelfAdjoint_nonzero_eigenvector_mem_range hc hA i
      (Finset.mem_filter.mp i.property).2)
  have hl : LinearIndependent ℂ (fun i : t => b i) :=
    b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  have hlK : LinearIndependent ℂ (fun i : t => (⟨b i, hm i⟩ : K)) :=
    hl.codRestrict K hm
  have hcard : t.card ≤ Module.finrank ℂ K := by
    simpa only [Fintype.card_coe] using hlK.fintype_card_le_finrank
  have he : (∑ i ∈ s, |i.1.re|) = ∑ i ∈ t, |i.1.re| := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i his hit
    have hz : i.1.re = 0 := by
      by_contra hn
      exact hit (Finset.mem_filter.mpr ⟨his, hn⟩)
    rw [hz, abs_zero]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg i.1.re), he]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ _ ∈ t, ‖A‖ := Finset.sum_le_sum
      (fun i _ => compactSelfAdjoint_eigenvalue_abs_le_norm hc hA i)
    _ = (t.card : ℝ) * ‖A‖ := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Module.finrank ℂ K : ℝ) * ‖A‖ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (norm_nonneg A)

theorem operatorTraceNorm_le_rank_mul_norm {A : E →L[ℂ] E}
    (hA : IsSelfAdjoint A) [FiniteDimensional ℂ A.toLinearMap.range] :
    operatorTraceNorm A ≤ ENNReal.ofReal
      ((Module.finrank ℂ A.toLinearMap.range : ℝ) * ‖A‖) :=
  operatorTraceNorm_le_finrank_mul_norm_of_range_le hA A.toLinearMap.range le_rfl

theorem finiteRank_selfAdjoint_traceNorm_lt_top {A : E →L[ℂ] E}
    (hA : IsSelfAdjoint A) [FiniteDimensional ℂ A.toLinearMap.range] :
    operatorTraceNorm A < ∞ :=
  (operatorTraceNorm_le_rank_mul_norm hA).trans_lt ENNReal.ofReal_lt_top

end VacuumBellSeparation.Gaussian
