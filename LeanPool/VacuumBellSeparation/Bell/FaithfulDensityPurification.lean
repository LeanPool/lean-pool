/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.DensityPurification
public import LeanPool.VacuumBellSeparation.Gaussian.HilbertEigenTrace

/-!
# Coordinate recovery from a faithful density purification

Faithfulness makes every eigenvalue of the actual compact positive density
strictly positive. Rank-one operators then recover all single-coordinate
vectors from its literal square-root purification. No bounded inverse of
the density or uniform positive lower spectral bound is used.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ρ : H →L[ℂ] H} (hρ : IsFaithfulDensity ρ)

include hρ in
theorem faithfulDensity_eigenvalue_pos (i : operatorEigenIndex ρ) : 0 < i.1.re := by
  refine lt_of_le_of_ne (operatorEigenFamily_eigenvalue_nonneg hρ.1 i) ?_
  intro hz
  have he := compactSelfAdjointBasis_apply_operator
    (positiveTraceClass_isCompactOperator hρ.isPositiveTraceClass) hρ.1.isSelfAdjoint i
  have hn := (positiveTraceClassEigenbasis hρ.isPositiveTraceClass).orthonormal.norm_eq_one i
  have hb : positiveTraceClassEigenbasis hρ.isPositiveTraceClass i = 0 := by
    apply hρ.2.2
    simpa only [positiveTraceClassEigenbasis, hz.symm, Complex.ofReal_zero,
      zero_smul, map_zero] using he
  exact zero_ne_one (by simpa only [hb, norm_zero] using hn)

/-- The spectral basis is constructed from the actual compact operator. -/
noncomputable def faithfulDensityPurification : lp (fun _ : operatorEigenIndex ρ => H) 2 :=
  densityPurification (positiveTraceClassEigenbasis hρ.isPositiveTraceClass)
    hρ.isPositiveTraceClass

theorem faithfulDensityPurification_apply (i : operatorEigenIndex ρ) :
    faithfulDensityPurification hρ i =
      Real.sqrt i.1.re • positiveTraceClassEigenbasis hρ.isPositiveTraceClass i := by
  apply hilbertEigenbasis_sqrt_apply _ hρ.1
  intro j
  exact compactSelfAdjointBasis_apply_operator
    (positiveTraceClass_isCompactOperator hρ.isPositiveTraceClass) hρ.1.isSelfAdjoint j

theorem faithfulDensityPurification_norm : ‖faithfulDensityPurification hρ‖ = 1 :=
  densityPurification_norm _ _ hρ.2.1

/-- Actual amplified rank-one action recovers a single coordinate. -/
theorem amplification_rankOne_faithfulDensityPurification
    [DecidableEq (operatorEigenIndex ρ)] (i : operatorEigenIndex ρ) (x : H) :
    hilbertAmplification (operatorEigenIndex ρ)
      (rankOne ℂ x (positiveTraceClassEigenbasis hρ.isPositiveTraceClass i))
      (faithfulDensityPurification hρ) =
        (Real.sqrt i.1.re : ℂ) • lp.single 2 i x := by
  ext j
  simp only [hilbertAmplification_apply, faithfulDensityPurification_apply, rankOne_apply,
    inner_smul_right_eq_smul, lp.coeFn_smul, Pi.smul_apply]
  by_cases h : j = i
  · subst j
    simp [inner_self_eq_norm_sq_to_K,
      (positiveTraceClassEigenbasis hρ.isPositiveTraceClass).orthonormal.norm_eq_one]
  · rw [(positiveTraceClassEigenbasis hρ.isPositiveTraceClass).orthonormal.inner_eq_zero
      (Ne.symm h)]
    simp only [smul_zero, zero_smul, lp.single_apply_ne _ _ _ h]

end VacuumBellSeparation
