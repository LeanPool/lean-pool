/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialIncrementRankDefs
public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialIncrementNorm
public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialCombinedRange

/-!
# The genuine unweighted nuclear estimate for the polynomial increments

The complex operator is the isometric complexification of the actual real
kernel operator. One cubic moment range contains both successive orders.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian Gaussian.HilbertComplexification

theorem complexify_sub_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B : E →L[ℝ] E) : complexify (A - B) = complexify A - complexify B := by
  simp only [sub_eq_add_neg, complexify_add, complexify_neg]

theorem nuclear_jointPolynomialIncrement_le_rank {μ s : ℝ}
    (hμ : 0 < μ) (hs : 600 ≤ s) (n : ℕ) :
    operatorTraceNorm (complexify (jointPolynomialIncrement hμ hs n)) ≤
      ENNReal.ofReal (jointPolynomialIncrementRank n * ‖jointPolynomialIncrement hμ hs n‖) := by
  let v := jointRegionMomentFamily hμ s
  let P := fun k => jointPhysicalPolynomial s (jointMidpointPolynomial
    (jointNormalizedFieldKernel μ s) k)
  let Q := fun k => jointPhysicalPolynomial s (jointMidpointPolynomial
    (jointNormalizedMomentumKernel μ s) k)
  let u := fun α => ofReal (v.field α)
  let w := fun α => ofReal (v.momentum α)
  have he : complexify (jointPolynomialIncrement hμ hs n) =
      (jointPolynomialMomentOperator u (P (n + 1)) + jointPolynomialMomentOperator w (Q (n + 1))) -
        (jointPolynomialMomentOperator u (P n) + jointPolynomialMomentOperator w (Q n)) := by
    simp only [jointPolynomialIncrement, jointPolynomialKernelOperator_eq_moments hμ hs v,
      complexify_sub_real, complexify_add, complexify_jointPolynomialMomentOperator, u, w, P, Q]
  have hp (k : ℕ) : (P k).totalDegree ≤ 9 * k :=
    (totalDegree_jointPhysicalPolynomial_le s _).trans (jointMidpointPolynomial_degree _ k)
  have hq (k : ℕ) : (Q k).totalDegree ≤ 9 * k :=
    (totalDegree_jointPhysicalPolynomial_le s _).trans (jointMidpointPolynomial_degree _ k)
  have ha := complexify_isSelfAdjoint (jointPolynomialIncrement_isSelfAdjoint hμ hs n)
  rw [he] at ha
  have h := nuclear_jointPolynomial_difference_le u w (P (n + 1)) (Q (n + 1)) (P n) (Q n)
    (hp (n + 1)) (hq (n + 1)) ((hp n).trans (by omega)) ((hq n).trans (by omega)) ha
  rw [← he, norm_complexify] at h
  exact h

theorem nuclear_jointPolynomialIncrement_le {μ s : ℝ}
    (hμ : 0 < μ) (hs : 157286400 ≤ s) (n : ℕ) :
    operatorTraceNorm (complexify (jointPolynomialIncrement hμ (show 600 ≤ s by linarith) n)) ≤
      ENNReal.ofReal ((jointPolynomialIncrementRank n : ℝ) *
        (2 * jointPolynomialErrorConstant * jointCommonEnvelope μ s * (78643200 / s) ^ n)) := by
  apply (nuclear_jointPolynomialIncrement_le_rank hμ _ n).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (norm_jointPolynomialIncrement_le hμ hs n) (Nat.cast_nonneg _)

end VacuumBellSeparation
