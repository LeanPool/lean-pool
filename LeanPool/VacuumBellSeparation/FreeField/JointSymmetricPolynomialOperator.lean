/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialFormRank
public import LeanPool.VacuumBellSeparation.Gaussian.SymmetricRankOneTrace
public import LeanPool.VacuumBellSeparation.Gaussian.FiniteRankNuclearBound
public import LeanPool.VacuumBellSeparation.Polynomial.MultivariateCoefficientNorm

/-!
# Genuine selfadjoint weighted polynomial operators

Negative symmetrization implements the manuscript's oriented polynomial
plus its transpose. The nuclear bound uses the actual coefficient sum,
not the number of monomials. No inverse reserve is involved.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian ContinuousLinearMap InnerProductSpace MvPolynomial
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Continuous linear map for the joint symmetric polynomial operator, of type `E →L[ℂ] E`. -/
def jointSymmetricPolynomialOperator (v : (Fin 3 → ℕ) → E)
    (P : MvPolynomial (Fin 6) ℂ) : E →L[ℂ] E :=
  -(∑ d ∈ P.support, (P.coeff d).re •
    symmetricRankOne (v (spatialSixLeftExponent d)) (v (spatialSixRightExponent d)))

theorem jointSymmetricPolynomialOperator_isSelfAdjoint (v : (Fin 3 → ℕ) → E)
    (P : MvPolynomial (Fin 6) ℂ) : IsSelfAdjoint (jointSymmetricPolynomialOperator v P) := by
  apply IsSelfAdjoint.neg
  apply isSelfAdjoint_sum
  intro d hd
  exact (show IsSelfAdjoint (P.coeff d).re from isSelfAdjoint_iff.mpr rfl).smul
    (symmetricRankOne_isSelfAdjoint _ _)

omit [CompleteSpace E] in
theorem range_jointSymmetricPolynomialOperator_le (v : (Fin 3 → ℕ) → E)
    (P : MvPolynomial (Fin 6) ℂ) {D : ℕ} (hP : P.totalDegree ≤ D) :
    (jointSymmetricPolynomialOperator v P).toLinearMap.range ≤
      spatialMomentDegreeRange (𝕜 := ℂ) v D := by
  rintro _ ⟨x, rfl⟩
  change jointSymmetricPolynomialOperator v P x ∈ spatialMomentDegreeRange (𝕜 := ℂ) v D
  simp only [jointSymmetricPolynomialOperator, neg_apply, _root_.sum_apply, smul_apply,
    symmetricRankOne, add_apply, rankOne_apply]
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro d hd
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  apply Submodule.smul_mem
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    exact mem_spatialMomentDegreeRange v D _ (fun i =>
      (MvPolynomial.le_degreeOf_of_mem_support (Fin.castAdd 3 i) hd).trans
        ((MvPolynomial.degreeOf_le_totalDegree P _).trans hP))
  · apply Submodule.smul_mem
    exact mem_spatialMomentDegreeRange v D _ (fun i =>
      (MvPolynomial.le_degreeOf_of_mem_support (Fin.natAdd 3 i) hd).trans
        ((MvPolynomial.degreeOf_le_totalDegree P _).trans hP))

instance finiteDimensional_range_jointSymmetricPolynomialOperator
    (v : (Fin 3 → ℕ) → E) (P : MvPolynomial (Fin 6) ℂ) :
    FiniteDimensional ℂ (jointSymmetricPolynomialOperator v P).toLinearMap.range :=
  Submodule.finiteDimensional_of_le (range_jointSymmetricPolynomialOperator_le v P le_rfl)

theorem nuclear_jointSymmetricPolynomialOperator_le (v : (Fin 3 → ℕ) → E)
    (P : MvPolynomial (Fin 6) ℂ) :
    operatorTraceNorm (jointSymmetricPolynomialOperator v P) ≤
      ENNReal.ofReal (2 * ∑ d ∈ P.support,
        ‖P.coeff d‖ * (‖v (spatialSixLeftExponent d)‖ * ‖v (spatialSixRightExponent d)‖)) := by
  classical
  let A := fun d : P.support => (P.coeff d).re •
    symmetricRankOne (v (spatialSixLeftExponent d)) (v (spatialSixRightExponent d))
  have hc (d : P.support) : IsCompactOperator (A d) :=
    (symmetricRankOne_isCompactOperator _ _).smul _
  have ha (d : P.support) : IsSelfAdjoint (A d) :=
    (show IsSelfAdjoint (P.coeff d).re from isSelfAdjoint_iff.mpr rfl).smul
      (symmetricRankOne_isSelfAdjoint _ _)
  have hs := operatorTraceNorm_tsum_le hc ha
    (Summable.of_finite : Summable fun d : P.support => ‖A d‖)
  have ht (d : P.support) : operatorTraceNorm (A d) ≤
      ENNReal.ofReal (2 * ‖P.coeff d‖ *
        (‖v (spatialSixLeftExponent d)‖ * ‖v (spatialSixRightExponent d)‖)) := by
    dsimp only [A]
    rw [operatorTraceNorm_real_smul]
    apply (_root_.mul_le_mul_right (operatorTraceNorm_symmetricRankOne_le _ _) _).trans
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm (P.coeff d))
      (show 0 ≤ 2 * (‖v (spatialSixLeftExponent d)‖ * ‖v
        (spatialSixRightExponent d)‖) by positivity)
    nlinarith
  have hsumA : (∑ d : P.support, A d) = ∑ d ∈ P.support,
      (P.coeff d).re •
        symmetricRankOne (v (spatialSixLeftExponent d)) (v (spatialSixRightExponent d)) :=
    Finset.sum_coe_sort P.support (fun d => (P.coeff d).re •
      symmetricRankOne (v (spatialSixLeftExponent d)) (v (spatialSixRightExponent d)))
  rw [jointSymmetricPolynomialOperator, operatorTraceNorm_neg]
  calc
    _ ≤ ∑ d : P.support, operatorTraceNorm (A d) := by
      simpa only [tsum_fintype, hsumA] using hs
    _ ≤ ∑ d : P.support, ENNReal.ofReal
        (2 * ‖P.coeff d‖ * (‖v (spatialSixLeftExponent d)‖ * ‖v (spatialSixRightExponent d)‖)) :=
      Finset.sum_le_sum fun d _ => ht d
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
        Finset.sum_coe_sort P.support (fun d => 2 * ‖P.coeff d‖ *
          (‖v (spatialSixLeftExponent d)‖ * ‖v (spatialSixRightExponent d)‖))]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

theorem symmetricRankOne_selfAdjoint_sandwich (R : E →L[ℂ] E)
    (hR : IsSelfAdjoint R) (u v : E) :
    R * symmetricRankOne u v * R = symmetricRankOne (R u) (R v) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp, symmetricRankOne, add_apply, rankOne_apply,
    map_add, map_smul]
  have hi (y : E) : inner ℂ y (R x) = inner ℂ (R y) x := by
    rw [← adjoint_inner_left, hR.adjoint_eq]
  rw [hi u, hi v]

theorem jointSymmetricPolynomialOperator_sandwich (R : E →L[ℂ] E)
    (hR : IsSelfAdjoint R) (v : (Fin 3 → ℕ) → E) (P : MvPolynomial (Fin 6) ℂ) :
    R * jointSymmetricPolynomialOperator v P * R =
      jointSymmetricPolynomialOperator (fun α => R (v α)) P := by
  simp only [jointSymmetricPolynomialOperator, mul_neg, neg_mul,
    Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    symmetricRankOne_selfAdjoint_sandwich R hR]

end VacuumBellSeparation
