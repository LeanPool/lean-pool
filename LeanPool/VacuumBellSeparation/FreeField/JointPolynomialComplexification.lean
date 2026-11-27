/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialMidpointForm
public import LeanPool.VacuumBellSeparation.Gaussian.ComplexifiedOperator

/-! # The complex polynomial operator is the true extension of its real form -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem complexify_rankOne_real (x y : E) :
    complexify (rankOne ℝ x y) = rankOne ℂ (ofReal x) (ofReal y) := by
  apply ContinuousLinearMap.ext
  intro z
  apply HilbertComplexification.ext
  · simp only [complexify_re, rankOne_apply, re_smul, ofReal_re, ofReal_im,
      HilbertComplexification.inner_eq, inner_zero_left, add_zero, sub_zero,
      smul_zero, sub_zero]
  · simp only [complexify_im, rankOne_apply, im_smul, ofReal_re, ofReal_im,
      HilbertComplexification.inner_eq, inner_zero_left, add_zero, sub_zero,
      smul_zero, add_zero]

theorem complexify_finset_sum {ι : Type*} (s : Finset ι) (A : ι → E →L[ℝ] E) :
    complexify (∑ i ∈ s, A i) = ∑ i ∈ s, complexify (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, complexify_zero]
  | @insert i s hi ih => rw [Finset.sum_insert hi, complexify_add, ih, Finset.sum_insert hi]

theorem complexify_jointPolynomialMomentOperator (v : (Fin 3 → ℕ) → E)
    (P : MvPolynomial (Fin 6) ℂ) :
    complexify (jointPolynomialMomentOperator (𝕜 := ℝ) v P) =
      jointPolynomialMomentOperator (𝕜 := ℂ) (fun α => ofReal (v α)) P := by
  simp only [jointPolynomialMomentOperator, Algebra.algebraMap_self_apply,
    complexify_finset_sum, complexify_real_smul, complexify_rankOne_real,
    RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal,
    RCLike.algebraMap_eq_ofReal]

theorem norm_complexified_jointPolynomialMomentOperator (v : (Fin 3 → ℕ) → E)
    (P : MvPolynomial (Fin 6) ℂ) :
    ‖jointPolynomialMomentOperator (𝕜 := ℂ) (fun α => ofReal (v α)) P‖ =
      ‖jointPolynomialMomentOperator (𝕜 := ℝ) v P‖ := by
  rw [← complexify_jointPolynomialMomentOperator, norm_complexify]

theorem complexified_jointPolynomialMomentOperator_rank_le
    (v : (Fin 3 → ℕ) → E) (P : MvPolynomial (Fin 6) ℂ) {D : ℕ}
    (hP : P.totalDegree ≤ D) :
    Module.finrank ℂ (complexify (jointPolynomialMomentOperator (𝕜 := ℝ) v P)).toLinearMap.range ≤
      (D + 1) ^ 3 := by
  rw [complexify_jointPolynomialMomentOperator]
  exact finrank_jointPolynomialMomentOperator_le _ P hP

theorem complexify_isSelfAdjoint [CompleteSpace E] {A : E →L[ℝ] E}
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (complexify A) := by
  change (complexify A).adjoint = complexify A
  rw [complexify_adjoint, hA.adjoint_eq]

end VacuumBellSeparation
