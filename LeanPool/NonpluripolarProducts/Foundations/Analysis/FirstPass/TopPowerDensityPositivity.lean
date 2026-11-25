/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.CoordinateWedgePullback
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.StandardHermitianTwoForm
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.StandardKahlerTopPower

/-!
# Positivity and monotonicity of the top-power density on `(1,1)`-forms

Let `ω = Im⟪·,·⟫` be the standard form on `ℂⁿ`.  Every semipositive real
`(1,1)`-form is `A = S^* ω` for a complex linear `S`
(`exists_linearMap_eq_standard_compContinuousLinearMap`), and the genuine top
power transforms by the real determinant (`actualTopPowerDensity_compContinuousLinearMap`),
which for complex linear `S` is `|det S|²`.  Hence
`actualTopPowerDensity A = |det S|² · actualTopPowerDensity ω`, and:

* `actualTopPowerDensity_nonneg`: the density of a semipositive `(1,1)`-form is
  nonnegative;
* `actualTopPowerDensity_le_add`: it is monotone under adding a semipositive
  `(1,1)`-form (`det(S^*S) ≤ det(S^*S + R^*R)`);
* `actualTopPowerDensity_pos`: it is positive for strictly positive forms;
* `pow_mul_le_actualTopPowerDensity`: if `λ‖v‖² ≤ A(v, iv)` then
  `λⁿ · density(ω) ≤ density(A)`.

The density of `ω` itself is `n!` (`StandardKahlerTopPower`).
-/

@[expose] public section

open scoped InnerProductSpace

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

noncomputable section

open PositiveClasses

variable {n : ℕ}

/-- The density of `S^* ω` is `|det S|²` times the density of `ω`. -/
theorem actualTopPowerDensity_standard_comp (S : ComplexModel n →ₗ[ℂ] ComplexModel n) :
    actualTopPowerDensity ((standardHermitianTwoForm n).compContinuousLinearMap
        (LinearMap.toContinuousLinearMap (S.restrictScalars ℝ))) =
      Complex.normSq (LinearMap.det S) * actualTopPowerDensity (standardHermitianTwoForm n) := by
  rw [actualTopPowerDensity_compContinuousLinearMap, ← normSq_det_eq_realDet]
  rfl

variable (n) in
/-- The standard form has positive top-power density (it is `n!`). -/
theorem actualTopPowerDensity_standardHermitianTwoForm_pos :
    0 < actualTopPowerDensity (standardHermitianTwoForm n) :=
  actualTopPowerDensity_pos_of_apply_eq_im _ standardHermitianTwoForm_apply

theorem actualTopPowerDensity_nonneg {A : CoordinateRealTwoForm n} (hA : IsOneOne A)
    (hpos : CoefficientSemipositive A) : 0 ≤ actualTopPowerDensity A := by
  obtain ⟨S, rfl⟩ := exists_linearMap_eq_standard_compContinuousLinearMap hA hpos
  rw [actualTopPowerDensity_standard_comp]
  exact mul_nonneg (Complex.normSq_nonneg _) (actualTopPowerDensity_standardHermitianTwoForm_pos
    n).le

theorem actualTopPowerDensity_le_add {A B : CoordinateRealTwoForm n} (hA : IsOneOne A)
    (hApos : CoefficientSemipositive A) (hB : IsOneOne B) (hBpos : CoefficientSemipositive B) :
    actualTopPowerDensity A ≤ actualTopPowerDensity (A + B) := by
  have hAB : IsOneOne (A + B) := fun u v => by
    simp only [ContinuousAlternatingMap.add_apply, hA u v, hB u v]
  have hABpos : CoefficientSemipositive (A + B) := fun v => by
    simpa only [ContinuousAlternatingMap.add_apply] using add_nonneg (hApos v) (hBpos v)
  obtain ⟨S, hS⟩ := exists_linearMap_eq_standard_compContinuousLinearMap hA hApos
  obtain ⟨R, hR⟩ := exists_linearMap_eq_standard_compContinuousLinearMap hB hBpos
  obtain ⟨W, hW⟩ := exists_linearMap_eq_standard_compContinuousLinearMap hAB hABpos
  have hdet : Complex.normSq (LinearMap.det S) ≤ Complex.normSq (LinearMap.det W) := by
    refine normSq_det_le_of_standard_comp_add S R W fun v w => ?_
    have h := congrArg (fun F : CoordinateRealTwoForm n => F ![v, w]) hW
    have hA' := congrArg (fun F : CoordinateRealTwoForm n => F ![v, w]) hS
    have hB' := congrArg (fun F : CoordinateRealTwoForm n => F ![v, w]) hR
    simp only [ContinuousAlternatingMap.add_apply,
      standardHermitianTwoForm_compContinuousLinearMap_apply] at h hA' hB'
    rw [← h, ← hA', ← hB']
  rw [hW, hS, actualTopPowerDensity_standard_comp, actualTopPowerDensity_standard_comp]
  exact mul_le_mul_of_nonneg_right hdet (actualTopPowerDensity_standardHermitianTwoForm_pos n).le

theorem actualTopPowerDensity_pos {A : CoordinateRealTwoForm n} (hA : IsOneOne A)
    (hpos : IsStrictlyPositive A) : 0 < actualTopPowerDensity A := by
  have hsemi : CoefficientSemipositive A := fun v => by
    rcases eq_or_ne v 0 with rfl | hv
    · rw [smul_zero, A.map_eq_zero_of_eq ![0, 0] (i := 0) (j := 1) (by simp) (by decide)]
    · exact (hpos v hv).le
  obtain ⟨S, hS⟩ := exists_linearMap_eq_standard_compContinuousLinearMap hA hsemi
  have hdet : LinearMap.det S ≠ 0 := by
    refine det_ne_zero_of_standard_comp_strictlyPositive (A := A) (fun v w => ?_) hpos
    rw [hS, standardHermitianTwoForm_compContinuousLinearMap_apply]
  rw [hS, actualTopPowerDensity_standard_comp]
  exact mul_pos (Complex.normSq_pos.mpr hdet) (actualTopPowerDensity_standardHermitianTwoForm_pos
    n)

/-- A uniform lower bound for the density of a uniformly positive `(1,1)`-form. -/
theorem pow_mul_le_actualTopPowerDensity {A : CoordinateRealTwoForm n} (hA : IsOneOne A)
    {c : ℝ} (hc : 0 ≤ c) (hcoer : ∀ v, c * ‖v‖ ^ 2 ≤ A ![v, Complex.I • v]) :
    c ^ n * actualTopPowerDensity (standardHermitianTwoForm n) ≤ actualTopPowerDensity A := by
  set S : ComplexModel n →ₗ[ℂ] ComplexModel n := ((Real.sqrt c : ℝ) : ℂ) • LinearMap.id
  set B := (standardHermitianTwoForm n).compContinuousLinearMap
    (LinearMap.toContinuousLinearMap (S.restrictScalars ℝ))
  have hBapply (v w : ComplexModel n) : B ![v, w] = c * (inner ℂ v w).im := by
    simp only [B, standardHermitianTwoForm_compContinuousLinearMap_apply, S,
      LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
    rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt hc, Complex.im_ofReal_mul]
  have hB : IsOneOne B := fun u v => by
    rw [hBapply, hBapply, ← standardHermitianTwoForm_apply, ← standardHermitianTwoForm_apply,
      standardHermitianTwoForm_isOneOne n u v]
  have hBpos : CoefficientSemipositive B := fun v => by
    rw [hBapply, ← standardHermitianTwoForm_apply, standardHermitianTwoForm_apply_I_smul_self]
    positivity
  have hD : IsOneOne (A - B) := fun u v => by
    simp only [ContinuousAlternatingMap.sub_apply, hA u v, hB u v]
  have hDpos : CoefficientSemipositive (A - B) := fun v => by
    simp only [ContinuousAlternatingMap.sub_apply, sub_nonneg]
    rw [hBapply, ← standardHermitianTwoForm_apply, standardHermitianTwoForm_apply_I_smul_self]
    exact hcoer v
  have hmono := actualTopPowerDensity_le_add hB hBpos hD hDpos
  rw [add_sub_cancel] at hmono
  refine le_trans (le_of_eq ?_) hmono
  rw [actualTopPowerDensity_standard_comp]
  congr 1
  simp only [S, LinearMap.det_smul, LinearMap.det_id, mul_one, map_pow, Complex.normSq_ofReal,
    finrank_euclideanSpace, Fintype.card_fin]
  rw [Real.mul_self_sqrt hc]

end

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
