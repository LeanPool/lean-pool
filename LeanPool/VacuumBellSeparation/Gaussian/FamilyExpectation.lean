/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SquareSummableFamily
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalState

/-!
# Actual complex expectations from a square-summable vector family

The series Σ⟨v_i,Bv_i⟩ converges absolutely for every bounded B. Its norm
is bounded by the summed squared norms times ‖B‖. It is a genuine bounded
complex-linear positive functional, and total squared norm one gives a
state on the actual bounded-operator algebra.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ComplexOrder

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Family expectation given by `∑' i, inner ℂ (v i) (B (v i))`. -/
def familyExpectation (v : ι → E) (B : E →L[ℂ] E) : ℂ := ∑' i, inner ℂ (v i) (B (v i))

omit [CompleteSpace E] in
theorem norm_familyExpectation_term_le (v : ι → E) (B : E →L[ℂ] E) (i : ι) :
    ‖inner ℂ (v i) (B (v i))‖ ≤ ‖v i‖ ^ 2 * ‖B‖ := by
  calc
    _ ≤ ‖v i‖ * ‖B (v i)‖ := norm_inner_le_norm _ _
    _ ≤ ‖v i‖ * (‖B‖ * ‖v i‖) := mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

omit [CompleteSpace E] in
theorem summable_familyExpectation_terms (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2)
    (B : E →L[ℂ] E) : Summable fun i => inner ℂ (v i) (B (v i)) :=
  (hv.mul_right ‖B‖).of_norm_bounded (norm_familyExpectation_term_le v B)

omit [CompleteSpace E] in
theorem norm_familyExpectation_le (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2)
    (B : E →L[ℂ] E) : ‖familyExpectation v B‖ ≤ (∑' i, ‖v i‖ ^ 2) * ‖B‖ :=
  tsum_of_norm_bounded (hv.hasSum.mul_right ‖B‖) (norm_familyExpectation_term_le v B)

/-- Continuous linear map for the family expectation linear, of type `(E →L[ℂ] E) →ₗ[ℂ] ℂ where
toFun`. -/
def familyExpectationLinear (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2) :
    (E →L[ℂ] E) →ₗ[ℂ] ℂ where
  toFun := familyExpectation v
  map_add' A B := by
    simp only [familyExpectation, add_apply, inner_add_right]
    exact (summable_familyExpectation_terms v hv A).tsum_add
      (summable_familyExpectation_terms v hv B)
  map_smul' c A := by
    simp only [familyExpectation, smul_apply, inner_smul_right, RingHom.id_apply, smul_eq_mul]
    exact tsum_mul_left

/-- Family expectation continuous linear map of type `(E →L[ℂ] E) →L[ℂ] ℂ`. -/
def familyExpectationCLM (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2) :
    (E →L[ℂ] E) →L[ℂ] ℂ :=
  (familyExpectationLinear v hv).mkContinuous (∑' i, ‖v i‖ ^ 2) (norm_familyExpectation_le v hv)

omit [CompleteSpace E] in
theorem familyExpectation_one (v : ι → E) :
    familyExpectation v 1 = (∑' i, ‖v i‖ ^ 2 : ℝ) := by
  unfold familyExpectation
  calc
    _ = ∑' i, ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
      apply tsum_congr
      intro i
      change inner ℂ (v i) (v i) = ((‖v i‖ ^ 2 : ℝ) : ℂ)
      have hi : inner ℂ (v i) (v i) = (‖v i‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
      exact hi.trans (Complex.ofReal_pow ‖v i‖ 2).symm
    _ = _ := (Complex.ofReal_tsum (L := .unconditional ι) (fun i => ‖v i‖ ^ 2)).symm

omit [CompleteSpace E] in
theorem familyExpectation_nonneg (v : ι → E) {B : E →L[ℂ] E} (hB : 0 ≤ B) :
    0 ≤ familyExpectation v B :=
  tsum_nonneg fun i => (ContinuousLinearMap.nonneg_iff_isPositive.mp hB).inner_nonneg_right (v i)

/-- Family state. -/
def familyState (v : ι → E) (hv : Summable fun i => ‖v i‖ ^ 2)
    (hunit : ∑' i, ‖v i‖ ^ 2 = 1) : State E where
  toLinearMap := familyExpectationLinear v hv
  map_one' := by
    change familyExpectation v 1 = 1
    simpa only [hunit, Complex.ofReal_one] using familyExpectation_one v
  map_nonneg' B hB := by
    have h := Complex.nonneg_iff.mp
      (familyExpectation_nonneg v (ContinuousLinearMap.nonneg_iff_isPositive.mpr hB))
    exact ⟨h.2.symm, h.1⟩

end VacuumBellSeparation.Gaussian
