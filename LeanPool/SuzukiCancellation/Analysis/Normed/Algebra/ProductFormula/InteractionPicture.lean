/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Ring.ContractionProduct
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ConjugationIntegral

/-!
# Interaction picture products

The exact interaction picture for a repeated splitting is an ordered product
of conjugated single-step increments. Finite contraction bounds retain the
operator sum as the leading term.

## Main definitions

* `TrotterError.interactionIncrement`: a transported single-step increment.

## Main results

* `TrotterError.interactionIncrement_eq_mul_sub_mul`: the single-step error at the cell endpoints.
* `TrotterError.interactionProduct_eq_contractionProduct`: the exact finite product.
* `TrotterError.norm_interactionProduct_sub_midpoint_le`: the discrete operator bound.
* `FQFP.norm_pow_sub_exp_eq_interaction`: equality of the physical and interaction error norms.
* `FQFP.abs_norm_pow_sub_exp_sub_norm_le`: the operator remainder controls the norm error.
-/

@[expose] public noncomputable section

open NormedSpace Finset FQFP
open scoped RealScalar

namespace TrotterError

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- A single-step error transported to the `k`-th interaction picture. -/
def interactionIncrement (G S : A) (h : ℝ) (k : ℕ) : A :=
  exp (-((k : ℝ) * h) • G) * (exp ((-h) • G) * S - 1) * exp (((k : ℝ) * h) • G)

/-- Adding the transported increment to the identity leaves a transported splitting factor. -/
lemma one_add_interactionIncrement (G S : A) (h : ℝ) (k : ℕ) :
    1 + interactionIncrement G S h k =
      exp (-(((k : ℝ) + 1) * h) • G) * S * exp (((k : ℝ) * h) • G) := by
  unfold interactionIncrement
  rw [mul_sub, sub_mul, mul_one, exp_smul_mul_exp_smul, neg_add_cancel, zero_smul, exp_zero,
    add_sub_cancel, ← mul_assoc,
    exp_smul_mul_exp_smul, show -((k : ℝ) * h) + -h = -(((k : ℝ) + 1) * h) by ring]

/-- The increment is the single-step error multiplied by the inverse evolution at the
right endpoint and the forward evolution at the left endpoint. -/
lemma interactionIncrement_eq_mul_sub_mul (G S : A) (h : ℝ) (k : ℕ) :
    interactionIncrement G S h k =
      exp (-(((k : ℝ) + 1) * h) • G) * (S - exp (h • G)) * exp (((k : ℝ) * h) • G) := by
  rw [mul_sub, sub_mul, ← one_add_interactionIncrement, exp_smul_mul_exp_smul,
    exp_smul_mul_exp_smul, show -(((k : ℝ) + 1) * h) + h + (k : ℝ) * h = 0 by ring]
  simp

/-- The interaction-picture splitting power is precisely the ordered finite product. -/
theorem interactionProduct_eq_contractionProduct (G S : A) (h : ℝ) (r : ℕ) :
    exp (-((r : ℝ) * h) • G) * S ^ r = contractionProduct (interactionIncrement G S h) r := by
  apply eq_contractionProduct_of_recurrence (interactionIncrement G S h)
    (fun k ↦ exp (-((k : ℝ) * h) • G) * S ^ k)
  · simp
  · intro k
    rw [one_add_interactionIncrement]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [mul_assoc, mul_assoc, ← mul_assoc (exp (((k : ℝ) * h) • G)),
      neg_smul ((k : ℝ) * h), exp_mul_neg_self, one_mul, ← mul_assoc, pow_succ', mul_assoc]

/-- Exponential norm bounds transfer the single-step norm to every transported increment. -/
lemma norm_interactionIncrement_eq (G S : A) (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (h : ℝ) (k : ℕ) :
    ‖interactionIncrement G S h k‖ = ‖S - exp (h • G)‖ := by
  rw [interactionIncrement_eq_mul_sub_mul, norm_mul_exp_smul_eq_of_le_one G _ hG,
    norm_exp_smul_mul_eq_of_le_one G _ hG]

/-- A contraction splitting and two-sided exponential controls make every factor contractive. -/
lemma norm_one_add_interactionIncrement_le_one (G S : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (hS : ‖S‖ ≤ 1) (h : ℝ) (k : ℕ) :
    ‖1 + interactionIncrement G S h k‖ ≤ 1 := by
  rw [one_add_interactionIncrement, norm_mul_exp_smul_eq_of_le_one G _ hG,
    norm_exp_smul_mul_eq_of_le_one G _ hG]
  exact hS

/-- The centered single-step error transported to a midpoint is the interaction increment. -/
lemma interactionIncrement_eq_midpoint_conj (G S : A) (h : ℝ) (k : ℕ) :
    interactionIncrement G S h k =
      expSMulConj (-G)
        (exp ((-h / 2) • G) * (S - exp (h • G)) * exp ((-h / 2) • G))
        (((k : ℝ) + 1 / 2) * h) := by
  rw [interactionIncrement_eq_mul_sub_mul]
  simp only [expSMulConj, smul_neg, ← neg_smul, neg_neg]
  rw [show -(((k : ℝ) + 1) * h) = -(((k : ℝ) + 1 / 2) * h) + -h / 2 by ring,
    show (k : ℝ) * h = -h / 2 + ((k : ℝ) + 1 / 2) * h by ring,
    ← exp_smul_mul_exp_smul, ← exp_smul_mul_exp_smul]
  simp only [mul_assoc]

/-- A centered local estimate transports unchanged to each interaction increment. -/
theorem norm_interactionIncrement_sub_conj_le (G S B : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (h : ℝ) {η : ℝ}
    (hlocal : ‖exp ((-h / 2) • G) * (S - exp (h • G)) * exp ((-h / 2) • G) -
      B‖ ≤ η) (k : ℕ) :
    ‖interactionIncrement G S h k -
      expSMulConj (-G) B (((k : ℝ) + 1 / 2) * h)‖ ≤ η := by
  have hneg (t : ℝ) : ‖exp (t • (-G))‖ ≤ 1 := by simpa only [smul_neg, neg_smul] using hG (-t)
  rwa [interactionIncrement_eq_midpoint_conj, ← dist_eq_norm,
    (isometry_expSMulConj_of_le_one (-G) hneg _).dist_eq, dist_eq_norm]

/-- A homogeneous quintic centered estimate transports to a midpoint conjugation. -/
theorem norm_interactionIncrement_sub_midpoint_le (G S L : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (h : ℝ) {η : ℝ}
    (hlocal : ‖exp ((-h / 2) • G) * (S - exp (h • G)) * exp ((-h / 2) • G) -
      h ^ 5 • L‖ ≤ η) (k : ℕ) :
    ‖interactionIncrement G S h k -
      h ^ 5 • expSMulConj (-G) L (((k : ℝ) + 1 / 2) * h)‖ ≤ η := by
  simpa only [expSMulConj, mul_smul_comm, smul_mul_assoc] using
    norm_interactionIncrement_sub_conj_le G S (h ^ 5 • L) hG h hlocal k

/-- **Discrete operator remainder.** Finite contraction products retain any complete
centered main term, with quadratic accumulation of the single-step distances. -/
theorem norm_interactionProduct_sub_sum_conj_le (G S B : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (h : ℝ) {η δ : ℝ}
    (hlocal : ‖exp ((-h / 2) • G) * (S - exp (h • G)) * exp ((-h / 2) • G) -
      B‖ ≤ η)
    (hδ : ‖S - exp (h • G)‖ ≤ δ) (r : ℕ) :
    ‖exp (-((r : ℝ) * h) • G) * S ^ r - 1 -
      ∑ k ∈ range r, expSMulConj (-G) B (((k : ℝ) + 1 / 2) * h)‖ ≤
        (r : ℝ) * η + (r : ℝ) * ((r : ℝ) - 1) / 2 * δ ^ 2 := by
  have hrem := norm_contractionProduct_sub_one_sub_sum_le
    (interactionIncrement G S h)
    (norm_one_add_interactionIncrement_le_one G S hG hS h)
    (fun k ↦ (norm_interactionIncrement_eq G S hG h k).le.trans hδ) r
  rw [← interactionProduct_eq_contractionProduct G S h r] at hrem
  rw [add_comm ((r : ℝ) * η)]
  refine (norm_sub_le_norm_sub_add_norm_sub _ (∑ k ∈ range r, interactionIncrement G S h k) _).trans
    (add_le_add hrem ?_)
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ _k ∈ range r, η :=
      (norm_sum_le _ _).trans (sum_le_sum fun k _ ↦
        norm_interactionIncrement_sub_conj_le G S B hG h hlocal k)
    _ = _ := by simp

/-- A quintic centered main term gives the original discrete midpoint bound. -/
theorem norm_interactionProduct_sub_midpoint_le (G S L : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (h : ℝ) {η δ : ℝ}
    (hlocal : ‖exp ((-h / 2) • G) * (S - exp (h • G)) * exp ((-h / 2) • G) -
      h ^ 5 • L‖ ≤ η)
    (hδ : ‖S - exp (h • G)‖ ≤ δ) (r : ℕ) :
    ‖exp (-((r : ℝ) * h) • G) * S ^ r - 1 -
      h ^ 4 • midpointConjugationIntegral G L r h‖ ≤
        (r : ℝ) * η + (r : ℝ) * ((r : ℝ) - 1) / 2 * δ ^ 2 := by
  simpa only [midpointConjugationIntegral, smul_smul, ← pow_succ, smul_sum,
    expSMulConj, mul_smul_comm, smul_mul_assoc] using
    norm_interactionProduct_sub_sum_conj_le G S (h ^ 5 • L) hG hS h hlocal hδ r

end TrotterError

namespace FQFP

open TrotterError

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- Multiplication by the inverse exact evolution identifies the physical
global error norm with the interaction-picture error norm. -/
theorem norm_pow_sub_exp_eq_interaction (G S : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (t : ℝ) (r : ℕ) :
    ‖S ^ r - exp (t • G)‖ = ‖exp ((-t) • G) * S ^ r - 1‖ := by
  rw [← norm_exp_smul_mul_eq_of_le_one G (S ^ r - exp (t • G)) hG (-t), mul_sub,
    TrotterError.exp_smul_mul_exp_smul]
  simp

/-- The interaction-picture operator remainder bounds the error in the predicted norm. -/
theorem abs_norm_pow_sub_exp_sub_norm_le (G S M : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (t : ℝ) (r : ℕ) :
    |‖S ^ r - exp (t • G)‖ - ‖M‖| ≤ ‖exp ((-t) • G) * S ^ r - 1 - M‖ := by
  rw [norm_pow_sub_exp_eq_interaction G S hG]
  exact abs_norm_sub_norm_le _ _

end FQFP
