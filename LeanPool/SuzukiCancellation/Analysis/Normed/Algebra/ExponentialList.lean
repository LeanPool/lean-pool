/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.Exponential

import LeanPool.SuzukiCancellation.Algebra.BigOperators.Group.List.Fin

/-!
# Ordered lists of exponentials

Reversing and negating the arguments inverts an ordered exponential product.
The sum of the argument norms controls its distance from one. Neither result
requires the arguments to commute.

## Main results

* `prod_exp_mul_reverse_neg_eq_one`: inverse cancellation in reverse order.
* `norm_prod_exp_sub_one_le`: the scalar exponential majorant for any finite list.
-/

@[expose] public noncomputable section

open NormedSpace

namespace FQFP

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- Negating the arguments and reversing their order gives a right inverse. -/
lemma prod_exp_mul_reverse_neg_eq_one (l : List A) :
    (l.map exp).prod * (l.reverse.map fun x ↦ exp (-x)).prod = 1 :=
  TrotterError.List.prod_mul_rev_eq_one_of_mul_eq_one l exp (fun x ↦ exp (-x))
    TrotterError.exp_mul_neg_self

/-- The distance of an ordered exponential product from one has a scalar majorant. -/
lemma norm_prod_exp_sub_one_le [NormOneClass A] (l : List A) :
    ‖(l.map exp).prod - 1‖ ≤ Real.exp ((l.map norm).sum) - 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [show exp a * (l.map exp).prod - 1 =
        exp a * ((l.map exp).prod - 1) + (exp a - 1) by noncomm_ring]
      calc
        _ ≤ ‖exp a‖ * ‖(l.map exp).prod - 1‖ + ‖exp a - 1‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
        _ ≤ Real.exp ‖a‖ * (Real.exp ((l.map norm).sum) - 1) +
            (Real.exp ‖a‖ - 1) :=
          add_le_add (mul_le_mul (norm_exp_le a) ih (norm_nonneg _)
            (Real.exp_pos _).le) (norm_exp_sub_one_le a)
        _ = _ := by
          rw [Real.exp_add]
          ring

/-- A small sum of argument norms puts the product in the logarithm's convergence ball. -/
lemma norm_prod_exp_sub_one_lt_one [NormOneClass A] (l : List A)
    (hl : (l.map norm).sum < Real.log 2) : ‖(l.map exp).prod - 1‖ < 1 := by
  refine (norm_prod_exp_sub_one_le l).trans_lt ?_
  have h := Real.exp_strictMono hl
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  linarith only [h]

end FQFP
