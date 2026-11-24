/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.Palindromic
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.RealScalar

/-!
# The symmetric half of the five-stage Strang product

The ordered six-factor half-product and its reversed counterpart multiply to the
eleven-factor Suzuki product. The central pair of equal exponentials is merged.
This identity uses only the complete normed algebra structure, with no
small-step or matrix assumptions.

## Main definitions and results

* `FQFP.BCH.fiveStageStrangHalfProduct` forms the ordered six-factor half of the Suzuki product.
* `FQFP.BCH.fiveStageStrangProduct_eq_half_mul_reverse` factors the full product into this half
  followed by the same factors in reverse order.
-/

@[expose] public noncomputable section

open NormedSpace
open scoped RealScalar

namespace FQFP.BCH

variable {A : Type*} [NormedRing A]

section

variable [NormedAlgebra ℝ A]

/-- The six ordered exponential arguments of the symmetric half-product. -/
def fiveStageStrangHalfArguments (a b : A) (p t : ℝ) : List A :=
  [(p * t / 2) • a, (p * t) • b, (p * t) • a, (p * t) • b,
    ((1 - 3 * p) * t / 2) • a, ((1 - 4 * p) * t / 2) • b]

/-- Reflecting time negates each half-product argument in place. -/
lemma fiveStageStrangHalfArguments_neg (a b : A) (p t : ℝ) :
    fiveStageStrangHalfArguments a b p (-t) =
      (fiveStageStrangHalfArguments a b p t).map Neg.neg := by
  simp [fiveStageStrangHalfArguments, mul_neg, neg_smul, neg_div]

/-- The half-list generators sum to half of the total generator at unit time. -/
theorem fiveStageStrangHalfArguments_sum (a b : A) (p : ℝ) :
    (fiveStageStrangHalfArguments a b p 1).sum = (1 / 2 : ℝ) • (a + b) := by
  simp [fiveStageStrangHalfArguments, smul_add]
  module

/-- The ordered six-factor half-product. -/
def fiveStageStrangHalfProduct (a b : A) (p t : ℝ) : A :=
  ((fiveStageStrangHalfArguments a b p t).map exp).prod

/-- The reversed half-product at the same time parameter. -/
def fiveStageStrangReverseHalfProduct (a b : A) (p t : ℝ) : A :=
  ((fiveStageStrangHalfArguments a b p t).reverse.map exp).prod

end

variable [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The reversed half is a right inverse of the half-product at reflected time. -/
theorem fiveStageStrangHalfProduct_neg_mul_reverse_eq_one (a b : A) (p t : ℝ) :
    fiveStageStrangHalfProduct a b p (-t) *
      fiveStageStrangReverseHalfProduct a b p t = 1 := by
  have h := FQFP.prod_exp_mul_reverse_neg_eq_one
    (fiveStageStrangHalfArguments a b p (-t))
  simpa [fiveStageStrangHalfProduct, fiveStageStrangReverseHalfProduct,
    fiveStageStrangHalfArguments_neg, List.map_reverse, List.map_map,
    Function.comp_def] using h

/-- The reversed half is also a left inverse of the half-product at reflected time. -/
theorem fiveStageStrangReverseHalfProduct_mul_neg_eq_one (a b : A) (p t : ℝ) :
    fiveStageStrangReverseHalfProduct a b p t *
      fiveStageStrangHalfProduct a b p (-t) = 1 := by
  have h := FQFP.prod_exp_mul_reverse_neg_eq_one
    (fiveStageStrangHalfArguments a b p t).reverse
  simpa [fiveStageStrangHalfProduct, fiveStageStrangReverseHalfProduct,
    fiveStageStrangHalfArguments_neg, List.map_map, Function.comp_def] using h

/-- The Suzuki product is the half-product followed by its reversed half.
This also specifies the order of conjugations used by the symmetric defect. -/
theorem fiveStageStrangProduct_eq_half_mul_reverse (a b : A) (p t : ℝ) :
    fiveStageStrangProduct a b p t =
      fiveStageStrangHalfProduct a b p t *
        fiveStageStrangReverseHalfProduct a b p t := by
  have hcentral : exp (((1 - 4 * p) * t / 2) • b) *
      exp (((1 - 4 * p) * t / 2) • b) =
      exp (((1 - 4 * p) * t) • b) := by
    rw [← exp_add_of_commute (Commute.refl _)]
    congr 1
    rw [← add_smul]
    congr 1
    ring
  simp only [fiveStageStrangProduct_eq, mul_assoc, ← hcentral, fiveStageStrangHalfProduct,
    fiveStageStrangHalfArguments, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, fiveStageStrangReverseHalfProduct, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  rw [show p / 2 * t = p * t / 2 by ring,
    show (1 - 3 * p) / 2 * t = (1 - 3 * p) * t / 2 by ring]

end FQFP.BCH
end
