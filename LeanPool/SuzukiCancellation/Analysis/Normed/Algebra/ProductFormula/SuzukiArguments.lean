/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: factored out the algebraic argument lists. -/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Module

/-! Ordered arguments of the five-stage Suzuki composition and its symmetric half. -/

@[expose] public noncomputable section

namespace FQFP.BCH

section Full

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- The eleven ordered arguments of the five-block Suzuki composition. -/
def fiveStageStrangArguments (a b : A) (p t : K) : List A :=
  [(p / 2 * t) • a, (p * t) • b, (p * t) • a, (p * t) • b,
    ((1 - 3 * p) / 2 * t) • a, ((1 - 4 * p) * t) • b,
    ((1 - 3 * p) / 2 * t) • a, (p * t) • b, (p * t) • a,
    (p * t) • b, (p / 2 * t) • a]

/-- The argument list is unchanged by reversal. -/
lemma fiveStageStrangArguments_reverse (a b : A) (p t : K) :
    (fiveStageStrangArguments a b p t).reverse = fiveStageStrangArguments a b p t := rfl

/-- Time reflection negates each exponent argument. -/
lemma fiveStageStrangArguments_neg (a b : A) (p t : K) :
    fiveStageStrangArguments a b p (-t) = (fiveStageStrangArguments a b p t).map Neg.neg := by
  simp [fiveStageStrangArguments, mul_neg, neg_smul]

/-- Each argument is homogeneous of degree one in time. -/
lemma fiveStageStrangArguments_smul (a b : A) (p t : K) :
    fiveStageStrangArguments a b p t =
      (fiveStageStrangArguments a b p 1).map (fun x ↦ t • x) := by
  simp [fiveStageStrangArguments, smul_smul, mul_comm]

end Full

section Half

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The six ordered half-generators of the five-stage Strang composition. -/
def fiveStageStrangHalfGenerator (a b : A) (p : ℝ) : Fin 6 → A :=
  ![(p / 2) • a, p • b, p • a, p • b, ((1 - 3 * p) / 2) • a,
    ((1 - 4 * p) / 2) • b]

/-- The six ordered exponential arguments of the symmetric half-product. -/
def fiveStageStrangHalfArguments (a b : A) (p t : ℝ) : List A :=
  List.ofFn (fun i ↦ t • fiveStageStrangHalfGenerator a b p i)

/-- The indexed generators give the half-arguments at unit time. -/
theorem fiveStageStrangHalfGenerator_ofFn (a b : A) (p : ℝ) :
    List.ofFn (fiveStageStrangHalfGenerator a b p) = fiveStageStrangHalfArguments a b p 1 := by
  simp [fiveStageStrangHalfArguments]

/-- The half-arguments scale homogeneously with time. -/
lemma fiveStageStrangHalfArguments_smul (a b : A) (p t : ℝ) :
    fiveStageStrangHalfArguments a b p t =
      (fiveStageStrangHalfArguments a b p 1).map (fun Z ↦ t • Z) := by
  rw [← fiveStageStrangHalfGenerator_ofFn]
  simp [fiveStageStrangHalfArguments]

/-- Reflecting time negates each half-product argument in place. -/
lemma fiveStageStrangHalfArguments_neg (a b : A) (p t : ℝ) :
    fiveStageStrangHalfArguments a b p (-t) =
      (fiveStageStrangHalfArguments a b p t).map Neg.neg := by
  simp [fiveStageStrangHalfArguments, neg_smul]

/-- The half-list generators sum to half of the total generator at unit time. -/
theorem fiveStageStrangHalfArguments_sum (a b : A) (p : ℝ) :
    (fiveStageStrangHalfArguments a b p 1).sum = (1 / 2 : ℝ) • (a + b) := by
  rw [← fiveStageStrangHalfGenerator_ofFn, List.sum_ofFn]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [fiveStageStrangHalfGenerator]
  module

end Half

end FQFP.BCH
