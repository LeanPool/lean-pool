/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

module

public import LeanPool.CatalyticRegisters.CommRing
public import Mathlib.Algebra.Ring.Defs

/-! # Using catalytic register programs over Mathlib commutative rings -/

namespace Catalytic

@[expose] public section

/-- Interpret the register evaluator's ring operations using a Mathlib commutative ring.
Use `letI := CRing.ofCommRing R` when invoking its correctness results. -/
@[instance_reducible]
def CRing.ofCommRing (R : Type*) [CommRing R] : CRing R where
  toAdd := inferInstance
  toMul := inferInstance
  toNeg := inferInstance
  toZero := inferInstance
  toOne := inferInstance
  add_assoc := _root_.add_assoc
  add_comm := _root_.add_comm
  zero_add := _root_.zero_add
  add_neg := add_neg_cancel
  mul_assoc := _root_.mul_assoc
  mul_comm := _root_.mul_comm
  one_mul x := _root_.one_mul x
  left_distrib := mul_add

@[simp]
theorem CRing.pow_ofCommRing {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    @CRing.pow R (CRing.ofCommRing R) x n = x ^ n := by
  induction n with
  | zero => exact (_root_.pow_zero x).symm
  | succ number inductionHypothesis =>
    change @CRing.pow R (CRing.ofCommRing R) x number * x = x ^ (number + 1)
    rw [inductionHypothesis, _root_.pow_succ]

end

end Catalytic
