/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.NumberTheory.NumberField.House

/-! # House bounds used in the interpolation determinant argument -/

@[expose] public section

namespace LeanPool

open Finset NumberField

namespace StrongSix

variable {K : Type*} [Field K] [NumberField K]

theorem house_one' : house (1 : K) = 1 := by
  have := house_intCast (K := K) 1
  simpa using this

theorem house_natCast' (n : ℕ) : house (n : K) = n := by
  have := house_intCast (K := K) n
  simpa using this

theorem house_prod_le' {ι : Type*} (s : Finset ι) (g : ι → K) :
    house (∏ i ∈ s, g i) ≤ ∏ i ∈ s, house (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [house_one']
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (house_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (house_nonneg _))

end StrongSix

end LeanPool
