/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.AaronsonAmbainis.RowDefs

/-!
# Characters at special points

`Row.sgn b = (-1)^b`, the all-false point `Row.zero`, the unit points `Row.unit b`, the value of a
character at these points and at a flipped point, and `chi S * chi T = chi (S ∆ T)`.

Since `false` stands for `+1` and `true` for `-1`, the point `Row.zero β` is the point `(1,…,1)` of
Section 6.3 of the paper, and `Row.unit b` is obtained from it by changing the sign of the
coordinate `b`.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Row

open Finset

/-- The sign `(-1)^b` of a bit. -/
noncomputable def sgn (b : Bool) : ℝ := if b then -1 else 1

@[simp] lemma sgn_true : sgn true = -1 := by simp [sgn]

@[simp] lemma sgn_false : sgn false = 1 := by simp [sgn]

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp

lemma abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp

lemma sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp

/-- The all-false point of a cube. -/
def zero (β : Type*) : Cube β := fun _ => false

/-- The point with exactly the coordinate `b` equal to `true`. -/
def unit {β : Type*} [DecidableEq β] (b : β) : Cube β := fun b' => decide (b' = b)

variable {ι : Type*}

lemma chi_eq_prod_sgn (T : Finset ι) (x : Cube ι) : chi T x = ∏ i ∈ T, sgn (x i) := rfl

lemma chi_zero (U : Finset ι) : chi U (zero ι) = 1 := by
  simp [chi, zero]

lemma chi_unit [DecidableEq ι] (U : Finset ι) (b : ι) :
    chi U (unit b) = if b ∈ U then -1 else 1 := by
  simp [chi, unit, Finset.prod_ite_eq']

/-- The sign of a coordinate of a flipped point. -/
lemma sgn_flipSet [DecidableEq ι] (x : Cube ι) (U : Finset ι) (i : ι) :
    sgn (flipSet x U i) = sgn (x i) * (if i ∈ U then -1 else 1) := by
  by_cases h : i ∈ U <;> simp [flipSet, h, sgn_not]

/-- The character at a flipped point. -/
lemma chi_flipSet [DecidableEq ι] (T U : Finset ι) (x : Cube ι) :
    chi T (flipSet x U) = ∏ i ∈ T, (sgn (x i) * (if i ∈ U then -1 else 1)) := by
  rw [chi_eq_prod_sgn]
  exact Finset.prod_congr rfl (fun i _ => sgn_flipSet x U i)

/-- Characters multiply by symmetric difference. -/
lemma chi_mul_chi [Finite ι] [DecidableEq ι] (S T : Finset ι) (x : Cube ι) :
    chi S x * chi T x = chi (symmDiff S T) x := by
  classical
  let := Fintype.ofFinite ι
  rw [chi_eq_prod_sgn, chi_eq_prod_sgn, chi_eq_prod_sgn,
    ← Fintype.prod_ite_mem S (fun i => sgn (x i)), ← Fintype.prod_ite_mem T (fun i => sgn (x i)),
    ← Fintype.prod_ite_mem (symmDiff S T) (fun i => sgn (x i)), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [Finset.mem_symmDiff, hS, hT, sgn_mul_self]

end Row
end AaronsonAmbainis
