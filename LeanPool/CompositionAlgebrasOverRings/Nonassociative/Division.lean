/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Logic.Function.Defs

/-!
# Division algebras (`GPR 8.6`)

`GPR 8.6` calls an algebra `A` a **division algebra** if it is non-zero and, for every `u ≠ 0`,
the equations `u x = v` and `y u = v` can be solved uniquely — equivalently, the left and right
multiplication operators `L_u` and `R_u` are bijective. This file states that definition for a
possibly non-associative multiplication.

⚠ mathlib's `DivisionRing` is an *associative* structure that carries an inverse operation as
data, so it does not apply to the non-associative algebras of this development; that is why the
predicate is defined here. Note also that, once associativity is dropped, `IsDivision` is strictly
stronger than every nonzero element having a two-sided inverse
(`ConicAlgebra.HasTwoSidedInverses`): the real sedenions separate the two (`GPR Exc. 19.29(e)`,
`ConicAlgebra.not_isDivision_realSedenion`). For unital alternative algebras the two agree
(`GPR 13.8`; for conic algebras, `ConicAlgebra.isDivision_iff_hasTwoSidedInverses`).

## Main definitions

* `IsDivision A` : `A` is a division algebra in the sense of `GPR 8.6`.

## Main results

* `IsDivision.eq_zero_or_eq_zero_of_mul_eq_zero` : a division algebra has no zero divisors
  (`GPR 8.6`).
* `not_isDivision_of_mul_eq_zero` : a pair of nonzero elements with product zero rules out
  division.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 8.6.
-/

@[expose] public section

universe u

/-- **`GPR 8.6`**: `A` is a **division algebra** if it is non-zero and, for every `u ≠ 0`, left and
right multiplication by `u` are bijective — that is, `u x = v` and `y u = v` have unique solutions.

No associativity is assumed. -/
structure IsDivision (A : Type u) [Mul A] [Zero A] : Prop where
  /-- A division algebra is non-zero. -/
  nontrivial : Nontrivial A
  /-- Left multiplication by a nonzero element is bijective. -/
  bijective_mul_left : ∀ u : A, u ≠ 0 → Function.Bijective (u * ·)
  /-- Right multiplication by a nonzero element is bijective. -/
  bijective_mul_right : ∀ u : A, u ≠ 0 → Function.Bijective (· * u)

namespace IsDivision

variable {A : Type u} [MulZeroClass A]

/-- **A division algebra has no zero divisors** (`GPR 8.6`): left multiplication by `x ≠ 0` is
injective and sends `0` to `0`. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero (h : IsDivision A) {x y : A} (hxy : x * y = 0) :
    x = 0 ∨ y = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr ((h.bijective_mul_left x hx).1 (hxy.trans (mul_zero x).symm))

end IsDivision

/-- Two nonzero elements with product zero rule out division. -/
theorem not_isDivision_of_mul_eq_zero {A : Type u} [MulZeroClass A] {x y : A} (hx : x ≠ 0)
    (hy : y ≠ 0) (hxy : x * y = 0) : ¬ IsDivision A := fun h ↦
  (h.eq_zero_or_eq_zero_of_mul_eq_zero hxy).elim hx hy
