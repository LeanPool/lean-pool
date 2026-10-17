/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.Algebra.Ring.Associator

/-!
# The associator

Basic API for the associator `⁅x, y, z⁆ = (x * y) * z - x * (y * z)` on a non-unital,
non-associative ring: additivity in each argument, behaviour under negation and zero.

⚠ **`associator` is mathlib's, not ours.** Mathlib already defines the ring-theoretic associator;
we import it and only add the multilinearity API. Do not redefine it. (If a future mathlib bump
moves or renames it, fix the import — do not introduce a local copy. See overview §0.)

## Main results

* `associator_add_left`, `associator_add_mid`, `associator_add_right` : additivity in each slot.
* `associator_neg_left`, `associator_neg_mid`, `associator_neg_right` : behaviour under negation.
* `associator_zero_left`, `associator_zero_mid`, `associator_zero_right` : vanishing.

## TODO

* The nucleus (`LeftNucleus`, `MiddleNucleus`, `RightNucleus`, `Nucleus`), as associative
  sub-structures. This is **not** decoration: the nucleus is the tool used to prove the hard
  direction of Artin's theorem (`Alternative/Artin.lean`). The centre needs no local definition:
  mathlib's `NonUnitalSubring.center` (and `Subring.center`, `NonUnitalSubalgebra.center`) is
  built on `Set.center`, whose `IsMulCentral` already asks for associativity as well as
  commutativity, and mathlib makes it a `NonUnitalCommRing`.
* Bundle the associator `R`-trilinearly (`associatorₗ`) once a base ring is in play.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, Ch. 13.
* Schafer, *An Introduction to Nonassociative Algebras*, §3.
-/

@[expose] public section

universe u

section AssociatorAdditivity

variable {α : Type u} [NonUnitalNonAssocRing α]

@[simp] theorem associator_add_left (x y z w : α) :
    associator (x + y) z w = associator x z w + associator y z w := by
  simp [associator, add_mul]; abel

@[simp] theorem associator_add_mid (x y z w : α) :
    associator x (y + z) w = associator x y w + associator x z w := by
  simp [associator, add_mul, mul_add]; abel

@[simp] theorem associator_add_right (x y z w : α) :
    associator x y (z + w) = associator x y z + associator x y w := by
  simp [associator, mul_add]; abel

@[simp] theorem associator_neg_left (x y z : α) :
    associator (-x) y z = -associator x y z := by
  simp [associator, neg_mul]; abel

@[simp] theorem associator_neg_mid (x y z : α) :
    associator x (-y) z = -associator x y z := by
  simp [associator, mul_neg, neg_mul]; abel

@[simp] theorem associator_neg_right (x y z : α) :
    associator x y (-z) = -associator x y z := by
  simp [associator, mul_neg]; abel

@[simp] theorem associator_zero_left (y z : α) : associator 0 y z = 0 := by simp [associator]

@[simp] theorem associator_zero_mid (x z : α) : associator x 0 z = 0 := by simp [associator]

@[simp] theorem associator_zero_right (x y : α) : associator x y 0 = 0 := by simp [associator]

/-- The associator vanishes exactly when the two bracketings agree. -/
theorem associator_eq_zero_iff (x y z : α) :
    associator x y z = 0 ↔ (x * y) * z = x * (y * z) := by
  simp [associator, sub_eq_zero]

end AssociatorAdditivity
