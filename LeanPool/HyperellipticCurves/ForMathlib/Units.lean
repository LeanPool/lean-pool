/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs

/-!
# Injectivity from unit differences

A family of ring elements whose pairwise differences are units is injective
(`Function.injective_of_isUnit_sub`). This is the separation hypothesis carried by the node
data of this development: the nodes of a `τ`-datum, of a tuple datum and of a fold
alphabet are all specified by unit differences, while the consumers ask for injectivity.
-/

@[expose] public section

/-- A family whose pairwise differences are units is injective. -/
theorem Function.injective_of_isUnit_sub {ι R : Type*} [Ring R] [Nontrivial R] {a : ι → R}
    (h : ∀ i j, i ≠ j → IsUnit (a i - a j)) : Function.Injective a := fun i j hij ↦ by
  by_contra hne
  exact (h i j hne).ne_zero (by rw [hij, sub_self])

end
