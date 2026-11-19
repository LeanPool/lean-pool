/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefreeness and multiplicative equivalences

A candidate for `Mathlib.Algebra.Squarefree.Basic`: a multiplicative equivalence preserves and
reflects squarefreeness (`MulEquiv.squarefree_iff`), as it does irreducibility
(`MulEquiv.irreducible_iff`) and primality (`MulEquiv.prime_iff`).
-/

@[expose] public section

theorem MulEquiv.squarefree_iff {M N F : Type*} [Monoid M] [Monoid N] [EquivLike F M N]
    [MulEquivClass F M N] (f : F) {x : M} : Squarefree (f x) ↔ Squarefree x := by
  simp [Squarefree, (EquivLike.surjective f).forall, ← map_mul, map_dvd_iff]

end
