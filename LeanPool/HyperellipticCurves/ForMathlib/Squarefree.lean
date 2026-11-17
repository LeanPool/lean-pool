/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefreeness transports along multiplicative equivalences

`MulEquiv.squarefree_iff`: an element is squarefree if and only if its image under a
multiplicative equivalence is, with `Squarefree.map` the direction used in practice
(Mathlib-bound).
-/

@[expose] public section

/-- Squarefreeness is invariant under multiplicative equivalences. -/
theorem MulEquiv.squarefree_iff {M N F : Type*} [Monoid M] [Monoid N] [EquivLike F M N]
    [MulEquivClass F M N] (f : F) {x : M} : Squarefree (f x) ↔ Squarefree x := by
  simp [Squarefree, (EquivLike.surjective f).forall, ← map_mul, map_dvd_iff, -isUnit_map_iff]

alias ⟨_, Squarefree.map⟩ := MulEquiv.squarefree_iff

end
