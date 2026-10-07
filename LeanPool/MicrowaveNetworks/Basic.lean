/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini, Lean Pool contributors
-/
module

public import Mathlib.Data.Fin.Basic

/-!
# Disjoint ports in a parallel microwave network

Common finite-index facts used by both synthesis models. Adapted from
formalizing-analog-computing at commit a89c1e9263658c20a29046f9ed1a8eeb867dd537.
-/

public section

namespace MiLAC

/-- The first and second blocks of a parallel network have disjoint ports. -/
@[simp] lemma castAdd_ne_natAdd {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n j :=
  Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n j.val)))

/-- Disjointness of parallel ports with the two blocks interchanged. -/
@[simp] lemma natAdd_ne_castAdd {n m : ℕ} (i : Fin m) (j : Fin n) :
    Fin.natAdd n i ≠ Fin.castAdd m j :=
  (castAdd_ne_natAdd j i).symm

end MiLAC
