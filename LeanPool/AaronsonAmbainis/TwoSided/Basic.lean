/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Data.Fintype.BigOperators
public import LeanPool.AaronsonAmbainis.AllPairsDefs

/-!
# Basic lemmas on `flipSet`, `antipode`, `diffSet`, `zone`
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

section NoFintype

variable {ι : Type*} [DecidableEq ι]

lemma flipSet_apply (x : Cube ι) (S : Finset ι) (i : ι) :
    flipSet x S i = if i ∈ S then !(x i) else x i := rfl

end NoFintype

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma mem_diffSet {x y : Cube ι} {i : ι} : i ∈ diffSet x y ↔ x i ≠ y i := by
  simp [diffSet]

lemma mem_zone {g : Cube ι → Bool} {u : Cube ι} :
    u ∈ zone g ↔ g u = true ∧ g (antipode u) = false := by
  simp [zone]

end AaronsonAmbainis
