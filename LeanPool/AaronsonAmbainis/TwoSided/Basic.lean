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

lemma flipSet_empty (x : Cube ι) : flipSet x ∅ = x := by
  funext i
  simp [flipSet]

lemma flipSet_flipSet_self (x : Cube ι) (S : Finset ι) : flipSet (flipSet x S) S = x := by
  funext i
  by_cases h : i ∈ S <;> simp [flipSet, h]

end NoFintype

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma antipode_eq_flipSet_univ (x : Cube ι) : antipode x = flipSet x univ := by
  funext i
  simp [flipSet, antipode]

lemma diffSet_flipSet (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by
  ext i
  by_cases h : i ∈ S <;> simp [diffSet, flipSet, h]

lemma flipSet_diffSet (x y : Cube ι) : flipSet x (diffSet x y) = y := by
  funext i
  by_cases h : x i = y i
  · simp [flipSet, diffSet, h]
  · have h' : (!(x i)) = y i := by
      cases hx : x i <;> cases hy : y i <;> simp_all
    simp [flipSet, diffSet, h, h']

omit [DecidableEq ι] in
lemma mem_diffSet {x y : Cube ι} {i : ι} : i ∈ diffSet x y ↔ x i ≠ y i := by
  simp [diffSet]

lemma mem_zone {g : Cube ι → Bool} {u : Cube ι} :
    u ∈ zone g ↔ g u = true ∧ g (antipode u) = false := by
  simp [zone]

lemma card_cube : Fintype.card (Cube ι) = 2 ^ Fintype.card ι := by
  simp [Cube]

end AaronsonAmbainis
