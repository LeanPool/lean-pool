/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Data.Fintype.Pi
public import LeanPool.AaronsonAmbainis.DetDefs

/-!
# DetLow: basic definitions

`Up g j` is the set of ones `x` of `g` with `x j = true` whose `j`-neighbour is also a one
(the upper endpoints of the `j`-edges inside the ones of `g`); its cardinality is the number
`e_j` of Section 3.3 of the paper. (With the identification `true ↦ -1` of `Defs.lean`, the set
`Up_j` of the paper consists of the other endpoints of the same edges; it is `Dn g j` of
`Count.lean`, and it has the same cardinality.)
-/

@[expose] public section

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The upper endpoints of the `j`-edges inside the ones of `g`. -/
def Up (g : Cube ι → Bool) (j : ι) : Finset (Ones g) :=
  univ.filter fun x => x.1 j = true ∧ g (flipSet x.1 {j}) = true

theorem mem_Up {g : Cube ι → Bool} {j : ι} {x : Ones g} :
    x ∈ Up g j ↔ x.1 j = true ∧ g (flipSet x.1 {j}) = true := by
  simp [Up]

omit [Fintype ι] in
@[simp] theorem flipSet_singleton_self (x : Cube ι) (j : ι) :
    flipSet x {j} j = !(x j) := by
  simp [flipSet]

omit [Fintype ι] in
theorem flipSet_singleton_of_ne (x : Cube ι) {i j : ι} (h : i ≠ j) :
    flipSet x {j} i = x i := by
  simp [flipSet, h]

omit [Fintype ι] in
@[simp] theorem flipSet_flipSet_singleton (x : Cube ι) (j : ι) :
    flipSet (flipSet x {j}) {j} = x := by
  funext i
  by_cases h : i = j
  · subst h; simp [flipSet]
  · simp [flipSet, h]

end DetLow
end AaronsonAmbainis
