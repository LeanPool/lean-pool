/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Basic
public import LeanPool.AaronsonAmbainis.DetDefs

/-!
# DetBij / Basic: cube lemmas and the agreement monomial

Elementary facts on `flipSet`, `diffSet`, `antipode`, the agreement set `agSet`, and the
exponent vector `agExp` of the agreement monomial `agMon`.
-/

@[expose] public section

namespace AaronsonAmbainis.DetBij

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The agreement set of `x` and `z` (written `ag(x,z)` in the paper). -/
def agSet (x z : Cube ι) : Finset ι := univ.filter fun i => x i = z i

omit [DecidableEq ι] in
theorem mem_agSet {x z : Cube ι} {i : ι} : i ∈ agSet x z ↔ x i = z i := by
  simp [agSet]

omit [DecidableEq ι] in
theorem mem_diffSet {x z : Cube ι} {i : ι} : i ∈ diffSet x z ↔ x i ≠ z i := by
  simp [diffSet]

omit [Fintype ι] in
theorem flipSet_apply (x : Cube ι) (S : Finset ι) (i : ι) :
    flipSet x S i = if i ∈ S then !(x i) else x i := rfl

omit [Fintype ι] in
theorem flipSet_empty (x : Cube ι) : flipSet x ∅ = x := by
  exact AaronsonAmbainis.flipSet_empty x

/-- A point `w` with `diffSet x w = S` is `flipSet x S`: first half. -/
theorem diffSet_flipSet (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by
  exact AaronsonAmbainis.diffSet_flipSet x S

/-- A point `w` with `diffSet x w = S` is `flipSet x S`: second half. -/
theorem flipSet_diffSet (x w : Cube ι) : flipSet x (diffSet x w) = w := by
  exact AaronsonAmbainis.flipSet_diffSet x w

omit [DecidableEq ι] in
theorem diffSet_eq_empty_iff {x w : Cube ι} : diffSet x w = ∅ ↔ x = w := by
  constructor
  · intro h
    funext i
    by_contra hne
    have hi : i ∈ diffSet x w := mem_diffSet.mpr hne
    rw [h] at hi
    simp at hi
  · rintro rfl
    ext i
    simp [mem_diffSet]

/-- `z` is the antipode of `u` flipped on the agreement set of `u` and `z`. -/
theorem flipSet_antipode_agSet (u z : Cube ι) : flipSet (antipode u) (agSet u z) = z := by
  funext i
  rw [flipSet_apply]
  by_cases h : u i = z i
  · rw [ite_eq_left (mem_agSet.mpr h)]
    simp [antipode, h]
  · rw [ite_eq_right (fun hh => h (mem_agSet.mp hh))]
    revert h
    simp only [antipode]
    cases u i <;> cases z i <;> simp

/-- The exponent vector of `agMon x z`: the indicator of the agreement set. -/
noncomputable def agExp (x z : Cube ι) : ι →₀ ℕ :=
  ∑ i, if x i = z i then Finsupp.single i 1 else 0

omit [DecidableEq ι] in
theorem agExp_apply (x z : Cube ι) (j : ι) : agExp x z j = if x j = z j then 1 else 0 := by
  rw [agExp, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · split_ifs <;> simp
  · intro i _ hij
    split_ifs
    · simp [hij]
    · simp
  · intro h
    exact absurd (Finset.mem_univ j) h

omit [DecidableEq ι] in
/-- `agMon x z` is the monomial with exponent vector `agExp x z` and coefficient `1`. -/
theorem agMon_eq_monomial (x z : Cube ι) :
    agMon x z = monomial (agExp x z) (1 : ℤ) := by
  rw [agExp, monomial_sum_one]
  unfold agMon
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · rfl
  · simp

end AaronsonAmbainis.DetBij
