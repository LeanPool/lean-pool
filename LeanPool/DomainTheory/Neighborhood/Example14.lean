/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import LeanPool.DomainTheory.Neighborhood.Basic

/-!
# Example 1.4 (Scott 1981, PRG-19, §1)

Scott's third worked example: the **binary tree** of depth 2. Tokens are the
finite binary
sequences of length ≤ 2, `Δ = {Λ, 0, 1, 00, 01, 10, 11}`, and the neighbourhoods
are the
subtrees rooted at each node:

`𝒟 = {Δ, {0,00,01}, {1,10,11}, {00}, {01}, {10}, {11}}`.

We encode the seven tokens as `Fin 7`:

| token | `Λ` | `0` | `1` | `00` | `01` | `10` | `11` |
| ----- | --- | --- | --- | ---- | ---- | ---- | ---- |
| `Fin 7` | `0` | `1` | `2` | `3` | `4` | `5` | `6` |

so `left = {0,00,01} = {1,3,4}`, `right = {1,10,11} = {2,5,6}`, and the four
leaves are the
singletons `{3}, {4}, {5}, {6}`.

We build the neighbourhood system (Definition 1.1) and classify its domain
elements
(Definition 1.6): there are exactly **seven** filters. Unlike Example 1.3's linear
chain, this is
the first example with **branching** — at the partial elements
`elemZero`/`elemOne` one has a
*choice* of how to refine toward one of the four total (leaf) elements.

The finite set calculations use subset and intersection lemmas; footprint
`[propext, Classical.choice, Quot.sound]` — same as Examples 1.2/1.3.
-/

@[expose] public section

namespace Domain.Neighborhood.Example14

/-- Tokens for Example 1.4: the binary tree `Δ = {Λ,0,1,00,01,10,11}`, encoded as
`Fin 7`
(`Λ=0, 0=1, 1=2, 00=3, 01=4, 10=5, 11=6`). -/
abbrev Token := Fin 7

/-- The master neighbourhood `Δ` (the whole tree). -/
def master : Set Token := Set.univ

/-- The left subtree `{0, 00, 01} = {1, 3, 4}`. -/
def left : Set Token := {1, 3, 4}

/-- The right subtree `{1, 10, 11} = {2, 5, 6}`. -/
def right : Set Token := {2, 5, 6}

/-- The leaf `{00} = {3}`. -/
def leaf00 : Set Token := {3}

/-- The leaf `{01} = {4}`. -/
def leaf01 : Set Token := {4}

/-- The leaf `{10} = {5}`. -/
def leaf10 : Set Token := {5}

/-- The leaf `{11} = {6}`. -/
def leaf11 : Set Token := {6}

/-- The seven neighbourhoods of Example 1.4. -/
def memSet : Set (Set Token) := {master, left, right, leaf00, leaf01, leaf10, leaf11}

/-- Membership in the neighbourhood system `𝒟` of Example 1.4. -/
def mem (X : Set Token) : Prop := X ∈ memSet

theorem mem_master : mem master := by
  exact Or.inl rfl
theorem mem_left : mem left := by
  exact Or.inr (Or.inl rfl)
theorem mem_right : mem right := by
  exact Or.inr (Or.inr (Or.inl rfl))
theorem mem_leaf00 : mem leaf00 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem mem_leaf01 : mem leaf01 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
theorem mem_leaf10 : mem leaf10 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
theorem mem_leaf11 : mem leaf11 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))

/-- A neighbourhood of Example 1.4 is exactly one of the seven. -/
theorem mem_iff (X : Set Token) :
    mem X ↔ X = master ∨ X = left ∨ X = right ∨ X = leaf00 ∨ X = leaf01 ∨ X = leaf10 ∨ X =
      leaf11 := by
  constructor
  · intro h
    simpa only [mem, memSet, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_master
    · exact mem_left
    · exact mem_right
    · exact mem_leaf00
    · exact mem_leaf01
    · exact mem_leaf10
    · exact mem_leaf11

theorem not_mem_empty : ¬mem (∅ : Set Token) := by
  intro h
  rcases (mem_iff (∅ : Set Token)).mp h with h | h | h | h | h | h | h
  · have : (0 : Token) ∈ (∅ : Set Token) := by rw [h]; simp only [master, Fin.isValue,
    Set.mem_univ]
    simp only [Fin.isValue, Set.mem_empty_iff_false] at this
  · have : (1 : Token) ∈ (∅ : Set Token) := by rw [h]; simp only [left, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false]
    simp only [Fin.isValue, Set.mem_empty_iff_false] at this
  · have : (2 : Token) ∈ (∅ : Set Token) := by rw [h]; simp only [right, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false]
    simp only [Fin.isValue, Set.mem_empty_iff_false] at this
  · have : (3 : Token) ∈ (∅ : Set Token) := by rw [h]; simp only [leaf00, Fin.isValue,
    Set.mem_singleton_iff]
    simp only [Fin.isValue, Set.mem_empty_iff_false] at this
  · have : (4 : Token) ∈ (∅ : Set Token) := by rw [h]; simp only [leaf01, Fin.isValue,
    Set.mem_singleton_iff]
    simp only [Fin.isValue, Set.mem_empty_iff_false] at this
  · have : (5 : Token) ∈ (∅ : Set Token) := by rw [h]; simp only [leaf10, Fin.isValue,
    Set.mem_singleton_iff]
    simp only [Fin.isValue, Set.mem_empty_iff_false] at this
  · have : (6 : Token) ∈ (∅ : Set Token) := by rw [h]; simp only [leaf11, Fin.isValue,
    Set.mem_singleton_iff]
    simp only [Fin.isValue, Set.mem_empty_iff_false] at this

/-! ### Distinctness of neighbourhoods (only the pairs needed below). -/

private theorem left_ne_master : left ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ left := by rw [h]; simp only [master, Fin.isValue, Set.mem_univ]
  simp only [left, Fin.isValue, Set.mem_insert_iff, Fin.zero_eq_one_iff, Nat.reduceEqDiff,
    Fin.reduceEq, Set.mem_singleton_iff, or_self] at hmem

private theorem right_ne_master : right ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ right := by rw [h]; simp only [master, Fin.isValue, Set.mem_univ]
  simp only [right, Fin.isValue, Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff,
    or_self] at hmem

private theorem leaf00_ne_master : leaf00 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf00 := by rw [h]; simp only [master, Fin.isValue, Set.mem_univ]
  simp only [leaf00, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq] at hmem

private theorem leaf01_ne_master : leaf01 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf01 := by rw [h]; simp only [master, Fin.isValue, Set.mem_univ]
  simp only [leaf01, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq] at hmem

private theorem leaf10_ne_master : leaf10 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf10 := by rw [h]; simp only [master, Fin.isValue, Set.mem_univ]
  simp only [leaf10, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq] at hmem

private theorem leaf11_ne_master : leaf11 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf11 := by rw [h]; simp only [master, Fin.isValue, Set.mem_univ]
  simp only [leaf11, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq] at hmem

private theorem leaf00_ne_left : leaf00 ≠ left := by
  intro h
  have hmem : (1 : Token) ∈ leaf00 := by rw [h]; simp only [left, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false]
  simp only [leaf00, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq] at hmem

private theorem leaf01_ne_left : leaf01 ≠ left := by
  intro h
  have hmem : (1 : Token) ∈ leaf01 := by rw [h]; simp only [left, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false]
  simp only [leaf01, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq] at hmem

private theorem leaf10_ne_right : leaf10 ≠ right := by
  intro h
  have hmem : (2 : Token) ∈ leaf10 := by rw [h]; simp only [right, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false]
  simp only [leaf10, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq] at hmem

private theorem leaf11_ne_right : leaf11 ≠ right := by
  intro h
  have hmem : (2 : Token) ∈ leaf11 := by rw [h]; simp only [right, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false]
  simp only [leaf11, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq] at hmem

/-! ### Nested-subset facts. -/

private theorem leaf00_subset_left : leaf00 ⊆ left := by
  exact Set.singleton_subset_iff.mpr (Or.inr (Or.inl rfl))

private theorem leaf01_subset_left : leaf01 ⊆ left := by
  exact Set.singleton_subset_iff.mpr (Or.inr (Or.inr rfl))

private theorem leaf10_subset_right : leaf10 ⊆ right := by
  exact Set.singleton_subset_iff.mpr (Or.inr (Or.inl rfl))

private theorem leaf11_subset_right : leaf11 ⊆ right := by
  exact Set.singleton_subset_iff.mpr (Or.inr (Or.inr rfl))

/-! ### "Which neighbourhoods contain a given one" (upward classification). -/

private theorem eq_of_master_subset {Y : Set Token} (hY : mem Y) (h : master ⊆ Y) : Y = master := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact absurd (h (show (0 : Token) ∈ master by simp only [master, Fin.isValue,
    Set.mem_univ])) (by simp only [left, Fin.isValue, Set.mem_insert_iff, Fin.zero_eq_one_iff,
      Nat.reduceEqDiff, Fin.reduceEq, Set.mem_singleton_iff, or_self, not_false_eq_true])
  · exact absurd (h (show (0 : Token) ∈ master by simp only [master, Fin.isValue,
    Set.mem_univ])) (by simp only [right, Fin.isValue, Set.mem_insert_iff, Fin.reduceEq,
      Set.mem_singleton_iff, or_self, not_false_eq_true])
  · exact absurd (h (show (0 : Token) ∈ master by simp only [master, Fin.isValue,
    Set.mem_univ])) (by simp only [leaf00, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq,
      not_false_eq_true])
  · exact absurd (h (show (0 : Token) ∈ master by simp only [master, Fin.isValue,
    Set.mem_univ])) (by simp only [leaf01, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq,
      not_false_eq_true])
  · exact absurd (h (show (0 : Token) ∈ master by simp only [master, Fin.isValue,
    Set.mem_univ])) (by simp only [leaf10, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq,
      not_false_eq_true])
  · exact absurd (h (show (0 : Token) ∈ master by simp only [master, Fin.isValue,
    Set.mem_univ])) (by simp only [leaf11, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq,
      not_false_eq_true])

private theorem left_subset_cases {Y : Set Token} (hY : mem Y) (h : left ⊆ Y) :
    Y = master ∨ Y = left := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd (h (show (1 : Token) ∈ left by simp only [left, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false])) (by simp only [
      right, Fin.isValue, Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self,
      not_false_eq_true])
  · exact absurd (h (show (1 : Token) ∈ left by simp only [left, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false])) (by simp only [
      leaf00, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq, not_false_eq_true])
  · exact absurd (h (show (1 : Token) ∈ left by simp only [left, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false])) (by simp only [
      leaf01, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq, not_false_eq_true])
  · exact absurd (h (show (1 : Token) ∈ left by simp only [left, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false])) (by simp only [
      leaf10, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq, not_false_eq_true])
  · exact absurd (h (show (1 : Token) ∈ left by simp only [left, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false])) (by simp only [
      leaf11, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq, not_false_eq_true])

private theorem right_subset_cases {Y : Set Token} (hY : mem Y) (h : right ⊆ Y) :
    Y = master ∨ Y = right := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd (h (show (2 : Token) ∈ right by simp only [right, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false])) (by simp only [
      left, Fin.isValue, Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self,
      not_false_eq_true])
  · exact Or.inr rfl
  · exact absurd (h (show (2 : Token) ∈ right by simp only [right, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false])) (by simp only [
      leaf00, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq, not_false_eq_true])
  · exact absurd (h (show (2 : Token) ∈ right by simp only [right, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false])) (by simp only [
      leaf01, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq, not_false_eq_true])
  · exact absurd (h (show (2 : Token) ∈ right by simp only [right, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false])) (by simp only [
      leaf10, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq, not_false_eq_true])
  · exact absurd (h (show (2 : Token) ∈ right by simp only [right, Fin.isValue,
    Set.mem_insert_iff, Fin.reduceEq, Set.mem_singleton_iff, or_self, or_false])) (by simp only [
      leaf11, Fin.isValue, Set.mem_singleton_iff, Fin.reduceEq, not_false_eq_true])

private theorem leaf00_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf00 ⊆ Y) :
    Y = master ∨ Y = left ∨ Y = leaf00 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (3 : Token) ∈ leaf00 by simp only [leaf00, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [right, Fin.isValue, Set.mem_insert_iff,
      Fin.reduceEq, Set.mem_singleton_iff, or_self, not_false_eq_true])
  · exact Or.inr (Or.inr rfl)
  · exact absurd (h (show (3 : Token) ∈ leaf00 by simp only [leaf00, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [leaf01, Fin.isValue, Set.mem_singleton_iff,
      Fin.reduceEq, not_false_eq_true])
  · exact absurd (h (show (3 : Token) ∈ leaf00 by simp only [leaf00, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [leaf10, Fin.isValue, Set.mem_singleton_iff,
      Fin.reduceEq, not_false_eq_true])
  · exact absurd (h (show (3 : Token) ∈ leaf00 by simp only [leaf00, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [leaf11, Fin.isValue, Set.mem_singleton_iff,
      Fin.reduceEq, not_false_eq_true])

private theorem leaf01_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf01 ⊆ Y) :
    Y = master ∨ Y = left ∨ Y = leaf01 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp only [leaf01, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [right, Fin.isValue, Set.mem_insert_iff,
      Fin.reduceEq, Set.mem_singleton_iff, or_self, not_false_eq_true])
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp only [leaf01, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [leaf00, Fin.isValue, Set.mem_singleton_iff,
      Fin.reduceEq, not_false_eq_true])
  · exact Or.inr (Or.inr rfl)
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp only [leaf01, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [leaf10, Fin.isValue, Set.mem_singleton_iff,
      Fin.reduceEq, not_false_eq_true])
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp only [leaf01, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [leaf11, Fin.isValue, Set.mem_singleton_iff,
      Fin.reduceEq, not_false_eq_true])

private theorem leaf10_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf10 ⊆ Y) :
    Y = master ∨ Y = right ∨ Y = leaf10 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp only [leaf10, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [left, Fin.isValue, Set.mem_insert_iff, Fin.reduceEq,
      Set.mem_singleton_iff, or_self, not_false_eq_true])
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp only [leaf10, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [leaf00, Fin.isValue, Set.mem_singleton_iff,
      Fin.reduceEq, not_false_eq_true])
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp only [leaf10, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [leaf01, Fin.isValue, Set.mem_singleton_iff,
      Fin.reduceEq, not_false_eq_true])
  · exact Or.inr (Or.inr rfl)
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp only [leaf10, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [leaf11, Fin.isValue, Set.mem_singleton_iff,
      Fin.reduceEq, not_false_eq_true])

private theorem leaf11_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf11 ⊆ Y) :
    Y = master ∨ Y = right ∨ Y = leaf11 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd (h (show (6 : Token) ∈ leaf11 by simp only [leaf11, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [left, Fin.isValue, Set.mem_insert_iff, Fin.reduceEq,
      Set.mem_singleton_iff, or_self, not_false_eq_true])
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (6 : Token) ∈ leaf11 by simp only [leaf11, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [leaf00, Fin.isValue, Set.mem_singleton_iff,
      Fin.reduceEq, not_false_eq_true])
  · exact absurd (h (show (6 : Token) ∈ leaf11 by simp only [leaf11, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [leaf01, Fin.isValue, Set.mem_singleton_iff,
      Fin.reduceEq, not_false_eq_true])
  · exact absurd (h (show (6 : Token) ∈ leaf11 by simp only [leaf11, Fin.isValue,
    Set.mem_singleton_iff])) (by simp only [leaf10, Fin.isValue, Set.mem_singleton_iff,
      Fin.reduceEq, not_false_eq_true])
  · exact Or.inr (Or.inr rfl)

/-! ### Intersections. -/

private theorem master_inter (A : Set Token) : master ∩ A = A := by
  rw [master]; exact Set.univ_inter A

private theorem inter_master (A : Set Token) : A ∩ master = A := by
  exact Set.inter_eq_left.mpr fun ⦃a⦄ a_1 => trivial

private theorem left_inter_leaf00 : left ∩ leaf00 = leaf00 := by
  exact Set.inter_singleton_of_mem (Or.inr (Or.inl rfl))
private theorem leaf00_inter_left : leaf00 ∩ left = leaf00 := by
  rw [Set.inter_comm]; exact left_inter_leaf00
private theorem left_inter_leaf01 : left ∩ leaf01 = leaf01 := by
  exact Set.inter_singleton_of_mem (Or.inr (Or.inr rfl))
private theorem leaf01_inter_left : leaf01 ∩ left = leaf01 := by
  rw [Set.inter_comm]; exact left_inter_leaf01
private theorem right_inter_leaf10 : right ∩ leaf10 = leaf10 := by
  exact Set.inter_singleton_of_mem (Or.inr (Or.inl rfl))
private theorem leaf10_inter_right : leaf10 ∩ right = leaf10 := by
  rw [Set.inter_comm]; exact right_inter_leaf10
private theorem right_inter_leaf11 : right ∩ leaf11 = leaf11 := by
  exact Set.inter_singleton_of_mem (Or.inr (Or.inr rfl))
private theorem leaf11_inter_right : leaf11 ∩ right = leaf11 := by
  rw [Set.inter_comm]; exact right_inter_leaf11

private theorem left_inter_right : left ∩ right = (∅ : Set Token) := by
  apply Set.disjoint_iff_inter_eq_empty.mp
  apply Set.disjoint_left.mpr
  intro t hl hr
  rcases hl with rfl | rfl | rfl <;>
    simp only [right, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.reduceEq, or_self] at hr
private theorem right_inter_left : right ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_right
private theorem left_inter_leaf10 : left ∩ leaf10 = (∅ : Set Token) := by
  exact Set.inter_singleton_eq_empty.mpr (by change ¬(((5 : Token) = 1) ∨ 5 = 3 ∨ 5 = 4); decide)
private theorem leaf10_inter_left : leaf10 ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_leaf10
private theorem left_inter_leaf11 : left ∩ leaf11 = (∅ : Set Token) := by
  exact Set.inter_singleton_eq_empty.mpr (by change ¬(((6 : Token) = 1) ∨ 6 = 3 ∨ 6 = 4); decide)
private theorem leaf11_inter_left : leaf11 ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_leaf11
private theorem right_inter_leaf00 : right ∩ leaf00 = (∅ : Set Token) := by
  exact Set.inter_singleton_eq_empty.mpr (by change ¬(((3 : Token) = 2) ∨ 3 = 5 ∨ 3 = 6); decide)
private theorem leaf00_inter_right : leaf00 ∩ right = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact right_inter_leaf00
private theorem right_inter_leaf01 : right ∩ leaf01 = (∅ : Set Token) := by
  exact Set.inter_singleton_eq_empty.mpr (by change ¬(((4 : Token) = 2) ∨ 4 = 5 ∨ 4 = 6); decide)
private theorem leaf01_inter_right : leaf01 ∩ right = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact right_inter_leaf01
private theorem leaf00_inter_leaf01 : leaf00 ∩ leaf01 = (∅ : Set Token) := by
  exact Set.inter_singleton_eq_empty.mpr (by change (4 : Token) ≠ 3; decide)
private theorem leaf01_inter_leaf00 : leaf01 ∩ leaf00 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf00_inter_leaf01
private theorem leaf00_inter_leaf10 : leaf00 ∩ leaf10 = (∅ : Set Token) := by
  exact Set.inter_singleton_eq_empty.mpr (by change (5 : Token) ≠ 3; decide)
private theorem leaf10_inter_leaf00 : leaf10 ∩ leaf00 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf00_inter_leaf10
private theorem leaf00_inter_leaf11 : leaf00 ∩ leaf11 = (∅ : Set Token) := by
  exact Set.inter_singleton_eq_empty.mpr (by change (6 : Token) ≠ 3; decide)
private theorem leaf11_inter_leaf00 : leaf11 ∩ leaf00 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf00_inter_leaf11
private theorem leaf01_inter_leaf10 : leaf01 ∩ leaf10 = (∅ : Set Token) := by
  exact Set.inter_singleton_eq_empty.mpr (by change (5 : Token) ≠ 4; decide)
private theorem leaf10_inter_leaf01 : leaf10 ∩ leaf01 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf01_inter_leaf10
private theorem leaf01_inter_leaf11 : leaf01 ∩ leaf11 = (∅ : Set Token) := by
  exact Set.inter_singleton_eq_empty.mpr (by change (6 : Token) ≠ 4; decide)
private theorem leaf11_inter_leaf01 : leaf11 ∩ leaf01 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf01_inter_leaf11
private theorem leaf10_inter_leaf11 : leaf10 ∩ leaf11 = (∅ : Set Token) := by
  exact Set.inter_singleton_eq_empty.mpr (by change (6 : Token) ≠ 5; decide)
private theorem leaf11_inter_leaf10 : leaf11 ∩ leaf10 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf10_inter_leaf11

/-- Every binary intersection of two neighbourhoods is again a neighbourhood, or
is empty
(the tree's "nested-or-disjoint" property). -/
private theorem inter_eq (X Y : Set Token) (hX : mem X) (hY : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = left ∨ X ∩ Y = right ∨ X ∩ Y = leaf00 ∨
      X ∩ Y = leaf01 ∨ X ∩ Y = leaf10 ∨ X ∩ Y = leaf11 ∨ X ∩ Y = (∅ : Set Token) := by
  rcases (mem_iff X).mp hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (master_inter _)
  · exact Or.inr (Or.inl (master_inter _))
  · exact Or.inr (Or.inr (Or.inl (master_inter _)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (master_inter _))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (master_inter _)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (master_inter _))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (master_inter _)))))))
  · exact Or.inr (Or.inl (inter_master _))
  · exact Or.inr (Or.inl (Set.inter_self _))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (left_inter_right)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (left_inter_leaf00))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (left_inter_leaf01)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (left_inter_leaf10)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (left_inter_leaf11)))))))
  · exact Or.inr (Or.inr (Or.inl (inter_master _)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (right_inter_left)))))))
  · exact Or.inr (Or.inr (Or.inl (Set.inter_self _)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (right_inter_leaf00)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (right_inter_leaf01)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (right_inter_leaf10))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (right_inter_leaf11)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (inter_master _))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (leaf00_inter_left))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf00_inter_right)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Set.inter_self _))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf00_inter_leaf01)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf00_inter_leaf10)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf00_inter_leaf11)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (inter_master _)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (leaf01_inter_left)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf01_inter_right)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf01_inter_leaf00)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Set.inter_self _)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf01_inter_leaf10)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf01_inter_leaf11)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (inter_master _))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf10_inter_left)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (leaf10_inter_right))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf10_inter_leaf00)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf10_inter_leaf01)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Set.inter_self _))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf10_inter_leaf11)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (inter_master _)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf11_inter_left)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (leaf11_inter_right)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf11_inter_leaf00)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf11_inter_leaf01)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (leaf11_inter_leaf10)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Set.inter_self _)))))))

/-- **Example 1.4.** The binary-tree neighbourhood system on `Δ =
{Λ,0,1,00,01,10,11}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := mem
  master := master
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h | h | h | h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_left
    · rw [h]; exact mem_right
    · rw [h]; exact mem_leaf00
    · rw [h]; exact mem_leaf01
    · rw [h]; exact mem_leaf10
    · rw [h]; exact mem_leaf11
    · simp_all

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The bottom element `⊥ = {Δ}` (node `Λ`). -/
def bot : neighborhoodSystem.Element where
  mem X := X = master
  sub h := by rw [h]; exact mem_master
  master_mem := rfl
  inter_mem := by
    simp_all
  up_mem := by
    intro X Y hX hY hXY
    rw [hX] at hXY
    exact eq_of_master_subset hY hXY

/-- The partial element `{Δ, left}` (node `0`): the left branch is decided. -/
def elemZero : neighborhoodSystem.Element where
  mem X := X = master ∨ X = left
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_left
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases left_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr h

/-- The partial element `{Δ, right}` (node `1`): the right branch is decided. -/
def elemOne : neighborhoodSystem.Element where
  mem X := X = master ∨ X = right
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_right
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases right_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr h

/-- The total element `{Δ, left, leaf00}` (leaf `00`). -/
def elem00 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = left ∨ X = leaf00
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_left
    · exact mem_leaf00
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr left_inter_leaf00)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf00_inter_left)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases left_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf00_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

@[simp] theorem elem00_mem_leaf00 : elem00.mem leaf00 := Or.inr (Or.inr rfl)

/-- The total element `{Δ, left, leaf01}` (leaf `01`). -/
def elem01 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = left ∨ X = leaf01
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_left
    · exact mem_leaf01
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr left_inter_leaf01)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf01_inter_left)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases left_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf01_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-- The total element `{Δ, right, leaf10}` (leaf `10`). -/
def elem10 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = right ∨ X = leaf10
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_right
    · exact mem_leaf10
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr right_inter_leaf10)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf10_inter_right)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases right_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf10_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-- The total element `{Δ, right, leaf11}` (leaf `11`). -/
def elem11 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = right ∨ X = leaf11
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_right
    · exact mem_leaf11
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr right_inter_leaf11)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf11_inter_right)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases right_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf11_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-! ### Filter classification: the seven elements. -/

private theorem mem_leaf00_imp (x : neighborhoodSystem.Element) (h : x.mem leaf00) :
    x = elem00 := by
  have hleft : x.mem left := x.up_mem h mem_left leaf00_subset_left
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [right_inter_leaf00] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [leaf01_inter_leaf00] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [leaf10_inter_leaf00] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [leaf11_inter_leaf00] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hleft
    · exact h

private theorem mem_leaf01_imp (x : neighborhoodSystem.Element) (h : x.mem leaf01) :
    x = elem01 := by
  have hleft : x.mem left := x.up_mem h mem_left leaf01_subset_left
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [right_inter_leaf01] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [leaf00_inter_leaf01] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [leaf10_inter_leaf01] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [leaf11_inter_leaf01] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hleft
    · exact h

private theorem mem_leaf10_imp (x : neighborhoodSystem.Element) (h : x.mem leaf10) :
    x = elem10 := by
  have hright : x.mem right := x.up_mem h mem_right leaf10_subset_right
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have hi := x.inter_mem hx h
      rw [left_inter_leaf10] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [leaf00_inter_leaf10] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [leaf01_inter_leaf10] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [leaf11_inter_leaf10] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hright
    · exact h

private theorem mem_leaf11_imp (x : neighborhoodSystem.Element) (h : x.mem leaf11) :
    x = elem11 := by
  have hright : x.mem right := x.up_mem h mem_right leaf11_subset_right
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have hi := x.inter_mem hx h
      rw [left_inter_leaf11] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [leaf00_inter_leaf11] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [leaf01_inter_leaf11] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [leaf10_inter_leaf11] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hright
    · exact h

private theorem mem_left_imp (x : neighborhoodSystem.Element) (hl : x.mem left)
    (h00 : ¬x.mem leaf00) (h01 : ¬x.mem leaf01) : x = elemZero := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have hi := x.inter_mem hl hx
      rw [left_inter_right] at hi
      exact not_mem_empty (x.sub hi)
    · exact absurd hx h00
    · exact absurd hx h01
    · exfalso
      have hi := x.inter_mem hl hx
      rw [left_inter_leaf10] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hl hx
      rw [left_inter_leaf11] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl
    · exact x.master_mem
    · exact hl

private theorem mem_right_imp (x : neighborhoodSystem.Element) (hr : x.mem right)
    (h10 : ¬x.mem leaf10) (h11 : ¬x.mem leaf11) : x = elemOne := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have hi := x.inter_mem hr hx
      rw [right_inter_left] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr rfl
    · exfalso
      have hi := x.inter_mem hr hx
      rw [right_inter_leaf00] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hr hx
      rw [right_inter_leaf01] at hi
      exact not_mem_empty (x.sub hi)
    · exact absurd hx h10
    · exact absurd hx h11
  · intro hx
    rcases hx with rfl | rfl
    · exact x.master_mem
    · exact hr

/-- **Example 1.4 classification.** Every filter is one of the seven: the bottom
`⊥`, the two
branch partials `elemZero`/`elemOne`, or one of the four total leaf elements. -/
theorem element_classification (x : neighborhoodSystem.Element) :
    x = bot ∨ x = elemZero ∨ x = elemOne ∨ x = elem00 ∨ x = elem01 ∨ x = elem10 ∨ x = elem11 := by
  by_cases h00 : x.mem leaf00
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_leaf00_imp x h00))))
  by_cases h01 : x.mem leaf01
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mem_leaf01_imp x h01)))))
  by_cases h10 : x.mem leaf10
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mem_leaf10_imp x h10))))))
  by_cases h11 : x.mem leaf11
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mem_leaf11_imp x h11))))))
  by_cases hl : x.mem left
  · exact Or.inr (Or.inl (mem_left_imp x hl h00 h01))
  by_cases hr : x.mem right
  · exact Or.inr (Or.inr (Or.inl (mem_right_imp x hr h10 h11)))
  apply Or.inl
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact absurd hx hl
    · exact absurd hx hr
    · exact absurd hx h00
    · exact absurd hx h01
    · exact absurd hx h10
    · exact absurd hx h11
  · intro hx
    rw [hx]
    exact x.master_mem

/-! ### The approximation order (Definition 1.8): a branching tree. -/

theorem bot_lt_elemZero : bot < elemZero := by
  constructor
  · intro X hx; rw [hx]; exact Or.inl rfl
  · intro h
    exact left_ne_master (h left (Or.inr rfl))

theorem bot_lt_elemOne : bot < elemOne := by
  constructor
  · intro X hx; rw [hx]; exact Or.inl rfl
  · intro h
    exact right_ne_master (h right (Or.inr rfl))

theorem elemZero_lt_elem00 : elemZero < elem00 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf00 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf00_ne_master h1
    · exact leaf00_ne_left h1

theorem elemZero_lt_elem01 : elemZero < elem01 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf01 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf01_ne_master h1
    · exact leaf01_ne_left h1

theorem elemOne_lt_elem10 : elemOne < elem10 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf10 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf10_ne_master h1
    · exact leaf10_ne_right h1

theorem elemOne_lt_elem11 : elemOne < elem11 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf11 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf11_ne_master h1
    · exact leaf11_ne_right h1

theorem elem00_maximal (x : neighborhoodSystem.Element) (h : elem00 ≤ x) : x = elem00 :=
  mem_leaf00_imp x (h leaf00 (Or.inr (Or.inr rfl)))

theorem elem01_maximal (x : neighborhoodSystem.Element) (h : elem01 ≤ x) : x = elem01 :=
  mem_leaf01_imp x (h leaf01 (Or.inr (Or.inr rfl)))

theorem elem10_maximal (x : neighborhoodSystem.Element) (h : elem10 ≤ x) : x = elem10 :=
  mem_leaf10_imp x (h leaf10 (Or.inr (Or.inr rfl)))

theorem elem11_maximal (x : neighborhoodSystem.Element) (h : elem11 ≤ x) : x = elem11 :=
  mem_leaf11_imp x (h leaf11 (Or.inr (Or.inr rfl)))

end neighborhoodSystem

end Domain.Neighborhood.Example14
