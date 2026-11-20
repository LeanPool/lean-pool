/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

import Mathlib.Data.Set.Finite.List
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Nat.Basic

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Trees over `{⊥, f}` as sets of constructor positions

Without `⊤`, a tree over `{⊥, f}` is determined by the set of paths labeled `f`, a prefix-closed
set of words; every other path of its domain is a `⊥` leaf. In this representation the covariant
subtype order is inclusion, `⊥` is the empty set and the constructor adds the empty word. Regular
trees are the sets with finitely many residuals, and finite trees the finite sets.

## Main declarations

- `PrefixSet`: prefix-closed sets of constructor positions, ordered by inclusion.
- `PrefixSet.bot`, `PrefixSet.node`, `PrefixSet.residual`: the tree `⊥`, the constructor and
  residuals.
- `PrefixSet.univ`, `PrefixSet.complete`: the tree all of whose paths are constructor
  positions, and the complete tree of depth `d`.
- `IsRegularTree`, `IsFiniteTree`: regular and finite trees.
- `isRegularTree_bot`, `isRegularTree_node`, `isFiniteTree_bot`, `isFiniteTree_node`: both
  classes are closed under the constructors.
- `exists_le_complete`: finitely many finite trees lie below a common complete tree.
-/

@[expose] public section


namespace DeciSigma1.Semantics

variable {n : ℕ}

/-- A tree over `{⊥, f}`, given by the set `carrier` of its constructor positions; the set is closed
under prefixes. -/
@[ext] structure PrefixSet (n : ℕ) where
  /-- Paths forming the prefix-closed set. -/
  carrier : Set (List (Fin n))
  prefix_closed : ∀ u v, u ++ v ∈ carrier → u ∈ carrier

namespace PrefixSet

/-- The tree `⊥`, with no constructor position. -/
def bot : PrefixSet n := ⟨∅, by simp⟩

/-- The tree `f(a 0, …, a (n - 1))`. -/
def node (a : Fin n → PrefixSet n) : PrefixSet n where
  carrier := {w | match w with
    | [] => True
    | i :: v => v ∈ (a i).carrier}
  prefix_closed := by
    intro u v h
    cases u with
    | nil => trivial
    | cons i u => exact (a i).prefix_closed u v h

instance : PartialOrder (PrefixSet n) where
  le t u := t.carrier ⊆ u.carrier
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h₁ h₂ := PrefixSet.ext (Set.Subset.antisymm h₁ h₂)

@[simp] theorem mem_bot (w : List (Fin n)) : w ∉ bot.carrier := by simp [bot]
@[simp] theorem nil_mem_node (a : Fin n → PrefixSet n) : [] ∈ (node a).carrier := trivial
@[simp] theorem cons_mem_node (a : Fin n → PrefixSet n) (i : Fin n)
    (w : List (Fin n)) : i :: w ∈ (node a).carrier ↔ w ∈ (a i).carrier := Iff.rfl

@[simp] theorem node_le_node (a b : Fin n → PrefixSet n) :
    node a ≤ node b ↔ ∀ i, a i ≤ b i := by
  constructor
  · intro h i w hw
    exact h (show i :: w ∈ (node a).carrier from hw)
  · intro h w hw
    cases w with
    | nil => trivial
    | cons i w => exact h i hw

theorem not_node_le_bot (a : Fin n → PrefixSet n) : ¬ node a ≤ bot := by
  intro h
  exact mem_bot [] (h (nil_mem_node a))

/-- The residual of `t` at the word `w`: the positions `v` with `w ++ v` in `t`. It is the subtree
at `w` when `w` is a constructor position or a leaf, and empty otherwise. -/
def residual (t : PrefixSet n) (w : List (Fin n)) : PrefixSet n where
  carrier := {v | w ++ v ∈ t.carrier}
  prefix_closed := by
    intro u v h
    exact t.prefix_closed (w ++ u) v (by simpa [List.append_assoc] using h)

/-- The `i`-th child of a tree. -/
def subtree (t : PrefixSet n) (i : Fin n) : PrefixSet n := t.residual [i]

/-- The tree all of whose paths are constructor positions. -/
def univ : PrefixSet n := ⟨Set.univ, fun _ _ _ => trivial⟩

theorem le_univ (P : PrefixSet n) : P ≤ univ := Set.subset_univ _

/-- The tree `univ` is the fixed point `f(univ, …, univ)`. -/
@[simp] theorem node_univ : (node fun _ => univ : PrefixSet n) = univ :=
  PrefixSet.ext (Set.ext fun π => by cases π <;> simp [univ])

@[simp] theorem mem_univ (w : List (Fin n)) : w ∈ (univ : PrefixSet n).carrier := trivial

/-- The complete tree of depth `d`: the paths of length less than `d` are constructor
positions, and the paths of length `d` are `⊥` leaves. -/
def complete (d : ℕ) : PrefixSet n where
  carrier := {w | w.length < d}
  prefix_closed u v h := lt_of_le_of_lt (by simp) (show (u ++ v).length < d from h)

/-- The complete tree of depth `d` lies below `f` applied to copies of itself, which is the
complete tree of depth `d + 1`. -/
theorem complete_le_node (d : ℕ) : complete d ≤ node fun _ => (complete d : PrefixSet n) := by
  intro w hw
  cases w with
  | nil => trivial
  | cons i w => exact lt_trans (Nat.lt_succ_self _) hw

end PrefixSet

/-- A regular tree: finitely many residuals. -/
def IsRegularTree (t : PrefixSet n) : Prop :=
  (Set.range fun w => (t.residual w).carrier).Finite

/-- The tree `⊥` is regular. -/
theorem isRegularTree_bot : IsRegularTree (PrefixSet.bot : PrefixSet n) := by
  apply (Set.finite_singleton (∅ : Set (List (Fin n)))).subset
  rintro _ ⟨w, rfl⟩
  simp [PrefixSet.residual, PrefixSet.bot]

/-- A constructor applied to regular trees gives a regular tree. -/
theorem isRegularTree_node (a : Fin n → PrefixSet n) (ha : ∀ i, IsRegularTree (a i)) :
    IsRegularTree (PrefixSet.node a) := by
  apply ((Set.finite_singleton (PrefixSet.node a).carrier).union (Set.finite_iUnion ha)).subset
  rintro _ ⟨w, rfl⟩
  cases w with
  | nil => exact Or.inl (by simp [PrefixSet.residual])
  | cons i w => exact Or.inr (Set.mem_iUnion.mpr ⟨i, w, rfl⟩)

/-- The tree `PrefixSet.univ` is regular. -/
theorem isRegularTree_univ : IsRegularTree (PrefixSet.univ : PrefixSet n) := by
  apply (Set.finite_singleton (Set.univ : Set (List (Fin n)))).subset
  rintro _ ⟨w, rfl⟩
  simp [PrefixSet.residual, PrefixSet.univ]

/-- A finite tree: finitely many constructor positions. -/
def IsFiniteTree (t : PrefixSet n) : Prop := t.carrier.Finite

/-- The tree `⊥` is finite. -/
theorem isFiniteTree_bot : IsFiniteTree (PrefixSet.bot : PrefixSet n) := Set.finite_empty

/-- A constructor applied to finite trees gives a finite tree. -/
theorem isFiniteTree_node (a : Fin n → PrefixSet n) (ha : ∀ i, IsFiniteTree (a i)) :
    IsFiniteTree (PrefixSet.node a) := by
  apply ((Set.finite_singleton []).union
    (Set.finite_iUnion fun i => (ha i).image (List.cons i))).subset
  intro w hw
  cases w with
  | nil => exact Or.inl rfl
  | cons i w => exact Or.inr (Set.mem_iUnion.mpr ⟨i, w, hw, rfl⟩)

/-- The complete tree of depth `d` is finite. -/
theorem isFiniteTree_complete (d : ℕ) : IsFiniteTree (PrefixSet.complete d : PrefixSet n) :=
  List.finite_length_lt (Fin n) d

/-- Finitely many finite trees lie below a common complete tree. -/
theorem exists_le_complete {ι : Type*} [Finite ι] {t : ι → PrefixSet n}
    (ht : ∀ i, IsFiniteTree (t i)) : ∃ d, ∀ i, t i ≤ PrefixSet.complete d := by
  obtain ⟨d, hd⟩ := ((Set.finite_iUnion ht).image List.length).bddAbove
  exact ⟨d + 1, fun i w hw =>
    Nat.lt_succ_of_le (hd ⟨w, Set.mem_iUnion.mpr ⟨i, hw⟩, rfl⟩)⟩

end DeciSigma1.Semantics
