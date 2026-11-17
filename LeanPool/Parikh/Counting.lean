/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import Mathlib.Computability.Language
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
import Mathlib.Algebra.Group.Submonoid.Finsupp

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# From words to semilinear sets

The Parikh map forgets letter order and remembers how often each letter occurs.
Its central law is `counts_append`: concatenating words adds their vectors.

A `Component` describes one linear set by a base and a finite list of periods;
a `Witness` describes a finite union of such sets. The denotations give these
finite descriptions their mathematical meaning. The final lemmas connect them
to Mathlib's `IsLinearSet` and `IsSemilinearSet` in both directions, so later
proofs can use explicit witnesses without replacing Mathlib's notions.

Source: `sec:statement`, `eq:word-add`.
-/
open scoped Pointwise

namespace Parikh

/-- A natural-number coordinate for each terminal letter. -/
abbrev Vector (T : Type*) := T → ℕ

/-- Count occurrences with Mathlib's `List.count`; no order on the alphabet is needed. -/
@[expose] def counts {T : Type*} [DecidableEq T] (w : List T) : Vector T := fun a => w.count a

/-- The exact image of a Mathlib language under terminal counting. -/
@[expose] def image {T : Type*} [DecidableEq T] (L : Language T) : Set (Vector T) := counts '' L

/-- A finite description of one linear set (`sec:statement`).
Start at `base` and add any natural number of copies of each period.
A Lean `List` always has finite length; no separate finiteness proof is needed.
Duplicate and zero periods are allowed, and an empty period list describes
just the base vector. -/
structure Component (T : Type*) where
  /-- Initial count vector of the linear component. -/
  base : Vector T
  /-- Independently repeatable period vectors, retaining duplicates and zero vectors. -/
  periods : List (Vector T)

/-- A finite representation, independent of grammars and trace theory. -/
abbrev Witness (T : Type*) := List (Component T)

/-- The vectors represented by a component.
A coefficient function assigns a natural number to each position in the period
list. Each coefficient is chosen independently and may be zero. Thus membership
means exactly that the vector is the base plus a finite nonnegative combination
of the listed periods. -/
@[expose] def Component.denotation {T : Type*} (c : Component T) : Set (Vector T) :=
  {v | ∃ k : Fin c.periods.length → ℕ,
    v = c.base + ∑ i : Fin c.periods.length, k i • c.periods[i]}

/-- Empty list denotes the empty set; this is an exact union, not an approximation. -/
@[expose] def Witness.denotation {T : Type*} (W : Witness T) : Set (Vector T) :=
  {v | ∃ c ∈ W, v ∈ c.denotation}

/-- Concatenation adds count vectors (`eq:word-add`). -/
theorem counts_append {T : Type*} [DecidableEq T] (u v : List T) :
    counts (u ++ v) = counts u + counts v := by
  funext a
  exact List.count_append

/-- Indexed period sums are exactly the additive closure of the period values.
This reuses Mathlib's finite-range closure theorem, including repeated and zero periods. -/
theorem Component.denotation_eq_vadd_closure {T : Type*} (c : Component T) :
    c.denotation = c.base +ᵥ
      (AddSubmonoid.closure (Set.range c.periods.get) : Set (Vector T)) := by
  ext x
  simp only [Component.denotation, Set.mem_ofPred_eq, Set.mem_vadd_set,
    SetLike.mem_coe, vadd_eq_add, AddSubmonoid.mem_closure_range_iff_of_fintype]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, rfl⟩

/-- Bridge indexed coefficient sums to Mathlib's finitely generated additive closure. -/
theorem component_isLinearSet {T : Type*} (c : Component T) :
    IsLinearSet c.denotation := by
  exact ⟨c.base, Set.range c.periods.get, Set.finite_range _,
    c.denotation_eq_vadd_closure⟩

/-- Every explicit witness denotes a Mathlib semilinear set (`sec:statement`). -/
theorem witness_isSemilinearSet {T : Type*} (W : Witness T) :
    IsSemilinearSet W.denotation := by
  classical
  have h : W.denotation = ⋃ c ∈ W.toFinset, c.denotation := by
    ext v
    simp [Witness.denotation]
  rw [h]
  exact IsSemilinearSet.biUnion_finset fun c _ =>
    (component_isLinearSet c).isSemilinearSet

/-- Mathlib's abstract semilinearity has an exact finite witness as well. -/
theorem exists_witness {T : Type*} (X : Set (Vector T)) (hX : IsSemilinearSet X) :
    ∃ W : Witness T, W.denotation = X := by
  classical
  have linear_witness : ∀ X : Set (Vector T), IsLinearSet X →
      ∃ c : Component T, c.denotation = X := by
    rintro X ⟨b, periods, hperiods, rfl⟩
    refine ⟨⟨b, hperiods.toFinset.toList⟩, ?_⟩
    rw [Component.denotation_eq_vadd_closure]
    have hrange : Set.range hperiods.toFinset.toList.get = periods := by
      ext p
      simp only [Set.mem_range, ← List.mem_iff_get, Finset.mem_toList,
        Set.Finite.mem_toFinset]
    simp only [hrange]
  rcases hX with ⟨S, hS, hlinear, rfl⟩
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    exact ⟨[], by ext v; simp [Witness.denotation]⟩
  | @insert X S hnot hS ih =>
    obtain ⟨c, hc⟩ := linear_witness X (hlinear X (by simp))
    obtain ⟨W, hW⟩ := ih (fun Y hY => hlinear Y (by simp [hY]))
    refine ⟨c :: W, ?_⟩
    have hcons : Witness.denotation (c :: W) = c.denotation ∪ W.denotation := by
      ext v
      simp [Witness.denotation]
    rw [hcons, hc, hW, Set.sUnion_insert]

end Parikh
