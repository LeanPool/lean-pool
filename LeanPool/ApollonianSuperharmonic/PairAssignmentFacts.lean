/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Init
public import Mathlib.Tactic.TypeStar



/-!
# PairAssignmentFacts

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace PairAssignmentFacts

/-- Distinct elements assigned to a two-element set use both slots. -/
theorem assignment {α : Type*} (a b x y : α) (ha : a = x ∨ a = y)
    (hb : b = x ∨ b = y) (hab : a ≠ b) :
    (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  rcases ha with h1 | h1 <;> rcases hb with h3 | h3
  · exact False.elim (hab (h1.trans h3.symm))
  · exact Or.inl ⟨h1, h3⟩
  · exact Or.inr ⟨h1, h3⟩
  · exact False.elim (hab (h1.trans h3.symm))

/-- Equality of unordered pairs gives one of the two ordered assignments. -/
theorem finsetPair {α : Type*} [DecidableEq α] {a b c d : α}
    (h : ({a, b} : Finset α) = {c, d}) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  have hs : ({a, b} : Set α) = {c, d} := by
    ext x
    have hx := congrArg (fun s : Finset α => x ∈ s) h
    apply Iff.of_eq
    change (x = a ∨ x = b) = (x = c ∨ x = d)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
  exact Set.pair_eq_pair_iff.mp hs

end PairAssignmentFacts
end ApollonianSuperharmonic

end
