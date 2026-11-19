/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess

/-!
# Lexicographic comparison of hierarchy measures

Arithmetic facts extracted from the credited Trellis change-lemma proofs at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12, independent of hierarchy certificates.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A nonincreasing first component and strictly decreasing second component
give a strict lexicographic decrease. -/
theorem HierarchyCounterexampleLess.of_le_of_lt {a b c d : ℕ}
    (hab : a ≤ b) (hcd : c < d) : HierarchyCounterexampleLess (a, c) (b, d) := by
  rcases Nat.lt_or_eq_of_le hab with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hcd⟩

end GoldbergSeymour

end
