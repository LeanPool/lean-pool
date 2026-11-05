/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure

/-!
# Hierarchy Counterexample Less

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Lexicographic strict order on the path-number and remaining-tail-length measures. -/
def HierarchyCounterexampleLess (a b : ℕ × ℕ) : Prop :=
 a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

end GoldbergSeymour

end
