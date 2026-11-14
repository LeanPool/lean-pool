/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.Finiteness.Attr

/-!
# Preamble

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A natural number above one strictly bounds its truncated predecessor. -/
theorem positivePrefixPredecessorBound (n : ℕ) (hn : 1 < n) : n - 1 < n :=
  Nat.sub_lt (lt_trans Nat.zero_lt_one hn) Nat.zero_lt_one

/-- A predecessor bound is preserved after adding the same offset. -/
theorem positivePrefixPrefixBound (n m offset : ℕ) (h : m = n - 1) :
    m + offset ≤ n + offset :=
  Nat.add_le_add_right (le_trans (le_of_eq h) (Nat.sub_le n 1)) offset

end GoldbergSeymour

end
