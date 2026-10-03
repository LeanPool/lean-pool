/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Fintype.Basic
import Lean.Elab.Tactic.Omega

/-! # Numerical data for the Häggkvist--Janssen certificate

The data follow page 301 of the original article. Natural subtraction is used
with explicit bounds in the supporting lemmas. The combinatorial certificate
is developed separately from the polynomial and graph-colouring interfaces.
-/

@[expose] public section

namespace LeanPool.ListEdgeColoringComplete

/-- Target total outdegree at an actual edge of the complete graph. -/
def targetDegree (n i j : ℕ) : ℕ :=
  if n - 1 ≤ i + j then n - 1 else n - 2

/-- Rank excluded from the extended star at vertex `i`. -/
def blockedRank (n i : ℕ) : ℕ :=
  if i < n / 2 then n - 2 - i else n - 1 - i + n / 2

theorem targetDegree_lt (n i j : ℕ) (hn : 2 ≤ n) :
    targetDegree n i j < n := by
  unfold targetDegree
  split <;> omega

theorem blockedRank_lt (n i : ℕ) (hn : 2 ≤ n) (hi : i < n) :
    blockedRank n i < n := by
  unfold blockedRank
  split <;> omega

end LeanPool.ListEdgeColoringComplete
