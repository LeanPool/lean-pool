/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.GraphColouringMatching.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Exact edge accounting for finite matching decompositions

The equivalence on individual edges yields an exact count, including palettes
with unused colours. Empty matching classes contribute zero.
-/

@[expose] public section

namespace SimpleGraph.MatchingDecomposition

variable {V C : Type*} {G : SimpleGraph V}

/-- The total number of edges is the sum of the matching-class sizes. -/
theorem card_edges_eq_sum [Finite V] [Fintype C] (D : MatchingDecomposition G C) :
    Nat.card G.edgeSet = ∑ c, Nat.card (D.matching c).edgeSet := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let : ∀ c, Fintype (D.matching c).edgeSet := fun c => Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma] using
    Fintype.card_congr D.edgeEquivSigma

end SimpleGraph.MatchingDecomposition
