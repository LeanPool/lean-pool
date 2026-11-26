/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Positive-length curves below a tangle order need a drawing edge

The geometric trace lemmas use an edge of the original drawing.
In XII (2.1), a positive curve length below the tangle order makes
that order at least two. X (2.3) then excludes an edgeless graph:
three copies of any small side would already cover its edge set.
This separates the geometric argument from the zero-length case.
-/

public section

namespace GraphMinor.GM12

open Set Hypergraph GM10

/-- A tangle of order at least two lives in a hypergraph with an edge.
Apply X (2.3) to three copies of the empty small side. -/
theorem edges_nonempty_of_tangle_order_two
    {α β : Type*} {G : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)}
    (hT : IsTangle G θ T) (hθ : 2 ≤ θ) : G.edgeSet.Nonempty :=
  GM10.IsTangle.edgeSet_nonempty_of_two_le hT hθ

end GraphMinor.GM12
