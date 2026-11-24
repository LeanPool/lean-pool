/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10d
public import LeanPool.GraphMinor.GM20.Section10l
public import LeanPool.GraphMinor.GM20.Section8b
public import LeanPool.GraphMinor.Surface.Classification
public import LeanPool.GraphMinor.Surface.PushOff

import LeanPool.GraphMinor.GM17.Bridge

import LeanPool.GraphMinor.GM19.Main

/-!
# Graph Minors XX: the graph minor theorem from the cited results

`GM20.graph_minor_theorem_of_cited` derives the graph minor theorem from the cited results.
-/

@[expose] public section

namespace GraphMinor.GM20

open Graph

/-- The graph minor theorem (Graph Minors XX, Section 10, page 355: "As a corollary, we deduce the
following form of Wagner’s conjecture for directed graphs (which immediately implies the standard
form of the conjecture for undirected graphs).") using the proved XVII and XIX results. -/
theorem graph_minor_theorem_of_cited
    {α β : Type*} (G : ℕ → Graph α β) (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) :=
  wagner_conjecture_undirected_proof G hV hE

end GraphMinor.GM20
