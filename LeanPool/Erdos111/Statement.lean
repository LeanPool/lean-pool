/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Statement of Erdős Problem 111: bipartizing finite subgraphs of uncountably chromatic graphs

These are the definitions from the upstream project's Mathlib-only `Challenge.lean`.
The source and upstream comparison records are linked in the project card.
-/

@[expose] public section

universe u

namespace Erdos111

/-- The least number of edges whose deletion leaves the subgraph `H` bipartite, for `H`
with finitely many vertices (the only case used below). -/
noncomputable def bipartizationNumber {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) : ℕ :=
  sInf {k : ℕ | ∃ D ⊆ H.edgeSet, D.ncard = k ∧ (H.deleteEdges D).coe.IsBipartite}

/-- `h G n` is the least bound such that every subgraph of `G` on `n` vertices can be
made bipartite by deleting at most `h G n` edges. -/
noncomputable def h {V : Type*} (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ H : G.Subgraph, H.verts.Finite ∧ H.verts.ncard = n ∧
    bipartizationNumber H = k}

/-- The chromatic number of `G` as a cardinal: the least cardinality of a set of colors
that properly colors `G`. -/
noncomputable def chromaticCardinal {V : Type u} (G : SimpleGraph V) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ α : Type u, Cardinal.mk α = κ ∧ Nonempty (G.Coloring α)}

end Erdos111
