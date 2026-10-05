/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.PathFour
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.VecNotation

/-!
# Native induced-path interface

The local edge/nonedge predicate is equivalent to exclusion of Mathlib's
`pathGraph 4` by `IsIndContained`. This connects the structural classes to
native induced graph embeddings without a parallel notion of containment.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The local `P₄` exclusion predicate excludes native induced path embeddings. -/
theorem IsP4Free.not_pathGraph_four_isIndContained (h : G.IsP4Free) :
    ¬(pathGraph 4).IsIndContained G := by
  rintro ⟨f⟩
  apply h (f 0) (f 1) (f 2) (f 3)
  · exact f.map_adj_iff.mpr (by simp [pathGraph_adj])
  · exact f.map_adj_iff.mpr (by simp [pathGraph_adj])
  · exact f.map_adj_iff.mpr (by simp [pathGraph_adj])
  · intro he
    simpa [pathGraph_adj] using f.map_adj_iff.mp he
  · intro he
    simpa [pathGraph_adj] using f.map_adj_iff.mp he
  · intro he
    simpa [pathGraph_adj] using f.map_adj_iff.mp he

/-- Four vertices satisfying the path edges and nonedges give a native induced embedding. -/
theorem pathGraph_four_isIndContained_of_adj {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hac : ¬G.Adj a c) (had : ¬G.Adj a d) (hbd : ¬G.Adj b d) :
    (pathGraph 4).IsIndContained G := by
  have habNe := hab.ne
  have hbcNe := hbc.ne
  have hcdNe := hcd.ne
  have hacNe : a ≠ c := by
    rintro rfl
    exact had hcd
  have hadNe : a ≠ d := by
    rintro rfl
    exact hbd hab.symm
  have hbdNe : b ≠ d := by
    rintro rfl
    exact had hab
  let f : Fin 4 → V := ![a, b, c, d]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  refine ⟨⟨⟨f, hf⟩, ?_⟩⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [f, pathGraph_adj, hab, hbc, hcd, hac, had, hbd, G.adj_comm]

/-- Local path exclusion and native induced-path exclusion are equivalent, without finiteness. -/
theorem isP4Free_iff_not_pathGraph_four_isIndContained :
    G.IsP4Free ↔ ¬(pathGraph 4).IsIndContained G := by
  refine ⟨IsP4Free.not_pathGraph_four_isIndContained, ?_⟩
  intro h a b c d hab hbc hcd hac had hbd
  exact h (pathGraph_four_isIndContained_of_adj hab hbc hcd hac had hbd)

end SimpleGraph
