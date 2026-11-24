/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

module

public import LeanPool.GraphMinor.GM20.Assembled

/-!
# The Robertson–Seymour graph minor theorem

Source: doi:10.1016/j.jctb.2004.08.001, url:https://github.com/mahdi-jfri/GraphMinor/tree/89c19b2fd07130fe6fc0fb7df2743ad99558c939
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
Status: verified
Main declarations: `GraphMinor.graph_minor_theorem`
Tags: graph-theory, graph-minors, multigraphs, well-quasi-ordering
MSC: 05C83, 05C10
-/

/-!
This is the dependency closure of the graph minor theorem from the Lean
formalization of the Robertson–Seymour series by MohammadTaghi Hajiaghayi
and Mahdi JafariRaviz. Graphs are Mathlib multigraphs and may have loops and
parallel edges. The supporting development includes drawings on surfaces,
surface classification, tangles and well-quasi-ordering.
-/

public section

namespace GraphMinor

open Graph

/-- In every infinite sequence of finite multigraphs, some earlier graph is
isomorphic to a minor of a later graph. -/
theorem graph_minor_theorem {α β : Type*} (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) :=
  GM20.graph_minor_theorem_assembled G hV hE

end GraphMinor
