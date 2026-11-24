/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.Forest
import LeanPool.GraphMinor.GM11.Walks

/-!
# Positions along a graph path

Enumerate the vertices and edges of a walk by their positions in
its two lists. The edge at position `i` joins the vertices at
positions `i` and `i+1`. For a simple walk these enumerations are
injective. They provide the endpoint-preserving isomorphisms used
to draw the replacing paths of the subdivision in XVI (4.2).
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph Surface GM11
universe u v
variable {α : Type u} {β : Type v} {G : Graph α β}

/-- The vertex at a specified position along a walk. -/
def pathWalkVertex {a b : α} (W : GraphWalk G a b) (i : ℕ) (hi : i ≤ W.length) : α :=
  W.support[i]'(by rw [length_support]; omega)

/-- The edge at a specified position along a walk. -/
def pathWalkEdge {a b : α} (W : GraphWalk G a b) (i : ℕ) (hi : i < W.length) : β :=
  W.edges[i]

/-- The first position is the starting vertex. -/
theorem pathWalkVertex_zero {a b : α} (W : GraphWalk G a b) :
    pathWalkVertex W 0 (Nat.zero_le _) = a := by
  cases W <;> rfl

/-- The last position is the final vertex. -/
theorem pathWalkVertex_last {a b : α} (W : GraphWalk G a b) :
    pathWalkVertex W W.length le_rfl = b := by
  induction W with
  | nil _ => rfl
  | cons h W ih =>
    change pathWalkVertex W W.length le_rfl = _
    exact ih

/-- Every edge joins its two consecutive vertex positions. -/
theorem pathWalkEdge_isLink {a b : α} (W : GraphWalk G a b) (i : ℕ) (hi : i < W.length) :
    G.IsLink (pathWalkEdge W i hi) (pathWalkVertex W i (by omega))
      (pathWalkVertex W (i+1) (by omega)) := by
  induction W generalizing i with
  | nil _ => simp only [GraphWalk.length_nil] at hi; omega
  | cons h W ih =>
    cases i with
    | zero =>
      change G.IsLink _ _ (pathWalkVertex W 0 (Nat.zero_le _))
      rw [pathWalkVertex_zero W]
      exact h
    | succ i =>
      have hi' : i < W.length := by simp only [GraphWalk.length_cons] at hi; omega
      exact ih i hi'

/-- Different vertex positions of a simple walk have different values. -/
theorem pathWalkVertex_injective {a b : α} {W : GraphWalk G a b} (hW : W.IsSimple)
    {i j : ℕ} (hi : i ≤ W.length) (hj : j ≤ W.length)
    (he : pathWalkVertex W i hi = pathWalkVertex W j hj) : i=j :=
  hW.getElem_inj_iff.mp he

/-- Different edge positions of a simple walk have different values. -/
theorem pathWalkEdge_injective {a b : α} {W : GraphWalk G a b} (hW : W.IsSimple)
    {i j : ℕ} (hi : i < W.length) (hj : j < W.length)
    (he : pathWalkEdge W i hi = pathWalkEdge W j hj) : i=j :=
  hW.edges_nodup.getElem_inj_iff.mp he

/-- Every position names a vertex in the walk's support. -/
theorem pathWalkVertex_mem_support {a b : α} (W : GraphWalk G a b) (i : ℕ) (hi : i ≤ W.length) :
    pathWalkVertex W i hi ∈ W.support := List.getElem_mem _

/-- Every position names an edge traversed by the walk. -/
theorem pathWalkEdge_mem_edges {a b : α} (W : GraphWalk G a b) (i : ℕ) (hi : i < W.length) :
    pathWalkEdge W i hi ∈ W.edges := List.getElem_mem _

end GraphMinor.GM16
