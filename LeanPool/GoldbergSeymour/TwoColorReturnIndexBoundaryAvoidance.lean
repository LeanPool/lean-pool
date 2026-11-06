/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Boundary edges after a maximal return index

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- A maximal return before a block vertex cannot enter either orientation of a boundary pair. -/
theorem TwoColorReturnIndexBoundaryAvoidance {V E : Type*} {G : LooplessMultigraph V E}
    {k : ℕ} {phi : PartialEdgeColoring E k} {a b : Fin k} {start finish : V ⊕ E}
    (walk : (TwoColorIncidenceGraph G phi a b).Walk start finish) (path : walk.IsPath)
    {leftEdge middleEdge rightEdge : E} {firstOutside secondOutside rightInside blockVertex : V}
    {remainder : Finset V}
    {i0 i1 i2 i3 i4 turn lastReturn query : Fin (walk.length + 1)}
    (step01 : i1.val = i0.val + 1) (step12 : i2.val = i1.val + 1)
    (step23 : i3.val = i2.val + 1) (step34 : i4.val = i3.val + 1)
    (queryStep : query.val = lastReturn.val + 1) (queryBefore : query.val < turn.val)
    (turnNode : walk.getVert turn.val = Sum.inl blockVertex)
    (leftNode : walk.getVert i0.val = Sum.inr leftEdge)
    (firstOutsideNode : walk.getVert i1.val = Sum.inl firstOutside)
    (middleNode : walk.getVert i2.val = Sum.inr middleEdge)
    (secondOutsideNode : walk.getVert i3.val = Sum.inl secondOutside)
    (rightNode : walk.getVert i4.val = Sum.inr rightEdge)
    (firstOutsideNe : firstOutside ≠ blockVertex) (secondOutsideNe : secondOutside ≠ blockVertex)
    (rightEnds : G.ends rightEdge = s(rightInside, secondOutside))
    (insideMember : rightInside ∈ remainder) (blockNotRemainder : blockVertex ∉ remainder)
    (maximalReturn : ∀ index : Fin (walk.length + 1), index.val < turn.val →
      (∃ vertex ∈ remainder, walk.getVert index.val = Sum.inl vertex) →
        index.val ≤ lastReturn.val) :
    walk.getVert query.val ≠ Sum.inr leftEdge := by
  classical
  intro queryNode
  have bounded (index : Fin (walk.length + 1)) : index.val ≤ walk.length :=
    Nat.le_of_lt_succ index.isLt
  have queryEq : query.val = i0.val :=
    path.getVert_injOn (by simpa using bounded query) (by simpa using bounded i0)
      (queryNode.trans leftNode.symm)
  have turnNeFirst : turn.val ≠ i1.val := by
    intro same
    apply firstOutsideNe
    apply Sum.inl.inj
    rw [← firstOutsideNode, ← same, turnNode]
  have turnNeMiddle : turn.val ≠ i2.val := by
    intro same
    have impossible : (Sum.inl blockVertex : V ⊕ E) = Sum.inr middleEdge := by
      rw [← turnNode, same, middleNode]
    simp at impossible
  have turnNeSecond : turn.val ≠ i3.val := by
    intro same
    apply secondOutsideNe
    apply Sum.inl.inj
    rw [← secondOutsideNode, ← same, turnNode]
  have turnNeRight : turn.val ≠ i4.val := by
    intro same
    have impossible : (Sum.inl blockVertex : V ⊕ E) = Sum.inr rightEdge := by
      rw [← turnNode, same, rightNode]
    simp at impossible
  have rightBefore : i4.val < turn.val := by omega
  let next : Fin (walk.length + 1) := ⟨i4.val + 1, by have := turn.isLt; omega⟩
  have adjacency : (TwoColorIncidenceGraph G phi a b).Adj
      (Sum.inr rightEdge) (walk.getVert next.val) := by
    simpa only [next, rightNode] using walk.adj_getVert_succ (i := i4.val) (by omega)
  have returnNode : walk.getVert next.val = Sum.inl rightInside := by
    cases node : walk.getVert next.val with
    | inr edge =>
      rw [node] at adjacency
      exact False.elim adjacency
    | inl vertex =>
      rw [node] at adjacency
      have incident : Incident G vertex rightEdge := adjacency.1
      have endpoints : vertex = rightInside ∨ vertex = secondOutside := by
        simpa [Incident, rightEnds] using incident
      rcases endpoints with endpoint | endpoint
      · simp [endpoint]
      · have repeated : walk.getVert next.val = walk.getVert i3.val := by
          rw [node, endpoint, secondOutsideNode]
        have indices := path.getVert_injOn
          (by simpa using bounded next) (by simpa using bounded i3) repeated
        dsimp [next] at indices
        omega
  have nextBefore : next.val < turn.val := by
    have nextLe : next.val ≤ turn.val := by dsimp [next]; omega
    have nextNe : next.val ≠ turn.val := by
      intro same
      have insideEq : rightInside = blockVertex := by
        apply Sum.inl.inj
        rw [← returnNode, same, turnNode]
      exact blockNotRemainder (insideEq ▸ insideMember)
    omega
  have bound := maximalReturn next nextBefore ⟨rightInside, insideMember, returnNode⟩
  dsimp [next] at bound
  omega

/-- An edge after a different outside vertex cannot immediately follow the recorded return. -/
theorem ReturnIndexAvoidsOutsideEdge {V E : Type*} {graph : SimpleGraph (V ⊕ E)}
    {start finish : V ⊕ E} (walk : graph.Walk start finish) (path : walk.IsPath)
    {edge : E} {inside outside : V}
    {lastReturn query outsideIndex edgeIndex : Fin (walk.length + 1)}
    (queryStep : query.val = lastReturn.val + 1)
    (edgeStep : edgeIndex.val = outsideIndex.val + 1)
    (edgeNode : walk.getVert edgeIndex.val = Sum.inr edge)
    (outsideNode : walk.getVert outsideIndex.val = Sum.inl outside)
    (returnNode : walk.getVert lastReturn.val = Sum.inl inside) (different : inside ≠ outside) :
    walk.getVert query.val ≠ Sum.inr edge := by
  intro queryNode
  have indices : query.val = edgeIndex.val :=
    path.getVert_injOn (Nat.le_of_lt_succ query.isLt) (Nat.le_of_lt_succ edgeIndex.isLt)
      (queryNode.trans edgeNode.symm)
  have previous : lastReturn.val = outsideIndex.val := by omega
  apply different
  apply Sum.inl.inj
  rw [← returnNode, previous, outsideNode]

end GoldbergSeymour

end
