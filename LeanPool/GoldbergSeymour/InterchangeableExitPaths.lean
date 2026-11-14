/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeExitPath
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorMissingVertexNeighbors

/-!
# Exit paths under interchangeable colors

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A missing-color vertex inside an interchangeable tree forces all exit-path starts to agree. -/
theorem TreeInterchangeable.exitPath_start_eq {V E : Type*} [Finite V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {tree : TreeSequence G e0}
    {sigma : PartialEdgeColoring E k} {c beta : Fin k} {a₁ b₁ a₂ b₂ : V}
    (interchangeable : TreeInterchangeable G tree sigma c beta)
    (proper : IsProperEdgeColoring G sigma) (colorsDistinct : c ≠ beta)
    (x : V) (inside : x ∈ TreeSequenceVertexSet tree)
    (missing : c ∈ MissingColors G sigma x ∨ beta ∈ MissingColors G sigma x)
    (Q₁ : (TwoColorIncidenceGraph G sigma c beta).Walk (Sum.inl a₁) (Sum.inl b₁))
    (Q₂ : (TwoColorIncidenceGraph G sigma c beta).Walk (Sum.inl a₂) (Sum.inl b₂))
    (hQ₁ : TreeExitPath tree sigma c beta a₁ b₁ Q₁)
    (hQ₂ : TreeExitPath tree sigma c beta a₂ b₂ Q₂) : a₁ = a₂ := by
  classical
  by_contra ha
  let graph := TwoColorIncidenceGraph G sigma c beta
  have missingLeaf := TwoColorMissingVertexNeighborsSubsingleton G sigma proper c beta
  have hxLeaf : Set.Subsingleton (graph.neighborSet (Sum.inl x)) :=
    missingLeaf x missing
  have ha₁Leaf : Set.Subsingleton (graph.neighborSet (Sum.inl a₁)) :=
    missingLeaf a₁ hQ₁.2.2.2.2.1
  have ha₂Leaf : Set.Subsingleton (graph.neighborSet (Sum.inl a₂)) :=
    missingLeaf a₂ hQ₂.2.2.2.2.1
  have hpathX : TwoColorPathComponent G sigma c beta (Sum.inl x) :=
    ⟨colorsDistinct, Sum.inl x, rfl, hxLeaf⟩
  have hpath₁ : TwoColorPathComponent G sigma c beta (Sum.inl a₁) :=
    ⟨colorsDistinct, Sum.inl a₁, rfl, ha₁Leaf⟩
  have hpath₂ : TwoColorPathComponent G sigma c beta (Sum.inl a₂) :=
    ⟨colorsDistinct, Sum.inl a₂, rfl, ha₂Leaf⟩
  have hmeetX : ∃ v ∈ TreeSequenceVertexSet tree,
      Sum.inl v ∈ TwoColorComponent G sigma c beta (Sum.inl x) :=
    ⟨x, inside, rfl⟩
  have hmeet₁ : ∃ v ∈ TreeSequenceVertexSet tree,
      Sum.inl v ∈ TwoColorComponent G sigma c beta (Sum.inl a₁) := by
    refine ⟨b₁, hQ₁.2.2.2.1, ?_⟩
    change graph.connectedComponentMk (Sum.inl b₁) =
      graph.connectedComponentMk (Sum.inl a₁)
    exact (SimpleGraph.ConnectedComponent.sound Q₁.reachable).symm
  have hmeet₂ : ∃ v ∈ TreeSequenceVertexSet tree,
      Sum.inl v ∈ TwoColorComponent G sigma c beta (Sum.inl a₂) := by
    refine ⟨b₂, hQ₂.2.2.2.1, ?_⟩
    change graph.connectedComponentMk (Sum.inl b₂) =
      graph.connectedComponentMk (Sum.inl a₂)
    exact (SimpleGraph.ConnectedComponent.sound Q₂.reachable).symm
  have ha₁x : a₁ ≠ x := by
    intro h
    exact hQ₁.2.2.1 (h ▸ (inside))
  have ha₂x : a₂ ≠ x := by
    intro h
    exact hQ₂.2.2.1 (h ▸ (inside))
  have hdistinct :
      TwoColorComponent G sigma c beta (Sum.inl x) ≠
          TwoColorComponent G sigma c beta (Sum.inl a₁) ∨
      TwoColorComponent G sigma c beta (Sum.inl x) ≠
          TwoColorComponent G sigma c beta (Sum.inl a₂) := by
    by_contra hnot
    push Not at hnot
    rcases TwoColorComponent.leaf_eq_or_eq sigma c beta proper
      (Sum.inl x) (Sum.inl a₁) (Sum.inl a₂) hxLeaf ha₁Leaf ha₂Leaf hnot.1 hnot.2 with h | h | h
    · exact ha₁x (Sum.inl.inj h.symm)
    · exact ha₂x (Sum.inl.inj h.symm)
    · exact ha (Sum.inl.inj h)
  rcases hdistinct with hneComp | hneComp
  · exact hneComp (interchangeable (Sum.inl x) (Sum.inl a₁)
      hpathX hpath₁ hmeetX hmeet₁)
  · exact hneComp (interchangeable (Sum.inl x) (Sum.inl a₂)
      hpathX hpath₂ hmeetX hmeet₂)

/-- An outside missing-color component cannot meet an interchangeable tree missing both colors. -/
theorem TreeInterchangeable.outside_missing_component {V E : Type*} [Finite V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {tree : TreeSequence G e0}
    {sigma : PartialEdgeColoring E k} {c d : Fin k}
    (interchangeable : TreeInterchangeable G tree sigma c d)
    (proper : IsProperEdgeColoring G sigma) (colorsDistinct : c ≠ d)
    (firstMissing : c ∈ TreeMissingColors sigma tree)
    (secondMissing : d ∈ TreeMissingColors sigma tree) (w : V)
    (outside : w ∉ TreeSequenceVertexSet tree)
    (missing : c ∈ MissingColors G sigma w ∨ d ∈ MissingColors G sigma w) :
    ∀ v ∈ TreeSequenceVertexSet tree, Sum.inl v ∉ TwoColorComponent G sigma c d (Sum.inl w) := by
  classical
  have pathMissing (v : V) (member : c ∈ MissingColors G sigma v ∨ d ∈ MissingColors G sigma v) :
      TwoColorPathComponent G sigma c d (Sum.inl v) :=
    ⟨colorsDistinct, Sum.inl v, rfl,
      TwoColorMissingVertexNeighborsSubsingleton G sigma proper c d v member⟩
  obtain ⟨u, huA, hcu⟩ := Finset.mem_biUnion.mp firstMissing
  obtain ⟨v, hvA, hdv⟩ := Finset.mem_biUnion.mp secondMissing
  intro z hzA hzC
  have huvC := interchangeable (Sum.inl u) (Sum.inl v)
    (pathMissing u (Or.inl hcu))
    (pathMissing v (Or.inr hdv))
    ⟨u, huA, rfl⟩ ⟨v, hvA, rfl⟩
  have huwC := interchangeable (Sum.inl u) (Sum.inl w)
    (pathMissing u (Or.inl hcu))
    (pathMissing w missing) ⟨u, huA, rfl⟩ ⟨z, hzA, hzC⟩
  have hwC : Sum.inl w ∈ TwoColorComponent G sigma c d (Sum.inl u) := by
    rw [huwC]
    rfl
  have huw : Sum.inl u ≠ (Sum.inl w : Sum V E) := by
    intro he
    exact outside (Sum.inl.inj he ▸ huA)
  have hvw : Sum.inl v ≠ (Sum.inl w : Sum V E) := by
    intro he
    exact outside (Sum.inl.inj he ▸ hvA)
  by_cases huv : u = v
  · subst v
    have hnone : (TwoColorIncidenceGraph G sigma c d).neighborSet (Sum.inl u) = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hz
      cases z with
      | inl z => exact hz
      | inr edge =>
        change Incident G u edge ∧ (sigma edge = some c ∨ sigma edge = some d) at hz
        obtain ⟨hinc, hcolor⟩ := hz
        have hcnot : c ∉ PresentColors G sigma u := by
          simpa [MissingColors] using hcu
        have hdnot : d ∉ PresentColors G sigma u := by
          simpa [MissingColors] using hdv
        rcases hcolor with hcolor | hcolor
        · apply hcnot
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨edge, hinc, hcolor⟩
        · apply hdnot
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨edge, hinc, hcolor⟩
    have hreach : (TwoColorIncidenceGraph G sigma c d).Reachable
        (Sum.inl u) (Sum.inl w) :=
      SimpleGraph.ConnectedComponent.reachable_of_mem_supp _ rfl hwC
    exact SimpleGraph.not_reachable_of_neighborSet_left_eq_empty huw hnone hreach
  · have leafU := TwoColorMissingVertexNeighborsSubsingleton G sigma proper c d u (Or.inl hcu)
    have leafV := TwoColorMissingVertexNeighborsSubsingleton G sigma proper c d v (Or.inr hdv)
    have leafW := TwoColorMissingVertexNeighborsSubsingleton G sigma proper c d w missing
    rcases TwoColorComponent.leaf_eq_or_eq sigma c d proper
      (Sum.inl u) (Sum.inl v) (Sum.inl w) leafU leafV leafW huvC huwC with h | h | h
    · exact huv (Sum.inl.inj h)
    · exact huw h
    · exact hvw h

end GoldbergSeymour

end
