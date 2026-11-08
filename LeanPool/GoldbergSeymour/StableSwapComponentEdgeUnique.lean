/-
Copyright (c) 2026 Wesley Pegden and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.KempeOrientation
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapPresentColors
public import LeanPool.GoldbergSeymour.TwoColorMissingVertexNeighbors

/-!
# Unique incident edges after a stable component swap

Shared from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 and generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- If a swapped component meets a tree only at its root, its incident edge is unique. -/
theorem StableColoring.componentIncidentEdgeUniqueOfSwap {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (tree : TreeSequence G e0) (controlled : Finset (Fin k))
    (before sigma second : PartialEdgeColoring E k) (alpha beta : Fin k)
    (vertex : V) (edge : E) (proper : IsProperEdgeColoring G sigma)
    (stable : StableColoring tree controlled before sigma)
    (swapped : before = TwoColorComponentSwap G second alpha beta (Sum.inl vertex))
    (controlledColor : alpha ∈ TreeMissingColors before tree ∪ controlled)
    (vertexInTree : vertex ∈ TreeSequenceVertexSet tree) (incident : Incident G vertex edge)
    (edgeColor : second edge = some beta) (distinct : alpha ≠ beta)
    (missing : alpha ∈ MissingColors G second vertex)
    (onlyRoot : ∀ v ∈ TreeSequenceVertexSet tree,
      Sum.inl v ∈ TwoColorComponent G sigma alpha beta (Sum.inl vertex) → v = vertex)
    (candidate : E) (candidateIncident : TreeIncidentEdge tree candidate)
    (candidateComponent : Sum.inr candidate ∈
      TwoColorComponent G sigma alpha beta (Sum.inl vertex)) : candidate = edge := by
  classical
  have edgeComponent : Sum.inr edge ∈
      TwoColorComponent G second alpha beta (Sum.inl vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simpa only [TwoColorIncidenceGraph] using And.intro incident (Or.inr edgeColor)
  have beforeColor : before edge = some alpha := by
    rw [swapped]
    simp [TwoColorComponentSwap, edgeComponent, edgeColor, distinct.symm]
  have sigmaColor : sigma edge = some alpha :=
    (stable.1 edge ⟨vertex, vertexInTree, incident⟩
      ⟨alpha, controlledColor, beforeColor⟩).trans beforeColor
  have betaPresent : beta ∈ PresentColors G second vertex := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨edge, incident, edgeColor⟩
  have betaMissing : beta ∈ MissingColors G sigma vertex := by
    rw [stable.2 vertex vertexInTree, swapped]
    have exchanged := (TwoColorComponentSwapExchangesRootColors
      (G := G) (phi := second) (v := vertex) distinct.symm missing betaPresent).1
    rw [← (P2880_T1_KempeOrientation G second beta alpha distinct.symm).2.2.1
      (Sum.inl vertex)]
    exact exchanged
  rcases candidateIncident with ⟨v, vInTree, vIncident⟩
  have candidateColor : sigma candidate = some alpha ∨ sigma candidate = some beta := by
    have support : Sum.inr candidate ∈
        (TwoColorIncidenceGraph G sigma alpha beta).support := by
      apply SimpleGraph.mem_support_of_reachable
        (G := TwoColorIncidenceGraph G sigma alpha beta)
        (u := Sum.inr candidate) (v := Sum.inl vertex) (by simp)
      exact SimpleGraph.ConnectedComponent.eq.mp candidateComponent
    obtain ⟨neighbor, adjacent⟩ :=
      (TwoColorIncidenceGraph G sigma alpha beta).mem_support.mp support
    cases neighbor with
    | inl v => exact adjacent.2
    | inr e => simp [TwoColorIncidenceGraph] at adjacent
  have vComponent : Sum.inl v ∈
      TwoColorComponent G sigma alpha beta (Sum.inl vertex) := by
    have adjacent : (TwoColorIncidenceGraph G sigma alpha beta).Adj
        (Sum.inl v) (Sum.inr candidate) := by
      simpa only [TwoColorIncidenceGraph] using And.intro vIncident candidateColor
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj adjacent).trans
      candidateComponent
  have same := onlyRoot v vInTree vComponent
  subst v
  have neighbors := TwoColorMissingVertexNeighborsSubsingleton G sigma proper alpha beta
    vertex (Or.inr betaMissing)
  apply Sum.inr.inj
  apply neighbors
  · exact ⟨vIncident, candidateColor⟩
  · exact ⟨incident, Or.inl sigmaColor⟩

end GoldbergSeymour

end
