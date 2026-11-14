/-
Copyright (c) 2026 Wesley Pegden and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.StableSwapComponentEdgeUnique
public import LeanPool.GoldbergSeymour.TashkinovSeries

/-!
# Unique component edges at a series slot

Shared from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 and generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A stable coloring has only the chosen component edge incident to the current series tree. -/
theorem TashkinovSeries.stableSwapComponentIncidentEdgeUnique {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
    (slot : Fin rounds) (sigma : PartialEdgeColoring E k)
    (proper : IsProperEdgeColoring G sigma)
    (stable : StableColoring (series.data.tree slot.succ.castSucc)
      (TashkinovStoredColors series.data slot.succ) (series.data.coloring slot.succ) sigma)
    (gamma : Fin k) (second : PartialEdgeColoring E k)
    (choice : MaximumDefectiveChoice G e0 (series.data.tree slot.succ.castSucc)
      (TashkinovStoredColors series.data slot.castSucc) (series.data.coloring slot.castSucc))
    (swapped : series.data.coloring slot.succ =
      TwoColorComponentSwap G second gamma choice.color (Sum.inl choice.vertex))
    (stored : series.data.stored slot.succ = insert choice.color ({gamma} : Finset (Fin k)))
    (onlyRoot : ∀ v ∈ TreeSequenceVertexSet (series.data.tree slot.succ.castSucc),
      Sum.inl v ∈ TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) ↔
        v = choice.vertex)
    (missing : gamma ∈ MissingColors G second choice.vertex)
    (edgeColor : second choice.edge = some choice.color) (distinct : gamma ≠ choice.color) :
    ∀ edge, TreeIncidentEdge (series.data.tree slot.succ.castSucc) edge →
      Sum.inr edge ∈ TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) →
        edge = choice.edge := by
  classical
  have controlled : gamma ∈
      TreeMissingColors (series.data.coloring slot.succ) (series.data.tree slot.succ.castSucc) ∪
        TashkinovStoredColors series.data slot.succ := by
    by_cases missing : gamma ∈
        TreeMissingColors (series.data.coloring slot.succ) (series.data.tree slot.succ.castSucc)
    · exact Finset.mem_union_left _ missing
    · apply Finset.mem_union_right _
      unfold TashkinovStoredColors
      rw [ite_eq_right (by simp)]
      simp only [Finset.mem_sdiff, Finset.mem_biUnion]
      refine ⟨⟨slot.succ, ?_, ?_⟩, missing⟩
      · simp
      · simp [stored]
  exact StableColoring.componentIncidentEdgeUniqueOfSwap _ _ _ _ _ gamma choice.color
    choice.vertex choice.edge proper stable swapped controlled choice.vertexDefective.1
    choice.edgeIncident edgeColor distinct missing (fun v hv hc => (onlyRoot v hv).mp hc)

end GoldbergSeymour

end
