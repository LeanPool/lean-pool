/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.StableColoringExitExtension

public import LeanPool.GoldbergSeymour.MaximumDefectiveChoiceExists

public import LeanPool.GoldbergSeymour.ParallelExtensionColorExists

/-!
# Algorithm Three One Choice Data Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem AlgorithmThreeOneChoiceDataExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : Nat) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input)
    (i : Fin (rounds + 1))
    (hdegree : MaximumDegree G + 1 ≤ k)
    (hproper : IsProperEdgeColoring G (series.data.coloring i))
    (hone : IsOneEdgeUncolored (series.data.coloring i) e0)
    (hclosed : ColoredVertexSetClosed G (series.data.coloring i)
      (TreeSequenceVertexSet (series.data.tree i.succ)))
    (hnotStrong : ¬ ColoredVertexSetStronglyClosed G
      (series.data.coloring i)
      (TreeSequenceVertexSet (series.data.tree i.succ))) :
    Nonempty (RevisitingExtensionCertificate series.data i) ∨
      (¬ Nonempty (RevisitingExtensionCertificate series.data i) ∧
        exists choice : MaximumDefectiveChoice G e0 (series.data.tree i.succ)
            (TashkinovStoredColors series.data i) (series.data.coloring i),
          forall pi : PartialEdgeColoring E k,
            IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
            StableColoring (series.data.tree i.succ)
              (insert choice.color (TashkinovStoredColors series.data i))
              choice.selected pi →
            Disjoint (MissingColors G pi choice.otherEndpoint)
              (TreeMissingColors pi (series.data.tree i.succ))) ∨
      (¬ Nonempty (RevisitingExtensionCertificate series.data i) ∧
        exists choice : MaximumDefectiveChoice G e0 (series.data.tree i.succ)
            (TashkinovStoredColors series.data i) (series.data.coloring i),
          (exists rho : PartialEdgeColoring E k,
            IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
            StableColoring (series.data.tree i.succ)
              (insert choice.color (TashkinovStoredColors series.data i))
              choice.selected rho ∧
            ¬ Disjoint (MissingColors G rho choice.otherEndpoint)
              (TreeMissingColors rho (series.data.tree i.succ))) ∧
          exists gamma : Fin k,
            ParallelExtensionColor series.data i choice.selected
              choice.vertex gamma ∧
            exists sigma : PartialEdgeColoring E k,
              IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
              StableColoring (series.data.tree i.succ)
                (insert choice.color (TashkinovStoredColors series.data i))
                choice.selected sigma ∧
              TreeExit (series.data.tree i.succ) sigma gamma choice.color
                choice.vertex) := by
  classical
  by_cases revisiting : Nonempty (RevisitingExtensionCertificate series.data i)
  · exact Or.inl revisiting
  · right
    obtain ⟨choice⟩ := MaximumDefectiveChoiceExists G e0
      (series.data.tree i.succ) (TashkinovStoredColors series.data i)
      (series.data.coloring i) hproper hone hclosed hnotStrong
    by_cases seriesCase : forall pi : PartialEdgeColoring E k,
        IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (series.data.tree i.succ)
          (insert choice.color (TashkinovStoredColors series.data i))
          choice.selected pi →
        Disjoint (MissingColors G pi choice.otherEndpoint)
          (TreeMissingColors pi (series.data.tree i.succ))
    · exact Or.inl ⟨revisiting, choice, seriesCase⟩
    · right
      have failure : exists rho : PartialEdgeColoring E k,
          IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
          StableColoring (series.data.tree i.succ)
            (insert choice.color (TashkinovStoredColors series.data i))
            choice.selected rho ∧
          ¬ Disjoint (MissingColors G rho choice.otherEndpoint)
            (TreeMissingColors rho (series.data.tree i.succ)) := by
        push Not at seriesCase
        exact seriesCase
      obtain ⟨gamma, gammaRule⟩ := ParallelExtensionColorExists G k rounds
        e0 input series i choice hdegree
      have edgeBoundary : choice.edge ∈ BoundaryEdges G
          (TreeSequenceVertexSet (series.data.tree i.succ)) := by
        rcases choice.edgeDefective with ⟨color, _, hmem⟩
        exact (Finset.mem_filter.mp hmem).1
      have boundaryIncident : forall f : E,
          f ∈ BoundaryEdges G (TreeSequenceVertexSet (series.data.tree i.succ)) →
          TreeIncidentEdge (series.data.tree i.succ) f := by
        intro f hf
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
          true_and] at hf
        obtain ⟨v, hv, u, hu, hends⟩ := hf
        exact ⟨v, hv, by change v ∈ G.ends f; rw [hends]; simp⟩
      have selectedClosed : ColoredVertexSetClosed G choice.selected
          (TreeSequenceVertexSet (series.data.tree i.succ)) := by
        intro f color v hf hv hfcolor hmissing
        have oldMissing : color ∈ MissingColors G (series.data.coloring i) v := by
          rw [← choice.selectedStable.2 v hv]
          exact hmissing
        have oldTreeMissing : color ∈
            TreeMissingColors (series.data.coloring i) (series.data.tree i.succ) := by
          simp only [TreeMissingColors, Finset.mem_biUnion]
          exact ⟨v, hv, oldMissing⟩
        have fixed := (sc1 G e0 (series.data.tree i.succ)
          (TashkinovStoredColors series.data i) (series.data.coloring i)
          choice.selected hproper hone choice.selectedProper
          choice.selectedOneUncolored).mp choice.selectedStable f
          (boundaryIncident f hf)
          (Or.inr ⟨color, Finset.mem_union_left _ oldTreeMissing, hfcolor⟩)
        have oldColor : series.data.coloring i f = some color := by
          rw [← fixed]
          exact hfcolor
        exact (hclosed hf hv oldColor) oldMissing
      have commonMissing : exists rho : PartialEdgeColoring E k,
          IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
          StableColoring (series.data.tree i.succ)
            (insert choice.color (TashkinovStoredColors series.data i))
            choice.selected rho ∧
          exists beta, beta ∈ MissingColors G rho choice.otherEndpoint ∧
            beta ∈ TreeMissingColors rho (series.data.tree i.succ) := by
        obtain ⟨rho, rhoProper, rhoOne, rhoStable, rhoNonDisjoint⟩ := failure
        rw [Finset.not_disjoint_iff] at rhoNonDisjoint
        obtain ⟨beta, betaOutside, betaTree⟩ := rhoNonDisjoint
        exact ⟨rho, rhoProper, rhoOne, rhoStable, beta, betaOutside, betaTree⟩
      have orientedEnds : G.ends choice.edge =
          s(choice.otherEndpoint, choice.vertex) := by
        exact choice.edgeEnds.trans Sym2.eq_swap
      obtain ⟨sigma, sigmaProper, sigmaOne, sigmaStable, sigmaExit⟩ :=
        LEM_extable G k e0 choice.edge (series.data.tree i.succ)
          (TashkinovStoredColors series.data i) choice.selected
          choice.otherEndpoint choice.vertex choice.color hdegree
          choice.selectedProper choice.selectedOneUncolored selectedClosed
          edgeBoundary orientedEnds choice.otherOutside choice.vertexDefective.1
          choice.edgeColor commonMissing gamma gammaRule.1
      exact ⟨revisiting, choice, failure, gamma, gammaRule, sigma,
        sigmaProper, sigmaOne, sigmaStable, sigmaExit⟩

end GoldbergSeymour

end
