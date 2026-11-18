/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree

public import LeanPool.GoldbergSeymour.Step1ExitLegPresentation

/-!
# Step1Exit Leg Minimum

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A selected elementary exit-leg presentation with primary and secondary minimality conditions. -/
structure Step1ExitLegMinimum {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ) where
  /-- The presentation selected by the minimality conditions. -/
  selected : Step1ExitLegPresentation G k e0 n q
  elementary : ColoredVertexSetElementary G selected.phi (TreeSequenceVertexSet selected.T)
  primaryMinimal :
    ∀ (sigma : PartialEdgeColoring E k) (U : TreeSequence G e0) (corr :
        CorrespondingExtendedTashkinovTree G k e0 selected.ett sigma U), IsProperEdgeColoring G
        sigma → IsOneEdgeUncolored sigma e0 → StableColoring (selected.ett.series.data.tree
        (Fin.last selected.ett.rounds).castSucc) (TashkinovStoredColors selected.ett.series.data
        (Fin.last selected.ett.rounds)) selected.phi sigma → MaximumProperty corr.replacementETT →
    ∀ (baseU : HierarchyBase corr.replacementETT sigma) (L : TashkinovHierarchy
        corr.replacementETT baseU) (goodU : GoodHierarchy L), L.dividerCount <
        selected.hierarchy.dividerCount → 2 * corr.replacementETT.rounds + 11 ≤ (TreeMissingColors
        sigma (corr.replacementETT.series.data.tree (Fin.last
        corr.replacementETT.rounds).castSucc)).card → TreeColorSetMinusClosed G sigma U
        ((HierarchyTerminalStoredColors L).biUnion (goodU.gamma (Fin.last L.dividerCount))) →
    ∀ (c d : Fin k), c ≠ d → c ∈ TreeMissingColors sigma U → TreeColorSetClosed G sigma U { c } →
    ∀ (u1 v1 u2 v2 : V) (Q1 : (TwoColorIncidenceGraph G sigma c d).Walk (Sum.inl u1) (Sum.inl v1))
        (Q2 : (TwoColorIncidenceGraph G sigma c d).Walk (Sum.inl u2) (Sum.inl v2)), TreeExitPath U
        sigma c d u1 v1 Q1 → TreeExitPath U sigma c d u2 v2 Q2 → (
    ∀ x, x ∈ Q1.support → x ∉ Q2.support) → u1 ≠ u2 → False
  secondary :
    selected.b ∈ TreeMissingColors selected.phi selected.T ∨
      (selected.b ∉ TreeMissingColors selected.phi selected.T ∧
        ∃ (a3 b3 : V) (P3 :
          (TwoColorIncidenceGraph G selected.phi selected.a selected.b).Walk (Sum.inl a3)
            (Sum.inl b3))
          (f3 : E),
          TreeExitPath selected.T selected.phi selected.a selected.b a3 b3 P3 ∧
            (
  ∀ x,
  x ∈ selected.P1.support →
  x ∉ P3.support) ∧
              (
  ∀ x,
  x ∈ selected.P2.support →
  x ∉ P3.support) ∧
                selected.a1 ≠ a3 ∧
                  selected.a2 ≠ a3 ∧
                    selected.b1 ≠ b3 ∧
                      selected.b2 ≠ b3 ∧
                        TreeVertexOrder selected.T selected.b2 b3 ∧
                          f3 ∈
                              BoundaryColorEdges G selected.phi (TreeSequenceVertexSet selected.T)
                                selected.b ∧
                            Incident G b3 f3 ∧
                              Sum.inr f3 ∈ P3.support ∧
                                (
  ∀ (sigma : PartialEdgeColoring E k) (U : TreeSequence G e0)
   (corr :
     CorrespondingExtendedTashkinovTree G k e0 selected.ett sigma U),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring
      (selected.ett.series.data.tree
        (Fin.last selected.ett.rounds).castSucc)
      (TashkinovStoredColors selected.ett.series.data
        (Fin.last selected.ett.rounds))
      selected.phi sigma →
  MaximumProperty corr.replacementETT →
  ∀ (baseU : HierarchyBase corr.replacementETT sigma)
    (L : TashkinovHierarchy corr.replacementETT baseU)
    (goodU : GoodHierarchy L),
  L.dividerCount = selected.hierarchy.dividerCount →
  2 * corr.replacementETT.rounds + 11 ≤
      (TreeMissingColors sigma
          (corr.replacementETT.series.data.tree
            (Fin.last
                corr.replacementETT.rounds).castSucc)).card →
  TreeColorSetMinusClosed G sigma U
      ((HierarchyTerminalStoredColors L).biUnion
        (goodU.gamma (Fin.last L.dividerCount))) →
  ∀ (c d : Fin k),
  c ≠ d →
  c ∈ TreeMissingColors sigma U →
  TreeColorSetClosed G sigma U { c } →
  ∀ (u1 v1 u2 v2 : V)
    (Q1 :
      (TwoColorIncidenceGraph G sigma c
            d).Walk
        (Sum.inl u1) (Sum.inl v1))
    (Q2 :
      (TwoColorIncidenceGraph G sigma c
            d).Walk
        (Sum.inl u2) (Sum.inl v2)),
  TreeExitPath U sigma c d u1 v1 Q1 →
  TreeExitPath U sigma c d u2 v2 Q2 →
  (
  ∀ x,
  x ∈ Q1.support →
  x ∉ Q2.support) →
  u1 ≠ u2 →
  (d ∈ TreeMissingColors sigma U ∨
        (d ∉
            TreeMissingColors sigma
              U ∧
          ∃ (u3 v3 : V) (Q3 :
            (TwoColorIncidenceGraph
                  G sigma c d).Walk
              (Sum.inl u3)
              (Sum.inl v3)),
            TreeExitPath U sigma c d
                u3 v3 Q3 ∧
              (
  ∀ x,
  x ∈ Q1.support →
  x ∉
    Q3.support) ∧
        (
  ∀ x,
  x ∈ Q2.support →
  x ∉
    Q3.support) ∧
        u1 ≠ u3 ∧
          u2 ≠ u3 ∧
            Q1.length +
                  Q2.length +
                Q3.length <
              selected.P1.length +
                  selected.P2.length +
                P3.length)) →
  False))

end GoldbergSeymour

end
