/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTailMissingColorExclusion
public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

/-!
# Missing tail colors and stable component swaps

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A missing tail color on a tail edge is incident to the penultimate tree and stored. -/
theorem TashkinovHierarchy.tailMissingColorIncident {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input phi : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (initialSegment : TreeSequenceInitialSegment
      (HierarchyStarredStage H (Fin.last H.dividerCount)) T)
    (elementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (HierarchyTailPrefix H
        (T.length - (HierarchyStarredStage H (Fin.last H.dividerCount)).length - 1))))
    (j : ℕ) (positive : 1 ≤ j)
    (bound : j < T.length - (HierarchyStarredStage H (Fin.last H.dividerCount)).length)
    (color : Fin k) (missing : color ∈ MissingColors G phi
      ((HierarchyTailPrefix H j).vertex (Fin.last (HierarchyTailPrefix H j).length)))
    (t : Fin T.length)
    (lower : (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ t.val)
    (upper : t.val < (HierarchyStarredStage H (Fin.last H.dividerCount)).length + j)
    (colored : phi (T.edge t) = some color) :
    TreeIncidentEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) (T.edge t) ∧
      color ∈ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
  classical
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let U := HierarchyTailPrefix H j
  have lengthU : U.length = A.length + j := by
    change min (A.length + j) T.length = A.length + j
    change j < T.length - A.length at bound
    exact min_eq_left (by omega)
  have segment : TreeSequenceInitialSegment U T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  let u : Fin U.length := ⟨t.val, by rw [lengthU]; exact upper⟩
  have indexEqual : Fin.castLE segment.1 u = t := Fin.ext rfl
  have edgeColor : phi (U.edge u) = some color := by
    rw [← segment.2.2 u, indexEqual]
    exact colored
  have exclusion := HierarchyTailMissingColorExclusion G k e0 input T phi ett base
    H elementary j positive bound color missing u lower upper edgeColor
  obtain ⟨noDividers, core, position, _, _, _, _, _, _, stored⟩ := exclusion
  have atStart : t.val = A.length := position
  have initialCore : A = base.core := by
    simp [A, HierarchyStarredStage, noDividers, Fin.last]
  obtain ⟨vertex, attached⟩ := T.attaches t
  let old : Fin (T.length + 1) :=
    Fin.castLT vertex (Nat.lt_trans vertex.isLt (Nat.succ_lt_succ t.isLt))
  have member : T.vertex old ∈ TreeSequenceVertexSet A :=
    TreeSequenceInitialSegmentVertexMem initialSegment (by
      have := vertex.isLt
      change vertex.val ≤ A.length
      omega)
  refine ⟨?_, stored⟩
  rw [← core, ← initialCore]
  refine ⟨T.vertex old, member, ?_⟩
  rw [Incident, attached]
  exact Sym2.mem_mk_right _ _

/-- Stability controls a two-color swap on a tail avoiding one color and storing the other. -/
theorem StableColoring.componentSwapFixedOnTail {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {coreEdge treeEdge : E}
    {core : TreeSequence G coreEdge} {tree : TreeSequence G treeEdge}
    {stored : Finset (Fin k)} {phi : PartialEdgeColoring E k} {alpha beta : Fin k}
    {root : V ⊕ E}
    (stable : StableColoring core stored phi (TwoColorComponentSwap G phi alpha beta root))
    (start : ℕ)
    (firstUnused : ∀ t : Fin tree.length, start ≤ t.val → phi (tree.edge t) ≠ some alpha)
    (secondControlled : ∀ t : Fin tree.length, start ≤ t.val →
      phi (tree.edge t) = some beta →
        TreeIncidentEdge core (tree.edge t) ∧ beta ∈ stored) :
    ∀ t : Fin tree.length, start ≤ t.val →
      TwoColorComponentSwap G phi alpha beta root (tree.edge t) = phi (tree.edge t) := by
  intro t lower
  by_cases second : phi (tree.edge t) = some beta
  · obtain ⟨incident, member⟩ := secondControlled t lower second
    exact stable.1 (tree.edge t) incident
      ⟨beta, Finset.mem_union_right _ member, second⟩
  · unfold TwoColorComponentSwap
    simp only [ite_eq_right (firstUnused t lower), ite_eq_right second, ite_self]

/-- A stable component swap fixes the tail when its second color is missing at the prefix end. -/
theorem TashkinovHierarchy.stableComponentSwapOnTail {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input phi : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (initialSegment : TreeSequenceInitialSegment
      (HierarchyStarredStage H (Fin.last H.dividerCount)) T)
    (elementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (HierarchyTailPrefix H
        (T.length - (HierarchyStarredStage H (Fin.last H.dividerCount)).length - 1))))
    (tailPositive : 1 ≤ T.length -
      (HierarchyStarredStage H (Fin.last H.dividerCount)).length - 1)
    (lastEdge : Fin T.length)
    (lastPosition : lastEdge.val = (HierarchyTailPrefix H
      (T.length - (HierarchyStarredStage H (Fin.last H.dividerCount)).length - 1)).length)
    {alpha beta : Fin k} {root : V ⊕ E}
    (missing : beta ∈ MissingColors G phi ((HierarchyTailPrefix H
      (T.length - (HierarchyStarredStage H (Fin.last H.dividerCount)).length - 1)).vertex
      (Fin.last (HierarchyTailPrefix H
        (T.length - (HierarchyStarredStage H (Fin.last H.dividerCount)).length - 1)).length)))
    (lastNotSecond : phi (T.edge lastEdge) ≠ some beta)
    (stable : StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi
      (TwoColorComponentSwap G phi alpha beta root))
    (firstUnused : ∀ t : Fin T.length,
      (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ t.val →
        phi (T.edge t) ≠ some alpha) :
    ∀ t : Fin T.length, (HierarchyStarredStage H (Fin.last H.dividerCount)).length ≤ t.val →
      TwoColorComponentSwap G phi alpha beta root (T.edge t) = phi (T.edge t) := by
  classical
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let ell := T.length - A.length
  let X := HierarchyTailPrefix H (ell - 1)
  have lengthX : X.length = A.length + (ell - 1) := by
    change min (A.length + (ell - 1)) T.length = A.length + (ell - 1)
    change 1 ≤ T.length - A.length - 1 at tailPositive
    exact min_eq_left (by dsimp only [ell]; omega)
  have terminalLength : X.length + 1 = T.length := by
    rw [lengthX]
    change 1 ≤ T.length - A.length - 1 at tailPositive
    dsimp only [ell]
    omega
  apply stable.componentSwapFixedOnTail A.length firstUnused
  intro t lower second
  by_cases last : t = lastEdge
  · exact (lastNotSecond (last ▸ second)).elim
  · have beforeLast : t.val < X.length := by
      have bound := t.isLt
      have different : t.val ≠ X.length :=
        fun equal => last (Fin.ext (equal.trans lastPosition.symm))
      omega
    exact H.tailMissingColorIncident initialSegment elementary (ell - 1) tailPositive
      (by change ell - 1 < ell; change 1 ≤ ell - 1 at tailPositive; omega)
      beta missing t lower (by rw [← lengthX]; exact beforeLast) second

end GoldbergSeymour

end
