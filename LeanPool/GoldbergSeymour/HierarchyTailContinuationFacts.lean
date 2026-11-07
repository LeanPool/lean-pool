/-
Copyright (c) 2026 Wesley Pegden and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation
public import LeanPool.GoldbergSeymour.GoodHierarchyReservedDisjoint
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence

/-!
# Missing colors and final edges of hierarchy tails

Shared and generalized from the credited Trellis situation-two proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. These interfaces retain only the
initial-segment, coloring and reserved-color facts used by their proofs.
-/

@[expose] public section

namespace GoldbergSeymour

/-- In an elementary tree, a color missing beyond an initial segment is absent from that
segment. -/
theorem TreeSequenceInitialSegment.missingColorNotInPrefix {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {initial middle tree : TreeSequence G e0}
    (nested : TreeSequenceInitialSegment initial middle)
    (extension : TreeSequenceInitialSegment initial tree)
    (elementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet middle))
    {position : Fin (tree.length + 1)}
    (member : tree.vertex position ∈ TreeSequenceVertexSet middle)
    (later : initial.length < position.val) {color : Fin k}
    (missing : color ∈ MissingColors G phi (tree.vertex position)) :
    color ∉ TreeMissingColors phi initial := by
  classical
  intro inInitial
  obtain ⟨vertex, inInitial, missingVertex⟩ := Finset.mem_biUnion.mp inInitial
  have different : vertex ≠ tree.vertex position := by
    intro same
    exact extension.vertex_not_mem_after later (same ▸ inInitial)
  exact Finset.disjoint_left.mp (elementary (nested.vertexSet_subset inInitial) member different)
    missingVertex missing

/-- The newly attached vertex is incident to its attachment edge. -/
theorem TreeSequence.edgeIncidentSuccessor {V E : Type*} {G : LooplessMultigraph V E} {e0 : E}
    (tree : TreeSequence G e0) (index : Fin tree.length) :
    Incident G (tree.vertex index.succ) (tree.edge index) := by
  obtain ⟨previous, endpoints⟩ := tree.attaches index
  change _ ∈ G.ends (tree.edge index)
  rw [endpoints]
  exact Sym2.mem_mk_left _ _

/-- A missing color carried by the final attachment gives a one-step augmentation. -/
theorem TashkinovAugmentationSequence.singleLastEdge {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {initial tree : TreeSequence G e0} (length : initial.length + 1 = tree.length)
    (segment : TreeSequenceInitialSegment initial tree) (index : Fin tree.length)
    (last : index.val + 1 = tree.length) {color : Fin k}
    (colored : phi (tree.edge index) = some color)
    (missing : color ∈ TreeMissingColors phi initial) :
    TashkinovAugmentationSequence phi initial tree := by
  apply Relation.ReflTransGen.single
  refine ⟨length.symm, segment, color, ?_, missing⟩
  have same : Fin.cast length (Fin.last initial.length) = index := Fin.ext (by
    simp only [Fin.val_cast, Fin.val_last]
    omega)
  simpa only [same] using colored

/-- Recoloring one edge makes its former color missing at every incident vertex. -/
theorem IsProperEdgeColoring.missingAfterSingleEdgeChange {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {phi sigma : PartialEdgeColoring E k}
    (proper : IsProperEdgeColoring G phi) {edge : E} {vertex : V} {color : Fin k}
    (incident : Incident G vertex edge) (colored : phi edge = some color)
    (changed : sigma edge ≠ some color)
    (fixed : ∀ other, other ≠ edge → sigma other = phi other) :
    color ∈ MissingColors G sigma vertex := by
  classical
  simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
  intro member
  obtain ⟨other, otherIncident, otherColored⟩ := (Finset.mem_filter.mp member).2
  by_cases same : other = edge
  · subst other
    exact changed otherColored
  · exact proper same ⟨vertex, otherIncident, incident⟩
      ((fixed other same).symm.trans otherColored) colored

/-- Transporting the reserved colors preserves their first-missing cutoff at a fixed prefix. -/
theorem HierarchyReplacementPresentation.gammaCutoff {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input phi : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} {C : HierarchyCounterexample base}
    {ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C}
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    {short middle : TreeSequence G e0} (shortInside : TreeSequenceInitialSegment short T)
    (nested : TreeSequenceInitialSegment short middle) {beta theta : Fin k}
    (thetaOutside : theta ∉ TreeMissingColors phi
      (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)))
    (cutoff : ∀ color ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
      beta ∈ C.good.gamma (Fin.last C.hierarchy.dividerCount) color →
        color = theta ∨ color ∈ TreeMissingColors phi short)
    (same : HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
        HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount) ∧
      ∀ color ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
        C.good.gamma (Fin.last C.hierarchy.dividerCount) color =
          P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) color)
    (preserved : ∀ color ∈ TreeMissingColors phi middle,
      HierarchyFirstMissingPosition P.coloring T color = HierarchyFirstMissingPosition phi T color)
    (thetaBound : (HierarchyFirstMissingPosition P.coloring T theta).val ≤ middle.length)
    (color : Fin k)
    (stored : color ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount))
    (pair : beta ∈ P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
      color ∨ theta ∈ P.counterexample.good.gamma
        (Fin.last P.counterexample.hierarchy.dividerCount) color) :
    (HierarchyFirstMissingPosition P.coloring T color).val ≤ middle.length := by
  classical
  have storedOld := Finset.subset_of_eq same.1.symm stored
  have pairOld : beta ∈ C.good.gamma (Fin.last C.hierarchy.dividerCount) color ∨
      theta ∈ C.good.gamma (Fin.last C.hierarchy.dividerCount) color :=
    (same.2 color storedOld).symm ▸ pair
  rcases pairOld with betaReserved | thetaReserved
  · rcases cutoff color storedOld betaReserved with equal | missing
    · exact equal.symm ▸ thetaBound
    · rw [preserved color (nested.treeMissingColors_subset missing)]
      exact (TreeSequenceFirstMissingPositionLePrefix shortInside missing).trans nested.1
  · exact (thetaOutside ((GoodHierarchyReservedDisjoint C.good
      (Fin.last C.hierarchy.dividerCount)).1 color storedOld thetaReserved)).elim

end GoldbergSeymour

end
