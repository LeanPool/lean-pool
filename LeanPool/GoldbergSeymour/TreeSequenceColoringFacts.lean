/-
Copyright (c) 2026 Wesley Pegden and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary

/-!
# Coloring Facts for Initial Segments

Shared facts extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 and generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Every vertex position inside an initial segment belongs to that segment's vertex set. -/
theorem TreeSequenceInitialSegmentVertexMem {V E : Type*} {G : LooplessMultigraph V E}
    {e0 : E} {initialSegment tree : TreeSequence G e0}
    (segment : TreeSequenceInitialSegment initialSegment tree)
    {index : Fin (tree.length + 1)} (bound : index.val ≤ initialSegment.length) :
    tree.vertex index ∈ TreeSequenceVertexSet initialSegment := by
  classical
  let position : Fin (initialSegment.length + 1) := ⟨index.val, by omega⟩
  have equal : Fin.castLE (Nat.succ_le_succ segment.1) position = index := Fin.ext rfl
  rw [← equal, segment.2.1 position]
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨position, rfl⟩

/-- A missing-color witness bounds the first missing position. -/
theorem TreeSequenceFirstMissingPositionLe {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {tree : TreeSequence G e0} {color : Fin k} {index : Fin (tree.length + 1)}
    (missing : color ∈ MissingColors G phi (tree.vertex index)) :
    (HierarchyFirstMissingPosition phi tree color).val ≤ index.val := by
  classical
  let candidates := Finset.univ.filter fun i : Fin (tree.length + 1) =>
    color ∈ MissingColors G phi (tree.vertex i)
  have member : index ∈ candidates := by simp [candidates, missing]
  have nonempty : candidates.Nonempty := ⟨index, member⟩
  simpa only [HierarchyFirstMissingPosition, candidates, dite_eq_left nonempty] using
    (show (candidates.min' nonempty).val ≤ index.val from
      Finset.min'_le candidates index member)

/-- A color missing somewhere in an initial segment first goes missing within that segment. -/
theorem TreeSequenceFirstMissingPositionLePrefix {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {initialSegment tree : TreeSequence G e0}
    (segment : TreeSequenceInitialSegment initialSegment tree)
    {color : Fin k} (missing : color ∈ TreeMissingColors phi initialSegment) :
    (HierarchyFirstMissingPosition phi tree color).val ≤ initialSegment.length := by
  classical
  obtain ⟨vertex, member, missing⟩ := Finset.mem_biUnion.mp missing
  obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp member
  have witness : color ∈ MissingColors G phi
      (tree.vertex (Fin.castLE (Nat.succ_le_succ segment.1) index)) := by
    rw [segment.2.1 index]
    exact missing
  have bound := TreeSequenceFirstMissingPositionLe witness
  have := index.isLt
  simp only [Fin.val_castLE] at bound
  omega

/-- In an elementary initial segment a missing color has its unique vertex at the first missing
position. -/
theorem TreeSequenceFirstMissingPositionEq {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {initialSegment tree : TreeSequence G e0}
    (segment : TreeSequenceInitialSegment initialSegment tree)
    (elementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet initialSegment))
    {index : Fin (tree.length + 1)} (bound : index.val ≤ initialSegment.length) {color : Fin k}
    (missing : color ∈ MissingColors G phi (tree.vertex index)) :
    HierarchyFirstMissingPosition phi tree color = index := by
  classical
  let candidates := Finset.univ.filter fun i : Fin (tree.length + 1) =>
    color ∈ MissingColors G phi (tree.vertex i)
  have member : index ∈ candidates := by simp [candidates, missing]
  have nonempty : candidates.Nonempty := ⟨index, member⟩
  have minimum := Finset.min'_le candidates index member
  have missingMinimum : color ∈ MissingColors G phi (tree.vertex (candidates.min' nonempty)) :=
    (Finset.mem_filter.mp (Finset.min'_mem candidates nonempty)).2
  have memberMinimum := TreeSequenceInitialSegmentVertexMem segment
    (Nat.le_trans minimum bound)
  have memberIndex := TreeSequenceInitialSegmentVertexMem segment bound
  have equal : candidates.min' nonempty = index := by
    by_contra different
    have verticesDifferent := fun h => different (tree.vertex_injective h)
    exact Finset.disjoint_left.mp
      (elementary memberMinimum memberIndex verticesDifferent) missingMinimum missing
  simpa only [HierarchyFirstMissingPosition, candidates, dite_eq_left nonempty] using equal

/-- A witness in an elementary initial segment determines the first missing position in the tree. -/
theorem TreeSequenceFirstMissingPositionEqCast {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {initialSegment tree : TreeSequence G e0}
    (segment : TreeSequenceInitialSegment initialSegment tree)
    (elementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet initialSegment))
    {position : Fin (initialSegment.length + 1)} {color : Fin k}
    (missing : color ∈ MissingColors G phi (initialSegment.vertex position)) :
    (HierarchyFirstMissingPosition phi tree color).val = position.val := by
  have witness : color ∈ MissingColors G phi
      (tree.vertex (Fin.castLE (Nat.succ_le_succ segment.1) position)) := by
    rw [segment.2.1 position]
    exact missing
  exact congrArg Fin.val (TreeSequenceFirstMissingPositionEq segment elementary
    (show position.val ≤ initialSegment.length from Nat.le_of_lt_succ position.isLt) witness)

/-- A color missing somewhere on the tree is missing at its first missing position. -/
theorem TreeSequenceFirstMissingPositionMemOfMissing {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {tree : TreeSequence G e0} {color : Fin k} (member : color ∈ TreeMissingColors phi tree) :
    color ∈ MissingColors G phi (tree.vertex (HierarchyFirstMissingPosition phi tree color)) := by
  classical
  obtain ⟨vertex, inTree, missing⟩ := Finset.mem_biUnion.mp member
  obtain ⟨index, equality⟩ : ∃ index, tree.vertex index = vertex := by
    simpa [TreeSequenceVertexSet] using inTree
  let candidates := Finset.univ.filter fun index : Fin (tree.length + 1) =>
    color ∈ MissingColors G phi (tree.vertex index)
  have nonempty : candidates.Nonempty := by
    refine ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [equality] using missing
  unfold HierarchyFirstMissingPosition
  rw [dite_eq_left nonempty]
  exact (Finset.mem_filter.mp (Finset.min'_mem candidates nonempty)).2

/-- A first missing position strictly before the fallback endpoint is an actual missing witness. -/
theorem TreeSequenceFirstMissingPositionMem {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {tree : TreeSequence G e0} {color : Fin k}
    (beforeLast : (HierarchyFirstMissingPosition phi tree color).val < tree.length) :
    color ∈ MissingColors G phi (tree.vertex (HierarchyFirstMissingPosition phi tree color)) := by
  classical
  let candidates := Finset.univ.filter fun index : Fin (tree.length + 1) =>
    color ∈ MissingColors G phi (tree.vertex index)
  by_cases nonempty : candidates.Nonempty
  · unfold HierarchyFirstMissingPosition
    rw [dite_eq_left nonempty]
    exact (Finset.mem_filter.mp (Finset.min'_mem candidates nonempty)).2
  · have last : (HierarchyFirstMissingPosition phi tree color).val = tree.length := by
      unfold HierarchyFirstMissingPosition
      rw [dite_eq_right nonempty]
      rfl
    omega

/-- Enlarging a tree by an initial-segment extension can only add missing colors. -/
theorem TreeSequenceInitialSegment.treeMissingColors_subset {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {coloring : PartialEdgeColoring E k}
    {initial tree : TreeSequence G e0} (segment : TreeSequenceInitialSegment initial tree) :
    TreeMissingColors coloring initial ⊆ TreeMissingColors coloring tree := by
  classical
  intro color membership
  obtain ⟨vertex, inInitial, missing⟩ := Finset.mem_biUnion.mp membership
  exact Finset.mem_biUnion.mpr ⟨vertex, segment.vertexSet_subset inInitial, missing⟩


/-- An actual missing-color witness gives both the first witness and its least-position bound. -/
theorem TreeSequenceFirstMissingPositionWitness {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {tree : TreeSequence G e0} {color : Fin k} {index : Fin (tree.length + 1)}
    (missing : color ∈ MissingColors G phi (tree.vertex index)) :
    color ∈ MissingColors G phi (tree.vertex (HierarchyFirstMissingPosition phi tree color)) ∧
      (HierarchyFirstMissingPosition phi tree color).val ≤ index.val := by
  classical
  exact ⟨TreeSequenceFirstMissingPositionMemOfMissing
    (Finset.mem_biUnion.mpr ⟨tree.vertex index, by simp [TreeSequenceVertexSet], missing⟩),
    TreeSequenceFirstMissingPositionLe missing⟩

/-- A color missing on a prefix has an actual first witness no later than that prefix. -/
theorem TreeSequenceFirstMissingPositionPrefixWitness {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {initial tree : TreeSequence G e0} (segment : TreeSequenceInitialSegment initial tree)
    {color : Fin k} (missing : color ∈ TreeMissingColors phi initial) :
    color ∈ MissingColors G phi (tree.vertex (HierarchyFirstMissingPosition phi tree color)) ∧
      (HierarchyFirstMissingPosition phi tree color).val ≤ initial.length := by
  exact ⟨TreeSequenceFirstMissingPositionMemOfMissing (segment.treeMissingColors_subset missing),
    TreeSequenceFirstMissingPositionLePrefix segment missing⟩

/-- A color missing on a prefix has its first missing vertex in that prefix. -/
theorem TreeSequenceFirstMissingVertexMemOfPrefix {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {initial tree : TreeSequence G e0} (segment : TreeSequenceInitialSegment initial tree)
    {color : Fin k} (missing : color ∈ TreeMissingColors phi initial) :
    tree.vertex (HierarchyFirstMissingPosition phi tree color) ∈ TreeSequenceVertexSet initial := by
  exact TreeSequenceInitialSegmentVertexMem segment
    (TreeSequenceFirstMissingPositionLePrefix segment missing)

/-- Absence before a bounded threshold gives a lower bound on the totalized first position. -/
theorem TreeSequenceFirstMissingPositionLowerBound {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {tree : TreeSequence G e0} {color : Fin k} {threshold : ℕ}
    (bound : threshold ≤ tree.length)
    (absent : ∀ index : Fin (tree.length + 1), index.val < threshold →
      color ∉ MissingColors G phi (tree.vertex index)) :
    threshold ≤ (HierarchyFirstMissingPosition phi tree color).val := by
  by_contra notBound
  have before : (HierarchyFirstMissingPosition phi tree color).val < threshold :=
    Nat.lt_of_not_ge notBound
  exact absent _ before (TreeSequenceFirstMissingPositionMem (before.trans_le bound))

/-- A color absent from a strict prefix first goes missing strictly after that prefix. -/
theorem TreeSequenceFirstMissingPositionAfterPrefix {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {initial tree : TreeSequence G e0} (segment : TreeSequenceInitialSegment initial tree)
    (strict : initial.length < tree.length) {color : Fin k}
    (absent : color ∉ TreeMissingColors phi initial) :
    initial.length < (HierarchyFirstMissingPosition phi tree color).val := by
  classical
  by_contra notAfter
  have bound : (HierarchyFirstMissingPosition phi tree color).val ≤ initial.length :=
    le_of_not_gt notAfter
  exact absent (Finset.mem_biUnion.mpr ⟨_, TreeSequenceInitialSegmentVertexMem segment bound,
    TreeSequenceFirstMissingPositionMem (bound.trans_lt strict)⟩)

/-- A color absent from a prefix containing every vertex before the last has final first
position. -/
theorem TreeSequenceFirstMissingPositionEqLastOfNotMemPrefix {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {initial tree : TreeSequence G e0} (segment : TreeSequenceInitialSegment initial tree)
    (last : tree.length ≤ initial.length + 1) {color : Fin k}
    (absent : color ∉ TreeMissingColors phi initial) :
    HierarchyFirstMissingPosition phi tree color = Fin.last tree.length := by
  classical
  apply Fin.ext
  simp only [Fin.val_last]
  refine Nat.le_antisymm (Nat.le_of_lt_succ (HierarchyFirstMissingPosition phi tree color).isLt) ?_
  apply TreeSequenceFirstMissingPositionLowerBound le_rfl
  intro index before missing
  exact absent (Finset.mem_biUnion.mpr ⟨_, TreeSequenceInitialSegmentVertexMem segment
    (Nat.le_of_lt_succ (before.trans_le last)), missing⟩)

/-- Color-wise missing-membership agreement preserves the totalized first position. -/
theorem TreeSequenceFirstMissingPositionMembershipCongr {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {tree : TreeSequence G e0}
    {first second : PartialEdgeColoring E k} {color : Fin k}
    (agreement : ∀ index : Fin (tree.length + 1),
      color ∈ MissingColors G first (tree.vertex index) ↔
        color ∈ MissingColors G second (tree.vertex index)) :
    HierarchyFirstMissingPosition first tree color =
      HierarchyFirstMissingPosition second tree color := by
  classical
  let firstCandidates := Finset.univ.filter
    fun index : Fin (tree.length + 1) => color ∈ MissingColors G first (tree.vertex index)
  let secondCandidates := Finset.univ.filter
    fun index : Fin (tree.length + 1) => color ∈ MissingColors G second (tree.vertex index)
  have equal : firstCandidates = secondCandidates := by
    ext index
    simp only [firstCandidates, secondCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact agreement index
  unfold HierarchyFirstMissingPosition
  change (if h : firstCandidates.Nonempty then firstCandidates.min' h else Fin.last tree.length) =
    (if h : secondCandidates.Nonempty then secondCandidates.min' h else Fin.last tree.length)
  rw [equal]

/-- Pointwise equality of missing colors on a tree preserves its missing-color union. -/
theorem TreeMissingColors.congr {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {tree : TreeSequence G e0}
    {first second : PartialEdgeColoring E k}
    (equal : ∀ vertex ∈ TreeSequenceVertexSet tree,
      MissingColors G first vertex = MissingColors G second vertex) :
    TreeMissingColors first tree = TreeMissingColors second tree := by
  classical
  unfold TreeMissingColors
  apply Finset.biUnion_congr rfl
  exact equal

/-- Pointwise equality of missing colors preserves the first missing position. -/
theorem TreeSequenceFirstMissingPositionCongr {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {tree : TreeSequence G e0}
    {first second : PartialEdgeColoring E k}
    (equal : ∀ vertex ∈ TreeSequenceVertexSet tree,
      MissingColors G first vertex = MissingColors G second vertex) (color : Fin k) :
    HierarchyFirstMissingPosition first tree color =
      HierarchyFirstMissingPosition second tree color := by
  apply TreeSequenceFirstMissingPositionMembershipCongr
  intro index
  rw [equal (tree.vertex index) (by simp [TreeSequenceVertexSet])]

end GoldbergSeymour

end
