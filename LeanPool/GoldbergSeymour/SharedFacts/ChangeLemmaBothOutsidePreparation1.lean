/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyCounterexample

/-!
# Shared facts for Preparation1

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ChangeLemmaBothOutsidePreparation1

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev initialSegmentTransitiveStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {S U W : TreeSequence G e0},
      TreeSequenceInitialSegment S U →
      TreeSequenceInitialSegment U W →
      TreeSequenceInitialSegment S W

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev comparableInitialSegmentsStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {S U W : TreeSequence G e0},
      TreeSequenceInitialSegment S W →
      TreeSequenceInitialSegment U W →
      S.length ≤ U.length →
      TreeSequenceInitialSegment S U

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev missingPositionOutsidePrefixStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
        (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
        (C : HierarchyCounterexample base) (_ _ : Fin k),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      TreeSequenceInitialSegment A T →
      ∀ (i : Fin (T.length + (1 : ℕ))),
      T.vertex i ∉ TreeSequenceVertexSet A →
      A.length < (↑i : ℕ)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem initialSegmentTransitive.{u_1, u_2} : initialSegmentTransitiveStatement.{u_1, u_2} := by
  classical
  intro V E G e0 S U W hSU hUW
  refine ⟨le_trans hSU.1 hUW.1, ?_, ?_⟩
  · intro i
    exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) i)).trans (hSU.2.1 i)
  · intro i
    exact (hUW.2.2 (Fin.castLE hSU.1 i)).trans (hSU.2.2 i)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem comparableInitialSegments.{u_1, u_2} : comparableInitialSegmentsStatement.{u_1, u_2} := by
  classical
  intro V E G e0 S U W hSW hUW hlen
  refine ⟨hlen, ?_, ?_⟩
  · intro i
    exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hSW.2.1 i)
  · intro i
    exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem missingPositionOutsidePrefix.{u_1, u_2} : missingPositionOutsidePrefixStatement.{u_1,
    u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A AToT i hi
  by_contra h
  have hle : i.val ≤ A.length := by omega
  apply hi
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨i.val, by omega⟩, (AToT.2.1 ⟨i.val, by omega⟩).symm⟩

end GoldbergSeymour.SharedFacts.ChangeLemmaBothOutsidePreparation1

end
