/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment

/-!
# Transporting Augmentation Routes

Shared facts from Wesley Pegden's Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12, generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A step transport below the target tree transports any augmentation route to that target. -/
theorem TashkinovAugmentationSequence.transport {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {first second : PartialEdgeColoring E k} {source target : TreeSequence G e0}
    (transportStep : ∀ {A B : TreeSequence G e0}, TashkinovAugmentation first A B →
      TreeSequenceInitialSegment B target → TashkinovAugmentation second A B)
    (route : TashkinovAugmentationSequence first source target) :
    TashkinovAugmentationSequence second source target := by
  unfold TashkinovAugmentationSequence at route ⊢
  induction route using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head A B step remainder transported =>
      have segment := TashkinovAugmentationSequenceInitialSegment first B target remainder
      exact Relation.ReflTransGen.head (transportStep step segment) transported

/-- Stability on the target transports every augmentation route ending there. -/
theorem TashkinovAugmentationSequence.transport_of_stable {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {first second : PartialEdgeColoring E k} {source target : TreeSequence G e0}
    {colors : Finset (Fin k)} (stable : StableColoring target colors first second)
    (route : TashkinovAugmentationSequence first source target) :
    TashkinovAugmentationSequence second source target := by
  classical
  apply TashkinovAugmentationSequence.transport ?_ route
  intro A B step segment
  obtain ⟨lengthEqual, base, color, colored, missing⟩ := step
  obtain ⟨vertex, member, absent⟩ := Finset.mem_biUnion.mp missing
  have inTarget := (base.trans segment).vertexSet_subset member
  let added : Fin B.length := Fin.cast lengthEqual.symm (Fin.last A.length)
  have incident : TreeIncidentEdge target (B.edge added) := by
    obtain ⟨index, attaches⟩ := B.attaches added
    refine ⟨B.vertex added.succ, segment.vertexSet_subset ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨added.succ, Finset.mem_univ _, rfl⟩
    · rw [Incident, attaches]
      exact Sym2.mem_mk_left _ _
  have fixed := stable.1 _ incident
    ⟨color, Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨vertex, inTarget, absent⟩), colored⟩
  refine ⟨lengthEqual, base, color, fixed.trans colored, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨vertex, member, (stable.2 vertex inTarget).symm ▸ absent⟩

/-- A route that strictly increases length has a first augmentation and a remaining route. -/
theorem TashkinovAugmentationSequence.first_step {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {coloring : PartialEdgeColoring E k} {source target : TreeSequence G e0}
    (route : TashkinovAugmentationSequence coloring source target)
    (lengthLt : source.length < target.length) :
    ∃ next, TashkinovAugmentation coloring source next ∧
      TashkinovAugmentationSequence coloring next target := by
  unfold TashkinovAugmentationSequence at route ⊢
  induction route using Relation.ReflTransGen.head_induction_on with
  | refl => exact (Nat.lt_irrefl _ lengthLt).elim
  | @head A B step remainder _ => exact ⟨B, step, remainder⟩

/-- Fixed edge colors and preserved missing colors on strict prefixes transport a route. -/
theorem TashkinovAugmentationSequence.transport_of_fixed {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {first second : PartialEdgeColoring E k} {source target : TreeSequence G e0}
    (fixedEdges : ∀ index : Fin target.length,
      second (target.edge index) = first (target.edge index))
    (fixedMissing : ∀ {initial : TreeSequence G e0},
      TreeSequenceInitialSegment initial target → initial.length < target.length →
      ∀ vertex ∈ TreeSequenceVertexSet initial,
        MissingColors G second vertex = MissingColors G first vertex)
    (route : TashkinovAugmentationSequence first source target) :
    TashkinovAugmentationSequence second source target := by
  classical
  apply TashkinovAugmentationSequence.transport ?_ route
  intro A B step segment
  obtain ⟨lengthEqual, base, color, colored, missing⟩ := step
  have initial : TreeSequenceInitialSegment A target := base.trans segment
  have strict : A.length < target.length := by
    have := segment.1
    omega
  have missingSecond : color ∈ TreeMissingColors second A := by
    unfold TreeMissingColors at missing ⊢
    obtain ⟨vertex, inTree, absent⟩ := Finset.mem_biUnion.mp missing
    refine Finset.mem_biUnion.mpr ⟨vertex, inTree, ?_⟩
    rw [fixedMissing initial strict vertex inTree]
    exact absent
  let added : Fin B.length := Fin.cast lengthEqual.symm (Fin.last A.length)
  have agreement := fixedEdges (Fin.castLE segment.1 added)
  rw [segment.2.2 added] at agreement
  exact ⟨lengthEqual, base, color, agreement.trans colored, missingSecond⟩

end GoldbergSeymour

end
