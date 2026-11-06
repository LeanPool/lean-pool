/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

/-!
# Hierarchy First Missing Position Prefix Cutoff

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma HierarchyFirstMissingPositionPrefixCutoff {V E : Type*}
    [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (A T : TreeSequence G e0)
    (hAT : TreeSequenceInitialSegment A T) (eta : Fin k)
    (uLength : Nat) (hu : uLength <= A.length) :
    min (HierarchyFirstMissingPosition phi A eta).val uLength =
      min (HierarchyFirstMissingPosition phi T eta).val uLength := by
  classical
  let candidatesA : Finset (Fin (A.length + 1)) :=
    {i | eta ∈ MissingColors G phi (A.vertex i)}
  let candidatesT : Finset (Fin (T.length + 1)) :=
    {i | eta ∈ MissingColors G phi (T.vertex i)}
  unfold HierarchyFirstMissingPosition
  dsimp only
  change min (if h : candidatesA.Nonempty then candidatesA.min' h
      else Fin.last A.length).val uLength =
    min (if h : candidatesT.Nonempty then candidatesT.min' h
      else Fin.last T.length).val uLength
  by_cases hA : candidatesA.Nonempty
  · rw [dite_eq_left hA]
    let mA := candidatesA.min' hA
    let mAT : Fin (T.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hAT.1) mA
    have hmAmem : mA ∈ candidatesA := Finset.min'_mem candidatesA hA
    have hmATmem : mAT ∈ candidatesT := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hmA : eta ∈ MissingColors G phi (A.vertex mA) :=
        (Finset.mem_filter.mp hmAmem).2
      rw [hAT.2.1 mA]
      exact hmA
    have hT : candidatesT.Nonempty := ⟨mAT, hmATmem⟩
    rw [dite_eq_left hT]
    have hTle : (candidatesT.min' hT).val <= mA.val := by
      have hFin := Finset.min'_le candidatesT mAT hmATmem
      change (candidatesT.min' hT).val <= mAT.val at hFin
      simpa [mAT] using hFin
    let mTA : Fin (A.length + 1) :=
      ⟨(candidatesT.min' hT).val, by omega⟩
    have hmTmem : candidatesT.min' hT ∈ candidatesT :=
      Finset.min'_mem candidatesT hT
    have hmTAmem : mTA ∈ candidatesA := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hmT : eta ∈ MissingColors G phi
          (T.vertex (candidatesT.min' hT)) :=
        (Finset.mem_filter.mp hmTmem).2
      have hcast : Fin.castLE (Nat.succ_le_succ hAT.1) mTA =
          candidatesT.min' hT := Fin.ext rfl
      rw [← hcast, hAT.2.1 mTA] at hmT
      exact hmT
    have hAle : mA.val <= (candidatesT.min' hT).val := by
      have hFin := Finset.min'_le candidatesA mTA hmTAmem
      change (candidatesA.min' hA).val <= mTA.val at hFin
      simpa [mTA, mA] using hFin
    have heq : mA.val = (candidatesT.min' hT).val := by omega
    rw [heq]
  · rw [dite_eq_right hA]
    by_cases hT : candidatesT.Nonempty
    · rw [dite_eq_left hT]
      have hbound : A.length <= (candidatesT.min' hT).val := by
        by_contra hnot
        have hlt : (candidatesT.min' hT).val < A.length := by omega
        let mTA : Fin (A.length + 1) :=
          ⟨(candidatesT.min' hT).val, by omega⟩
        have hmTmem : candidatesT.min' hT ∈ candidatesT :=
          Finset.min'_mem candidatesT hT
        have hmTAmem : mTA ∈ candidatesA := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          have hmT : eta ∈ MissingColors G phi
              (T.vertex (candidatesT.min' hT)) :=
            (Finset.mem_filter.mp hmTmem).2
          have hcast : Fin.castLE (Nat.succ_le_succ hAT.1) mTA =
              candidatesT.min' hT := Fin.ext rfl
          rw [← hcast, hAT.2.1 mTA] at hmT
          exact hmT
        exact hA ⟨mTA, hmTAmem⟩
      simp only [Fin.val_last]
      omega
    · rw [dite_eq_right hT]
      simp only [Fin.val_last]
      have hlen := hAT.1
      omega


/-- Preserving missing colors on a prefix preserves first positions of its missing colors. -/
theorem TreeSequenceFirstMissingPositionCongrOfPrefix {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {initial tree : TreeSequence G e0}
    {first second : PartialEdgeColoring E k}
    (segment : TreeSequenceInitialSegment initial tree)
    (equal : ∀ vertex ∈ TreeSequenceVertexSet initial,
      MissingColors G first vertex = MissingColors G second vertex)
    {color : Fin k} (missing : color ∈ TreeMissingColors second initial) :
    HierarchyFirstMissingPosition first tree color =
      HierarchyFirstMissingPosition second tree color := by
  have missingFirst : color ∈ TreeMissingColors first initial := by
    rwa [TreeMissingColors.congr equal]
  have firstCut := HierarchyFirstMissingPositionPrefixCutoff first initial tree segment
    color initial.length le_rfl
  have secondCut := HierarchyFirstMissingPositionPrefixCutoff second initial tree segment
    color initial.length le_rfl
  have positionsEqual := TreeSequenceFirstMissingPositionCongr equal color
  have truncated := firstCut.symm.trans
    ((congrArg (fun position : Fin (initial.length + 1) => min position.val initial.length)
      positionsEqual).trans secondCut)
  have firstBound := TreeSequenceFirstMissingPositionLePrefix segment missingFirst
  have secondBound := TreeSequenceFirstMissingPositionLePrefix segment missing
  apply Fin.ext
  rw [min_eq_left firstBound, min_eq_left secondBound] at truncated
  exact truncated

end GoldbergSeymour

end
