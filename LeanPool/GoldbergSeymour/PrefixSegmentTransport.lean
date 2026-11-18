/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff

public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import Mathlib.Data.Fintype.EquivFin

/-!
# P2813_T1_Prefix Segment Transport

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2813_T1_PrefixSegmentTransport {V E : Type*}
    [Finite V] [Fintype E] {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi sigma : PartialEdgeColoring E k) (U A T : TreeSequence G e0)
    (hUA : TreeSequenceInitialSegment U A)
    (hAT : TreeSequenceInitialSegment A T)
    (hfixed : ∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t))
    (hmissing : ∀ v ∈ TreeSequenceVertexSet A,
      MissingColors G sigma v = MissingColors G phi v)
    (eta : Fin k) (lower : Nat) :
    (Finset.univ.filter fun c : Fin k =>
      ∃ r : Fin U.length, lower ≤ r.val ∧
        r.val < min (HierarchyFirstMissingPosition sigma A eta).val U.length ∧
        sigma (U.edge r) = some c) =
    (Finset.univ.filter fun c : Fin k =>
      ∃ r : Fin U.length, lower ≤ r.val ∧
        r.val < min (HierarchyFirstMissingPosition phi T eta).val U.length ∧
        phi (U.edge r) = some c) := by
  classical
  let _ := Fintype.ofFinite V
  have firstEq : HierarchyFirstMissingPosition sigma A eta =
      HierarchyFirstMissingPosition phi A eta := by
    exact TreeSequenceFirstMissingPositionCongr hmissing eta
  have cutoff := HierarchyFirstMissingPositionPrefixCutoff phi A T hAT eta U.length hUA.1
  rw [firstEq, cutoff]
  apply Finset.filter_congr
  intro c _
  constructor
  · rintro ⟨r, hr, hp, hc⟩
    refine ⟨r, hr, hp, ?_⟩
    have he : sigma (U.edge r) = phi (U.edge r) := by
      rw [← hUA.2.2 r]
      exact hfixed _
    exact he.symm.trans hc
  · rintro ⟨r, hr, hp, hc⟩
    refine ⟨r, hr, hp, ?_⟩
    have he : sigma (U.edge r) = phi (U.edge r) := by
      rw [← hUA.2.2 r]
      exact hfixed _
    exact he.trans hc

end GoldbergSeymour

end
