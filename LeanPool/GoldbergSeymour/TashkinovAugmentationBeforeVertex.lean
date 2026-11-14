/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.StableColoringBeforeVertex
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Augmentation transport before a vertex

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Stability before a vertex transports augmentations contained in an earlier seed. -/
theorem TashkinovAugmentation.transportBeforeVertex {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tj seed : TreeSequence G e0) (phiJ rho3 : PartialEdgeColoring E k)
    (Dprev : Finset (Fin k)) (terminalSupport : V)
    (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj)
    (hd1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj Dprev phiJ rho3)
    (hsegmentVertexBefore : ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed →
      A.length < seed.length → ∀ {v : V}, v ∈ TreeSequenceVertexSet A →
        v ∈ TreeVerticesBefore Tj terminalSupport hterminalTj)
    {A B : TreeSequence G e0} (hstep : TashkinovAugmentation phiJ A B)
    (hBseed : TreeSequenceInitialSegment B seed) : TashkinovAugmentation rho3 A B := by
  classical
  rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
  have hAseed : TreeSequenceInitialSegment A seed := hAB.trans hBseed
  have hAlen : A.length < seed.length :=
    lt_of_lt_of_le (by omega) hBseed.1
  have hcMissingRho : c ∈ TreeMissingColors rho3 A := by
    unfold TreeMissingColors at hcMissing ⊢
    obtain ⟨w, hwA, hcw⟩ := Finset.mem_biUnion.mp hcMissing
    refine Finset.mem_biUnion.mpr ⟨w, hwA, ?_⟩
    rw [hd1.2 w (hsegmentVertexBefore hAseed hAlen hwA)]
    exact hcw
  let added : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
  obtain ⟨q, hq⟩ := B.attaches added
  let oldPos : Fin (B.length + 1) :=
    Fin.castLT q (Nat.lt_trans q.isLt (Nat.succ_lt_succ added.isLt))
  have holdVal : oldPos.val < A.length + 1 := by
    have hqBound := q.isLt
    dsimp [oldPos, added] at *
    omega
  let oldA : Fin (A.length + 1) := ⟨oldPos.val, holdVal⟩
  have holdEq : B.vertex oldPos = A.vertex oldA := by
    have hcast : Fin.castLE (Nat.succ_le_succ hAB.1) oldA = oldPos := by
      apply Fin.ext
      rfl
    rw [← hcast]
    exact hAB.2.1 oldA
  have holdA : A.vertex oldA ∈ TreeSequenceVertexSet A := by
    simp [TreeSequenceVertexSet]
  have holdBefore : B.vertex oldPos ∈
      TreeVerticesBefore Tj terminalSupport hterminalTj := by
    rw [holdEq]
    exact hsegmentVertexBefore hAseed hAlen holdA
  have holdIncident : Incident G (B.vertex oldPos) (B.edge added) := by
    unfold Incident
    rw [hq]
    simp [oldPos]
  have haddedFixed : rho3 (B.edge added) = phiJ (B.edge added) := by
    apply hd1.1 (B.edge added) ⟨B.vertex oldPos, holdBefore, holdIncident⟩
    refine ⟨c, ?_, ?_⟩
    · apply Finset.mem_union_left
      unfold TreeMissingColors at hcMissing
      obtain ⟨w, hwA, hcw⟩ := Finset.mem_biUnion.mp hcMissing
      exact Finset.mem_biUnion.mpr
        ⟨w, hsegmentVertexBefore hAseed hAlen hwA, hcw⟩
    · exact hcolor
  refine ⟨hlen, hAB, c, ?_, hcMissingRho⟩
  change rho3 (B.edge added) = some c
  exact haddedFixed.trans hcolor

end GoldbergSeymour

end
