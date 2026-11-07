/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

public import LeanPool.GoldbergSeymour.TreeSequencePrefix

/-!
# Shared facts for ExtensionBaseBranchPreparation

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ExtensionBranchPreparation




/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev huUStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        (TjPrime : TreeSequence G e0) (u0 : V) (uPosition : Fin (TjPrime.length + (1 : ℕ))),
      TjPrime.vertex uPosition = u0 →
      ∀ (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
        (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
      let U : TreeSequence G e0 :=
        TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
      u0 ∈ TreeSequenceVertexSet U




/-- A common proof used by the branches of this transport or construction argument. -/
theorem huU.{u_1, u_2} : huUStatement.{u_1, u_2} := by
  classical
  intro V E G e0 TjPrime u0 uPosition huPosition huPositionPositive huPositionBound U
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  refine ⟨Fin.last U.length, ?_⟩
  change TjPrime.vertex (Fin.castLE (Nat.succ_le_succ huPositionBound)
    (Fin.last uPosition.val)) = u0
  have hindex : Fin.castLE (Nat.succ_le_succ huPositionBound)
      (Fin.last uPosition.val) = uPosition := by
    apply Fin.ext
    rfl
  rw [hindex]
  exact huPosition

end GoldbergSeymour.SharedFacts.ExtensionBranchPreparation

end
