/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree

/-!
# Shared facts for TerminalSeriesRebuildTransport

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.TerminalRebuildTransport

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev branchStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
          e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
          k) (Tstar : TreeSequence G e0),
      let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
      by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
      ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds → ett.series.data.kind q.succ = some
          TashkinovExtensionKind.PE → ((ett.series.data.kind (Fin.last ett.rounds) = some
          TashkinovExtensionKind.SE ∨ ett.series.data.kind (Fin.last ett.rounds) = some
          TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges (Fin.last ett.rounds) =
          ({ f } : Finset E) ∧ TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last
          ett.rounds).castSucc) f seed ∧ TashkinovAugmentationSequence sigma seed Tstar) → Nonempty
          (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem branch.{u_1, u_2} : branchStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q hqSucc hpeKind hsimple
  rcases hsimple.1 with hse | hre
  · have hbad := hpeKind.symm.trans (by simpa [hqSucc] using hse)
    cases hbad
  · have hbad := hpeKind.symm.trans (by simpa [hqSucc] using hre)
    cases hbad

end GoldbergSeymour.SharedFacts.TerminalRebuildTransport

end
