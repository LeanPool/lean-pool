/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree

/-!
# Shared facts for RevisitingTerminalPreparation

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.RevisitingTerminalPreparation

open scoped Sym2

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev tnClosureStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
        ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
          (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
          (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
          (ett : ExtendedTashkinovTree G k e0 input T generating) (Tstar : TreeSequence G e0),
          TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar →
            ∀ (closureTree : TreeSequence G e0),
              TreeSequenceInitialSegment Tstar closureTree →
                TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                  closureTree

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hiStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
          e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
      let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
      by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
      ⟩ : Fin ett.rounds);
      ∀ (i : Fin ett.rounds), Fin.last ett.rounds = i.succ → i = q

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hneStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
        ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
          (e0 : E) (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
          (ch : MaximumDefectiveChoice G e0 X C phi) (g : Fin k) (second : PartialEdgeColoring E k),
          g ∈ MissingColors G second ch.vertex → second ch.edge = some ch.color → g ≠ ch.color

/-- A common proof used by the branches of this transport or construction argument. -/
theorem tnClosure.{u_1, u_2} : tnClosureStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett Tstar hTnTstar closureTree hTstarClosure
  rcases hTnTstar with ⟨hlenAB, hvertexAB, hedgeAB⟩
  rcases hTstarClosure with ⟨hlenBC, hvertexBC, hedgeBC⟩
  refine ⟨Nat.le_trans hlenAB hlenBC, ?_, ?_⟩
  · intro j
    calc
      closureTree.vertex (Fin.castLE (Nat.succ_le_succ (Nat.le_trans hlenAB hlenBC)) j) =
          closureTree.vertex
            (Fin.castLE (Nat.succ_le_succ hlenBC) (Fin.castLE (Nat.succ_le_succ hlenAB) j)) :=
        by congr 1
      _ = Tstar.vertex (Fin.castLE (Nat.succ_le_succ hlenAB) j) := hvertexBC _
      _ = (ett.series.data.tree (Fin.last ett.rounds).castSucc).vertex j := hvertexAB j
  · intro j
    calc
      closureTree.edge (Fin.castLE (Nat.le_trans hlenAB hlenBC) j) =
          closureTree.edge (Fin.castLE hlenBC (Fin.castLE hlenAB j)) :=
        by congr 1
      _ = Tstar.edge (Fin.castLE hlenAB j) := hedgeBC _
      _ = (ett.series.data.tree (Fin.last ett.rounds).castSucc).edge j := hedgeAB j

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hi.{u_1, u_2} : hiStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q i htarget
  apply Fin.ext
  have hv : ett.rounds = i.val + 1 := by simpa using congrArg Fin.val htarget
  change i.val = ett.rounds - 1
  omega

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hne.{u_1, u_2} : hneStatement.{u_1, u_2} := by
  classical
  intro V E _ _ G k e0 X C phi ch g second hgSecond hedgeSecond heq
  have hpresent : g ∈ PresentColors G second ch.vertex := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ch.edge, ch.edgeIncident, by simpa [heq] using hedgeSecond⟩
  have hnotPresent : g ∉ PresentColors G second ch.vertex := by simpa [MissingColors] using hgSecond
  exact hnotPresent hpresent

end GoldbergSeymour.SharedFacts.RevisitingTerminalPreparation

end
