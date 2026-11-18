/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.CertifiedETTPredecessor
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase

/-!
# Shared facts for StableChangeCasesOneTwoFullTail

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.FullTailTransport

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev preStepElementaryStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
      HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C →
      let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      let i : Fin ett.rounds :=
        (⟨ett.rounds - (1 : ℕ), by have this : (0 : ℕ) < ett.rounds := C.positive; omega⟩ :
          Fin ett.rounds);
      ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet Tn)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem preStepElementary.{u_1, u_2} : preStepElementaryStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx n Tn
  dsimp only
  by_cases hn : ett.rounds = 1
  · have hcolor : (⟨ett.rounds - 1, by have := C.positive; omega⟩ : Fin ett.rounds).castSucc = 0 :=
      Fin.ext (by simp [hn])
    have htree : n.castSucc = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) :=
      Fin.ext (by simp [n, hn])
    dsimp only [Tn]
    rw [hcolor, htree]
    exact (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
  · have hmore : 1 < ett.rounds := by have := C.positive; omega
    obtain ⟨predecessor, hr, hmaximum, _, _⟩ :=
      CertifiedETTPredecessor G k e0 input T phi ett C.maximum hmore
    have htree : n.castSucc = (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) :=
      Fin.ext rfl
    dsimp only [Tn]
    rw [htree]
    exact (ctx.lowerRung predecessor (by omega) (by omega) hmaximum).1

end GoldbergSeymour.SharedFacts.FullTailTransport

end
