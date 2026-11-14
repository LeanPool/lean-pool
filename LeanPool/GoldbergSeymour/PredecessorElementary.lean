/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CertifiedETTPredecessor

public import LeanPool.GoldbergSeymour.TechnicalInductionContext
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase

/-!
# P2634_T1_Predecessor Elementary

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2634_T1_PredecessorElementary
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett) :
    let q : Fin ett.rounds := ⟨ett.rounds - 1, by
      have := ett.roundsPositive
      omega⟩
    ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc)
      (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
  dsimp only
  intro u hu v hv hne
  by_cases hone : ett.rounds = 1
  · have hbase : ColoredVertexSetElementary G (ett.series.data.coloring 0)
        (TreeSequenceVertexSet (ett.series.data.tree ⟨1, by omega⟩)) :=
      (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
    have hc : (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) = 0 := by
      apply Fin.ext
      simp [hone]
    have ht : (Fin.last ett.rounds).castSucc =
        (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simp [hone]
    rw [ht] at hu hv
    have hd := hbase hu hv hne
    simpa only [Fin.castSucc_mk, hc] using hd
  · have hmore : 1 < ett.rounds := by have := ett.roundsPositive; omega
    obtain ⟨pred, hr, hmax, _, _⟩ :=
      CertifiedETTPredecessor G k e0 input T phi ett hMP hmore
    have helem : ColoredVertexSetElementary G
        (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
        (TreeSequenceVertexSet (ett.series.data.tree ⟨ett.rounds, by omega⟩)) :=
      ctx.lowerOne pred (by omega) (by omega) hmax
    have ht : (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
        (Fin.last ett.rounds).castSucc := by
      apply Fin.ext
      rfl
    rw [← ht] at hu hv
    simpa only [Fin.castSucc_mk] using helem hu hv hne

end GoldbergSeymour

end
