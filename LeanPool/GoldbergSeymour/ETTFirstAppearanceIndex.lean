/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtendedTashkinovLadderStage

/-!
# ETTFirst Appearance Index

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The first ladder stage containing the vertex, numbered starting at one. -/
noncomputable def ETTFirstAppearanceIndex {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) (v : V)
    (hv : v ∈ TreeSequenceVertexSet T) : ℕ := by
  classical
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hfinal :
      ExtendedTashkinovLadderStage ett (Fin.last ett.rounds) = T := by
    unfold ExtendedTashkinovLadderStage
    exact Fin.lastCases_last
  have hlast : Fin.last ett.rounds ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfinal]
    exact hv
  exact (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val + 1

/-- A vertex already present in a nonterminal ladder stage appears no later than that stage. -/
theorem ETTFirstAppearanceIndex.le_of_series_mem {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input generating : PartialEdgeColoring E k}
    {tree : TreeSequence G e0} (ett : ExtendedTashkinovTree G k e0 input tree generating)
    (vertex : V) (member : vertex ∈ TreeSequenceVertexSet tree) (index : Fin ett.rounds)
    (stageMember : vertex ∈ TreeSequenceVertexSet (ett.series.data.tree index.succ.castSucc)) :
    ETTFirstAppearanceIndex ett vertex member ≤ index.val + 1 := by
  classical
  unfold ETTFirstAppearanceIndex
  dsimp
  have candidate : index.castSucc ∈ Finset.univ.filter
      (fun position : Fin (ett.rounds + 1) =>
        vertex ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett position)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage ett index.castSucc =
        ett.series.data.tree index.succ.castSucc by
      unfold ExtendedTashkinovLadderStage
      exact @Fin.lastCases_castSucc ett.rounds
        (fun _ : Fin (ett.rounds + 1) => TreeSequence G e0) tree
        (fun index => ett.series.data.tree index.succ.castSucc) index]
    exact stageMember
  exact Nat.succ_le_succ (Fin.le_iff_val_le_val.mp (Finset.min'_le _ _ candidate))

end GoldbergSeymour

end
