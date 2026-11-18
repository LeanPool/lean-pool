/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ETTFirstAppearanceIndex

/-!
# Restricting ladders and first appearance

General structural facts extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input lowerInput generating lowerGenerating : PartialEdgeColoring E k}
    {tree lowerTree : TreeSequence G e0}

/-- A restricted series and its displayed terminal tree determine every lower ladder stage. -/
theorem ExtendedTashkinovLadderStage.restrict
    (upper : ExtendedTashkinovTree G k e0 input tree generating)
    (lower : ExtendedTashkinovTree G k e0 lowerInput lowerTree lowerGenerating)
    (rounds : lower.rounds < upper.rounds)
    (display : lowerTree = upper.series.data.tree ⟨lower.rounds + 1, by omega⟩)
    (trees : ∀ index : Fin (lower.rounds + 2), lower.series.data.tree index =
      upper.series.data.tree (Fin.castLE (by omega) index))
    (index : Fin (lower.rounds + 1)) :
    ExtendedTashkinovLadderStage lower index =
      ExtendedTashkinovLadderStage upper (Fin.castLE (by omega) index) := by
  refine Fin.lastCases ?_ (fun earlier => ?_) index
  · rw [show ExtendedTashkinovLadderStage lower (Fin.last lower.rounds) = lowerTree from
      Fin.lastCases_last]
    have mapped : Fin.castLE (by omega) (Fin.last lower.rounds) =
        (⟨lower.rounds, rounds⟩ : Fin upper.rounds).castSucc := Fin.ext (by simp)
    rw [mapped]
    unfold ExtendedTashkinovLadderStage
    rw [Fin.lastCases_castSucc]
    exact display.trans (congrArg upper.series.data.tree (Fin.ext (by simp)))
  · have mapped : Fin.castLE (by omega) earlier.castSucc =
        (⟨earlier.val, by omega⟩ : Fin upper.rounds).castSucc := Fin.ext rfl
    rw [mapped]
    unfold ExtendedTashkinovLadderStage
    rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
    exact (trees earlier.succ.castSucc).trans
      (congrArg upper.series.data.tree (Fin.ext rfl))

/-- Restricting ladder stages preserves first appearance whenever it is in the lower range. -/
theorem ETTFirstAppearanceIndex.eq_of_ladder_restriction
    (upper : ExtendedTashkinovTree G k e0 input tree generating)
    (lower : ExtendedTashkinovTree G k e0 lowerInput lowerTree lowerGenerating)
    (rounds : lower.rounds ≤ upper.rounds)
    (stages : ∀ index : Fin (lower.rounds + 1), ExtendedTashkinovLadderStage lower index =
      ExtendedTashkinovLadderStage upper (Fin.castLE (by omega) index))
    (vertex : V) (lowerMember : vertex ∈ TreeSequenceVertexSet lowerTree)
    (upperMember : vertex ∈ TreeSequenceVertexSet tree)
    (bounded : ETTFirstAppearanceIndex upper vertex upperMember ≤ lower.rounds + 1) :
    ETTFirstAppearanceIndex lower vertex lowerMember =
      ETTFirstAppearanceIndex upper vertex upperMember := by
  classical
  unfold ETTFirstAppearanceIndex at bounded ⊢
  dsimp at bounded ⊢
  let lowerCandidates := Finset.univ.filter fun index : Fin (lower.rounds + 1) =>
    vertex ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage lower index)
  let upperCandidates := Finset.univ.filter fun index : Fin (upper.rounds + 1) =>
    vertex ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage upper index)
  have lowerNonempty : lowerCandidates.Nonempty := by
    refine ⟨Fin.last lower.rounds, ?_⟩
    simp only [lowerCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage lower (Fin.last lower.rounds) = lowerTree by
      unfold ExtendedTashkinovLadderStage
      exact Fin.lastCases_last]
    exact lowerMember
  have upperNonempty : upperCandidates.Nonempty := by
    refine ⟨Fin.last upper.rounds, ?_⟩
    simp only [upperCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage upper (Fin.last upper.rounds) = tree by
      unfold ExtendedTashkinovLadderStage
      exact Fin.lastCases_last]
    exact upperMember
  let firstLower := lowerCandidates.min' lowerNonempty
  let firstUpper := upperCandidates.min' upperNonempty
  have inLowerRange : firstUpper.val < lower.rounds + 1 := by
    have bound : firstUpper.val + 1 ≤ lower.rounds + 1 := bounded
    omega
  let restricted : Fin (lower.rounds + 1) := ⟨firstUpper.val, inLowerRange⟩
  have restrictedMember : restricted ∈ lowerCandidates := by
    simp only [lowerCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [stages restricted]
    exact (Finset.mem_filter.mp (Finset.min'_mem upperCandidates upperNonempty)).2
  have lowerMemberUpper : Fin.castLE (by omega) firstLower ∈ upperCandidates := by
    simp only [upperCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← stages firstLower]
    exact (Finset.mem_filter.mp (Finset.min'_mem lowerCandidates lowerNonempty)).2
  have one := Fin.le_iff_val_le_val.mp
    (Finset.min'_le lowerCandidates restricted restrictedMember)
  have two := Fin.le_iff_val_le_val.mp
    (Finset.min'_le upperCandidates (Fin.castLE (by omega) firstLower) lowerMemberUpper)
  change firstLower.val + 1 = firstUpper.val + 1
  exact congrArg (fun value : ℕ => value + 1) (le_antisymm one two)

/-- First appearance is preserved by a series restriction with the correct terminal display. -/
theorem ETTFirstAppearanceIndex.eq_of_series_restriction
    (upper : ExtendedTashkinovTree G k e0 input tree generating)
    (lower : ExtendedTashkinovTree G k e0 lowerInput lowerTree lowerGenerating)
    (rounds : lower.rounds < upper.rounds)
    (display : lowerTree = upper.series.data.tree ⟨lower.rounds + 1, by omega⟩)
    (trees : ∀ index : Fin (lower.rounds + 2), lower.series.data.tree index =
      upper.series.data.tree (Fin.castLE (by omega) index))
    (vertex : V) (lowerMember : vertex ∈ TreeSequenceVertexSet lowerTree)
    (upperMember : vertex ∈ TreeSequenceVertexSet tree)
    (bounded : ETTFirstAppearanceIndex upper vertex upperMember ≤ lower.rounds + 1) :
    ETTFirstAppearanceIndex lower vertex lowerMember =
      ETTFirstAppearanceIndex upper vertex upperMember :=
  ETTFirstAppearanceIndex.eq_of_ladder_restriction upper lower (Nat.le_of_lt rounds)
    (ExtendedTashkinovLadderStage.restrict upper lower rounds display trees)
    vertex lowerMember upperMember bounded

end GoldbergSeymour

end
